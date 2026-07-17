//! Primitive and builtin evaluation: the string/float/array/buffer builtins, the
//! numeric operator dispatch, and float formatting. Pure functions over runtime
//! values, shared by the machine's step loop.

use std::cmp::Ordering;
use std::io::Write as _;
use std::path::Path;
use std::rc::Rc;
use std::sync::OnceLock;
use std::time::{Instant, SystemTime, UNIX_EPOCH};
use std::{env, fs};

use num_bigint::{BigInt, Sign};

use crate::core::builtins::{Builtin, FloatOp};
use crate::core::{CoreOp, NegLane};
use crate::store::bridge;
use crate::types::{CONS, NIL};
use Builtin as B;
use FloatOp as F;

use super::{owned_math, Rv};

// The C runtime's `prism_show_float_prec` formats `%.*f` into a 64-byte buffer,
// so it can emit at most 63 characters. The interpreter mirrors that cap to stay
// byte-identical with the native backend.
const RT_FLOAT_PREC_MAX_CHARS: usize = 63;
const BUFFER_INDEX_ERROR: &str = "buffer index out of bounds";
const TBUF_NEGATIVE_LENGTH_ERROR: &str = "tbuf_new: negative length";
/// Mirrors `prism_big_of_str` in the C runtime: ASCII-trim, optional sign, then
/// a strict all-digit decimal parse. Anything else is None.
pub(super) fn big_of_str(s: &str) -> Option<BigInt> {
    let t = s.trim_matches(|c: char| c.is_ascii_whitespace());
    let digits = t.strip_prefix(['+', '-']).unwrap_or(t);
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    t.parse().ok()
}

/// Builds the `Result(Unit, String)` ADT value the file builtins return,
/// matching the `Ok`/`Err` cells the native runtime constructs.
fn file_result(r: std::io::Result<()>) -> Rv {
    match r {
        Ok(()) => Rv::Data("Ok".into(), vec![Rv::Unit].into()),
        Err(e) => Rv::Data("Err".into(), vec![Rv::Str(e.to_string())].into()),
    }
}
// Truncating/widening conversions are the language semantics of these builtins.
#[allow(clippy::cast_possible_truncation, clippy::cast_precision_loss)]
// Genuine unary negation per lane. Int reuses the exact `0 - x` subtract path
// (immediate/bignum promotion included) so the result is identical to the old
// lowering; I64 is the wrapping fixed-width subtract from zero; Float is a real
// sign-bit flip (`-f`, not `-0.0 - f`) so it preserves signed zero and matches
// the native `fneg` bit for bit.
pub(super) fn neg_rv(lane: NegLane, v: &Rv) -> Result<Rv, String> {
    match lane {
        NegLane::Int => prim(CoreOp::Sub, &Rv::Int(0), v),
        NegLane::I64 => fixed2(&Rv::I64(0), v, u64::wrapping_sub),
        NegLane::Float => match v {
            Rv::Float(f) => Ok(Rv::Float(-f)),
            _ => Err("negation on non-float value".into()),
        },
    }
}
// The int/float conversion casts are the conversion semantics, not accidents:
// `Int -> Float` rounds to nearest (the IEEE double nearest to the integer),
// and the float-to-int forms truncate/floor/ceil saturate into the i64 lane,
// mirroring the native `llvm.fptosi.sat` lowering and guarded by the parity
// corpus and the conformance gate.
#[allow(clippy::cast_precision_loss, clippy::cast_possible_truncation)]
pub(super) fn float_builtin(op: FloatOp, rv: Rv) -> Result<Rv, String> {
    let Rv::Float(f) = rv else {
        // The one non-float input is the int->float conversion.
        return match (op, rv) {
            (F::ToFloat, Rv::Int(n)) => Ok(Rv::Float(n as f64)),
            (o, _) => Err(format!("float builtin {}: wrong argument type", o.name())),
        };
    };
    Ok(match op {
        // int<->float conversions. `f as i64` truncates toward zero and saturates
        // (NaN -> 0), the pinned rounding; native codegen matches it with
        // `llvm.fptosi.sat`, so the two backends agree on out-of-range inputs.
        F::Truncate => Rv::Int(f as i64),
        F::FloorToInt => Rv::Int(owned_floor(f) as i64),
        F::CeilToInt => Rv::Int(owned_ceil(f) as i64),
        // Exact float->float: correctly rounded / exact on every IEEE-754
        // platform, so Rust std matches the hardware intrinsic codegen emits.
        F::AbsFloat => Rv::Float(f.abs()),
        F::Sqrt => Rv::Float(f.sqrt()),
        F::Floor => Rv::Float(owned_floor(f)),
        F::Ceil => Rv::Float(owned_ceil(f)),
        F::Round => Rv::Float(f.round()),
        F::Trunc => Rv::Float(f.trunc()),
        // Transcendentals: the owned vendored libm, identical to native.
        F::Sin => Rv::Float(owned_math::sin(f)),
        F::Cos => Rv::Float(owned_math::cos(f)),
        F::Tan => Rv::Float(owned_math::tan(f)),
        F::Asin => Rv::Float(owned_math::asin(f)),
        F::Acos => Rv::Float(owned_math::acos(f)),
        F::Atan => Rv::Float(owned_math::atan(f)),
        F::Sinh => Rv::Float(owned_math::sinh(f)),
        F::Cosh => Rv::Float(owned_math::cosh(f)),
        F::Tanh => Rv::Float(owned_math::tanh(f)),
        F::Exp => Rv::Float(owned_math::exp(f)),
        F::Exp2 => Rv::Float(owned_math::exp2(f)),
        F::Expm1 => Rv::Float(owned_math::expm1(f)),
        F::Ln => Rv::Float(owned_math::log(f)),
        F::Log2 => Rv::Float(owned_math::log2(f)),
        F::Log10 => Rv::Float(owned_math::log10(f)),
        F::Log1p => Rv::Float(owned_math::log1p(f)),
        F::Cbrt => Rv::Float(owned_math::cbrt(f)),
        F::ToFloat => return Err(format!("float builtin {}: wrong argument type", op.name())),
    })
}

// `floor`/`ceil` are exact and share their result with the codegen intrinsic;
// factored out so the float->float and float->int forms cannot drift.
const fn owned_floor(f: f64) -> f64 {
    f.floor()
}
const fn owned_ceil(f: f64) -> f64 {
    f.ceil()
}

// The typed-buffer family (f64 `tbuf_*` and i64 `ibuf_*`): one `Rv::TBuf` of
// raw 8-byte words underneath, mirroring the element-agnostic C runtime. Only
// the element boxing differs between the families (float bits in and out versus
// exact-bit-pattern `cast_unsigned`/`cast_signed` for i64); construction,
// length, set, and blit share one implementation on the raw words.
fn tbuf_builtin(b: Builtin, vals: &[Rv]) -> Result<Rv, String> {
    match (b, vals) {
        (B::TbufNew, [Rv::Int(n), Rv::Float(init)]) => tbuf_make(*n, init.to_bits()),
        (B::IbufNew, [Rv::Int(n), Rv::I64(init)]) => tbuf_make(*n, init.cast_unsigned()),
        (B::TbufLen | B::IbufLen, [Rv::TBuf(v)]) => {
            Ok(Rv::Int(i64::try_from(v.len()).unwrap_or(0)))
        }
        (B::TbufGet, [Rv::TBuf(v), Rv::Int(i)]) => {
            tbuf_word(v, *i).map(|bits| Rv::Float(f64::from_bits(bits)))
        }
        (B::IbufGet, [Rv::TBuf(v), Rv::Int(i)]) => {
            tbuf_word(v, *i).map(|bits| Rv::I64(bits.cast_signed()))
        }
        (B::TbufSet, [Rv::TBuf(v), Rv::Int(i), Rv::Float(x)]) => tbuf_store(v, *i, x.to_bits()),
        (B::IbufSet, [Rv::TBuf(v), Rv::Int(i), Rv::I64(x)]) => tbuf_store(v, *i, x.cast_unsigned()),
        (
            B::TbufBlit | B::IbufBlit,
            [Rv::TBuf(d), Rv::Int(ds), Rv::TBuf(s), Rv::Int(ss), Rv::Int(n)],
        ) => tbuf_copy(d, *ds, s, *ss, *n),
        _ => Err("typed-buffer op: wrong args".into()),
    }
}

fn tbuf_make(n: i64, init: u64) -> Result<Rv, String> {
    let k = usize::try_from(n).map_err(|_| TBUF_NEGATIVE_LENGTH_ERROR.to_string())?;
    Ok(Rv::TBuf(Rc::new(vec![init; k])))
}

fn tbuf_word(v: &[u64], i: i64) -> Result<u64, String> {
    usize::try_from(i)
        .ok()
        .and_then(|k| v.get(k).copied())
        .ok_or_else(|| BUFFER_INDEX_ERROR.to_string())
}

fn tbuf_store(v: &[u64], i: i64, bits: u64) -> Result<Rv, String> {
    let k = usize::try_from(i).map_err(|_| BUFFER_INDEX_ERROR.to_string())?;
    if k >= v.len() {
        return Err(BUFFER_INDEX_ERROR.to_string());
    }
    let mut next = v.to_vec();
    next[k] = bits;
    Ok(Rv::TBuf(Rc::new(next)))
}

fn tbuf_copy(d: &[u64], ds: i64, s: &[u64], ss: i64, n: i64) -> Result<Rv, String> {
    let oob = || BUFFER_INDEX_ERROR.to_string();
    let dstart = usize::try_from(ds).map_err(|_| oob())?;
    let sstart = usize::try_from(ss).map_err(|_| oob())?;
    let count = usize::try_from(n).map_err(|_| oob())?;
    if dstart.checked_add(count).is_none_or(|e| e > d.len())
        || sstart.checked_add(count).is_none_or(|e| e > s.len())
    {
        return Err(oob());
    }
    let mut next = d.to_vec();
    next[dstart..dstart + count].copy_from_slice(&s[sstart..sstart + count]);
    Ok(Rv::TBuf(Rc::new(next)))
}

pub(super) fn str_builtin(b: Builtin, vals: &[Rv], args: &[String]) -> Result<Rv, String> {
    match (b, vals) {
        (B::Concat, [Rv::Str(a), Rv::Str(b)]) => Ok(Rv::Str(format!("{a}{b}"))),
        (B::StrLen, [Rv::Str(s)]) => Ok(Rv::Int(i64::try_from(s.chars().count()).unwrap_or(0))),
        (B::StrEq, [Rv::Str(a), Rv::Str(b)]) => Ok(Rv::Bool(a == b)),
        (B::StrCmp, [Rv::Str(a), Rv::Str(b)]) => Ok(Rv::Int(match a.cmp(b) {
            Ordering::Less => -1,
            Ordering::Equal => 0,
            Ordering::Greater => 1,
        })),
        (B::ShowInt, [Rv::Int(n)]) | (B::ShowI64, [Rv::I64(n)]) => Ok(Rv::Str(n.to_string())),
        (B::ShowInt, [Rv::Big(n)]) => Ok(Rv::Str(n.to_string())),
        (B::ShowBool, [Rv::Bool(b)]) => Ok(Rv::Str(b.to_string())),
        (B::ShowFloat, [Rv::Float(f)]) => Ok(Rv::Str(fmt_g(*f))),
        (B::ShowFloatPrec, [Rv::Float(f), Rv::Int(d)]) => {
            // Cap the precision at the runtime's buffer width before formatting.
            // Digits past `RT_FLOAT_PREC_MAX_CHARS` are truncated away regardless,
            // and materializing a user-controlled precision first (e.g. 1e9) would
            // allocate gigabytes in the interpreter while the native path bounds the
            // work at the buffer; capping first keeps the output byte identical.
            let prec = usize::try_from(*d)
                .unwrap_or(0)
                .min(RT_FLOAT_PREC_MAX_CHARS);
            let mut s = format!("{f:.prec$}");
            s.truncate(RT_FLOAT_PREC_MAX_CHARS);
            Ok(Rv::Str(s))
        }
        (B::ProbeEnabled, [Rv::Str(name)]) => Ok(Rv::Bool(probe_enabled(name))),
        (B::PowFloat, [Rv::Float(a), Rv::Float(b)]) => Ok(Rv::Float(owned_math::pow(*a, *b))),
        (B::Atan2, [Rv::Float(a), Rv::Float(b)]) => Ok(Rv::Float(owned_math::atan2(*a, *b))),
        (B::Hypot, [Rv::Float(a), Rv::Float(b)]) => Ok(Rv::Float(owned_math::hypot(*a, *b))),
        (B::Fmod, [Rv::Float(a), Rv::Float(b)]) => Ok(Rv::Float(owned_math::fmod(*a, *b))),
        // Strict full-consume parse: trailing garbage and hex yield 0.0, matching
        // `prism_parse_float` in the runtime (see its note on the strtod divergence).
        (B::ParseFloat, [Rv::Str(s)]) => Ok(Rv::Float(s.trim().parse::<f64>().unwrap_or(0.0))),
        (B::Substring, [Rv::Str(s), Rv::Int(start), Rv::Int(len)]) => {
            let st = usize::try_from(*start).unwrap_or(0);
            let take = usize::try_from(*len).unwrap_or(0);
            Ok(Rv::Str(s.chars().skip(st).take(take).collect()))
        }
        (B::CharAt, [Rv::Str(s), Rv::Int(i)]) => {
            Ok(Rv::Int(usize::try_from(*i).map_or(-1, |idx| {
                s.chars().nth(idx).map_or(-1, |c| i64::from(c as u32))
            })))
        }
        // Hash a string's raw bytes with blake3, returned as lowercase hex. The
        // native runtime's `prism_blake3` must produce the identical string.
        (B::Blake3, [Rv::Str(s)]) => Ok(Rv::Str(blake3::hash(s.as_bytes()).to_hex().to_string())),
        (B::ShowChar, [Rv::Int(cp)]) => Ok(Rv::Str(
            u32::try_from(*cp)
                .ok()
                .and_then(char::from_u32)
                .map(|c| c.to_string())
                .unwrap_or_default(),
        )),
        (B::ParseInt, [Rv::Str(s)]) => Ok(big_of_str(s).map_or_else(
            || Rv::Data("None".into(), Vec::new().into()),
            |n| Rv::Data("Some".into(), vec![norm(n)].into()),
        )),
        // Elaborator-only: decimal text of a valid big literal to its `Integer`.
        (B::BigLit, [Rv::Str(s)]) => Ok(norm(s.parse().unwrap_or(BigInt::ZERO))),
        (B::Getenv, [Rv::Str(s)]) => Ok(Rv::Str(env::var(s).unwrap_or_default())),
        (B::ReadFile, [Rv::Str(p)]) => match fs::read_to_string(p) {
            Ok(s) => Ok(Rv::Str(s)),
            Err(e) => Err(format!("read_file: {e}: {p}")),
        },
        // Raw bytes, no UTF-8 constraint: a byte buffer holds an arbitrary file
        // faithfully where `Rv::Str` (a Rust `String`) could not.
        (B::ReadBytesFile, [Rv::Str(p)]) => match fs::read(p) {
            Ok(v) => Ok(Rv::Buf(Rc::new(v))),
            Err(e) => Err(format!("read_bytes: {e}: {p}")),
        },
        (B::WriteBytesFile, [Rv::Str(p), Rv::Buf(v)]) => Ok(file_result(fs::write(p, &v[..]))),
        (B::WriteFile, [Rv::Str(p), Rv::Str(c)]) => Ok(file_result(fs::write(p, c))),
        (B::FileExists, [Rv::Str(p)]) => Ok(Rv::Bool(std::path::Path::new(p).exists())),
        (B::AppendFile, [Rv::Str(p), Rv::Str(c)]) => {
            let r = fs::OpenOptions::new()
                .append(true)
                .create(true)
                .open(p)
                .and_then(|mut f| f.write_all(c.as_bytes()));
            Ok(file_result(r))
        }
        (B::RemoveFile, [Rv::Str(p)]) => {
            let _ = fs::remove_file(p);
            Ok(Rv::Unit)
        }
        // The content-addressed store bridge. Reads are best-effort cache reads:
        // a missing, dangling, or corrupt blob returns empty/false so the caller
        // cold-starts, exactly as a missing snapshot file does. A write failure is
        // swallowed too, since the store is only a cache.
        (B::StoreGet, [Rv::Str(root), Rv::Str(key)]) => Ok(Rv::Str(
            bridge::get(Path::new(root), key)
                .ok()
                .flatten()
                .unwrap_or_default(),
        )),
        (B::StorePut, [Rv::Str(root), Rv::Str(key), Rv::Str(content)]) => {
            let _ = bridge::put(Path::new(root), key, content);
            Ok(Rv::Unit)
        }
        (B::StoreHas, [Rv::Str(root), Rv::Str(key)]) => {
            Ok(Rv::Bool(bridge::has(Path::new(root), key)))
        }
        // `exit` is intercepted in `step` (it sets the machine's exit status
        // and unwinds), so it never reaches the value-returning builtin path.
        (B::Exit, _) => Err("exit: unexpected argument".into()),
        // Run a shell command, returning its exit code (-1 on spawn failure or
        // signal death), matching the C runtime's `WEXITSTATUS(system(..))`.
        (B::System, [Rv::Str(cmd)]) => Ok(Rv::Int(i64::from(
            std::process::Command::new("sh")
                .arg("-c")
                .arg(cmd)
                .status()
                .ok()
                .and_then(|s| s.code())
                .unwrap_or(-1),
        ))),
        (B::Eprint, [Rv::Str(s)]) => {
            eprint!("{s}");
            let _ = std::io::stderr().flush();
            Ok(Rv::Unit)
        }
        (B::ArgsCount, []) => Ok(Rv::Int(i64::try_from(args.len()).unwrap_or(0))),
        // Clock reads, in nanoseconds, matching the C runtime. Both are recorded
        // capability observations (see `capability_obs`), so the live value here
        // is only read on the first (recording) run; replay serves the trace. The
        // monotonic origin is this process's first read, so only differences are
        // meaningful, exactly as the native `CLOCK_MONOTONIC` origin is arbitrary.
        (B::WallNow, []) => {
            let ns = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map_or(0, |d| d.as_nanos());
            Ok(Rv::Int(i64::try_from(ns).unwrap_or(i64::MAX)))
        }
        (B::MonoNow, []) => {
            static MONO_BASE: OnceLock<Instant> = OnceLock::new();
            let ns = MONO_BASE.get_or_init(Instant::now).elapsed().as_nanos();
            Ok(Rv::Int(i64::try_from(ns).unwrap_or(i64::MAX)))
        }
        (B::Arg, [Rv::Int(i)]) => Ok(Rv::Str(
            usize::try_from(*i)
                .ok()
                .and_then(|k| args.get(k).cloned())
                .unwrap_or_default(),
        )),
        (B::I64Add | B::U64Add, [a, b]) => fixed2(a, b, u64::wrapping_add),
        (B::I64Sub | B::U64Sub, [a, b]) => fixed2(a, b, u64::wrapping_sub),
        (B::I64Mul | B::U64Mul, [a, b]) => fixed2(a, b, u64::wrapping_mul),
        (B::I64Div | B::I64Rem, [_, Rv::I64(0)]) | (B::U64Div | B::U64Rem, [_, Rv::U64(0)]) => {
            Err("division by zero".into())
        }
        (B::I64Div, [Rv::I64(x), Rv::I64(y)]) => Ok(Rv::I64(x.wrapping_div(*y))),
        (B::I64Rem, [Rv::I64(x), Rv::I64(y)]) => Ok(Rv::I64(x.wrapping_rem(*y))),
        (B::U64Div, [Rv::U64(x), Rv::U64(y)]) => Ok(Rv::U64(x / y)),
        (B::U64Rem, [Rv::U64(x), Rv::U64(y)]) => Ok(Rv::U64(x % y)),
        (B::I64Cmp, [Rv::I64(x), Rv::I64(y)]) => Ok(ord(x.cmp(y))),
        (B::U64Cmp, [Rv::U64(x), Rv::U64(y)]) => Ok(ord(x.cmp(y))),
        (B::ArrayNew, [Rv::Int(n), init]) => {
            let k = usize::try_from(*n).map_err(|_| "array_new: negative length".to_string())?;
            Ok(Rv::Array(vec![init.clone(); k].into()))
        }
        (B::ArrayEmpty, []) => Ok(Rv::Array(Vec::new().into())),
        (B::ArrayPush, [Rv::Array(v), x]) => {
            let mut next = v.to_vec();
            next.push(x.clone());
            Ok(Rv::Array(next.into()))
        }
        (B::ArrayPop, [Rv::Array(v)]) => {
            if v.is_empty() {
                return Err("array_pop: empty array".to_string());
            }
            let mut next = v.to_vec();
            next.pop();
            Ok(Rv::Array(next.into()))
        }
        (B::ByteLen, [Rv::Str(s)]) => Ok(Rv::Int(i64::try_from(s.len()).unwrap_or(0))),
        (B::ByteAt, [Rv::Str(s), Rv::Int(i)]) => Ok(Rv::Int(
            usize::try_from(*i)
                .ok()
                .and_then(|k| s.as_bytes().get(k))
                .map_or(-1, |b| i64::from(*b)),
        )),
        (B::StringOfBytes, [Rv::Array(v)]) => {
            let bytes: Vec<u8> = v
                .iter()
                .map(|e| {
                    if let Rv::Int(n) = e {
                        u8::try_from(*n & 0xFF).unwrap_or(0)
                    } else {
                        0
                    }
                })
                .collect();
            Ok(Rv::Str(String::from_utf8_lossy(&bytes).into_owned()))
        }
        (B::ArrayLen, [Rv::Array(v)]) => Ok(Rv::Int(i64::try_from(v.len()).unwrap_or(0))),
        (B::StringOfArray, [Rv::Array(v)]) => {
            let mut s = String::new();
            for e in v.iter() {
                let Rv::Str(t) = e else {
                    return Err("string_of_array: non-string element".to_string());
                };
                s.push_str(t);
            }
            Ok(Rv::Str(s))
        }
        (B::ArrayGet, [Rv::Array(v), Rv::Int(i)]) => usize::try_from(*i)
            .ok()
            .and_then(|k| v.get(k).cloned())
            .ok_or_else(|| "array index out of bounds".to_string()),
        (B::ArraySet, [Rv::Array(v), Rv::Int(i), x]) => {
            let k = usize::try_from(*i).map_err(|_| "array index out of bounds".to_string())?;
            if k >= v.len() {
                return Err("array index out of bounds".to_string());
            }
            let mut next = v.to_vec();
            next[k] = x.clone();
            Ok(Rv::Array(next.into()))
        }
        // The unboxed byte buffer under `Bytes`. Bytes are masked into 0..255 on
        // the way in and every op is value-semantic (copy on write), mirroring the
        // C runtime's rc==1 in-place / shared-copy discipline bit-for-bit.
        (B::BufEmpty, []) => Ok(Rv::Buf(Rc::new(Vec::new()))),
        (B::BufNew, [Rv::Int(n), Rv::Int(init)]) => {
            let k = usize::try_from(*n).map_err(|_| "buf_new: negative length".to_string())?;
            #[expect(clippy::cast_sign_loss)]
            let byte = (*init & 0xFF) as u8;
            Ok(Rv::Buf(Rc::new(vec![byte; k])))
        }
        (B::BufLen, [Rv::Buf(v)]) => Ok(Rv::Int(i64::try_from(v.len()).unwrap_or(0))),
        (B::BufGet, [Rv::Buf(v), Rv::Int(i)]) => usize::try_from(*i)
            .ok()
            .and_then(|k| v.get(k))
            .map(|b| Rv::Int(i64::from(*b)))
            .ok_or_else(|| BUFFER_INDEX_ERROR.to_string()),
        (B::BufSet, [Rv::Buf(v), Rv::Int(i), Rv::Int(x)]) => {
            let k = usize::try_from(*i).map_err(|_| BUFFER_INDEX_ERROR.to_string())?;
            if k >= v.len() {
                return Err(BUFFER_INDEX_ERROR.to_string());
            }
            let mut next = v.to_vec();
            #[expect(clippy::cast_sign_loss)]
            {
                next[k] = (*x & 0xFF) as u8;
            }
            Ok(Rv::Buf(Rc::new(next)))
        }
        (B::BufPush, [Rv::Buf(v), Rv::Int(x)]) => {
            let mut next = v.to_vec();
            #[expect(clippy::cast_sign_loss)]
            next.push((*x & 0xFF) as u8);
            Ok(Rv::Buf(Rc::new(next)))
        }
        // Typed buffers (f64 and i64 elements): one raw-word storage, routed to
        // its own dispatcher below.
        (
            B::TbufNew
            | B::TbufLen
            | B::TbufGet
            | B::TbufSet
            | B::TbufBlit
            | B::IbufNew
            | B::IbufLen
            | B::IbufGet
            | B::IbufSet
            | B::IbufBlit,
            _,
        ) => tbuf_builtin(b, vals),
        (B::BufSlice, [Rv::Buf(v), Rv::Int(start), Rv::Int(len)]) => {
            let n = v.len();
            let s = usize::try_from(*start).unwrap_or(0).min(n);
            let take = usize::try_from(*len).unwrap_or(0);
            let e = s.saturating_add(take).min(n);
            Ok(Rv::Buf(Rc::new(v[s..e].to_vec())))
        }
        (B::BufCat, [Rv::Buf(a), Rv::Buf(b)]) => {
            let mut next = a.to_vec();
            next.extend_from_slice(b);
            Ok(Rv::Buf(Rc::new(next)))
        }
        (B::BufEq, [Rv::Buf(a), Rv::Buf(b)]) => Ok(Rv::Bool(a == b)),
        (B::BufCmp, [Rv::Buf(a), Rv::Buf(b)]) => Ok(ord(a.as_slice().cmp(b.as_slice()))),
        // blake3 of the raw bytes, byte-identical to a string's `blake3` over the
        // same bytes and to the native `prism_buf_hash`.
        (B::BufHash, [Rv::Buf(v)]) => Ok(Rv::Str(blake3::hash(v).to_hex().to_string())),
        (B::BufOfString, [Rv::Str(s)]) => Ok(Rv::Buf(Rc::new(s.as_bytes().to_vec()))),
        // The total lossy decode (the boundary wrapper validates first, so on
        // valid input this is lossless); matches `prism_string_of_buf`.
        (B::StringOfBuf, [Rv::Buf(v)]) => Ok(Rv::Str(String::from_utf8_lossy(v).into_owned())),
        (B::BufUtf8Valid, [Rv::Buf(v)]) => Ok(Rv::Bool(std::str::from_utf8(v).is_ok())),
        (B::I64And | B::U64And, [a, b]) => fixed2(a, b, |x, y| x & y),
        (B::I64Or | B::U64Or, [a, b]) => fixed2(a, b, |x, y| x | y),
        (B::I64Xor | B::U64Xor, [a, b]) => fixed2(a, b, |x, y| x ^ y),
        // Shift counts are masked to 0..64; `i64_shr` is arithmetic (signed),
        // `u64_shr` logical, matching the C runtime's signed/unsigned `>>`.
        (B::I64Shl, [Rv::I64(x), Rv::I64(y)]) => {
            Ok(Rv::I64(x.wrapping_shl(u32::try_from(*y & 63).unwrap_or(0))))
        }
        (B::I64Shr, [Rv::I64(x), Rv::I64(y)]) => {
            Ok(Rv::I64(x.wrapping_shr(u32::try_from(*y & 63).unwrap_or(0))))
        }
        (B::U64Shl, [Rv::U64(x), Rv::U64(y)]) => {
            Ok(Rv::U64(x.wrapping_shl(u32::try_from(*y & 63).unwrap_or(0))))
        }
        (B::U64Shr, [Rv::U64(x), Rv::U64(y)]) => {
            Ok(Rv::U64(x.wrapping_shr(u32::try_from(*y & 63).unwrap_or(0))))
        }
        (B::ShowU64, [Rv::U64(n)]) => Ok(Rv::Str(n.to_string())),
        (B::ToI64, [v]) => Ok(Rv::I64(low64(v)?.cast_signed())),
        (B::ToU64, [v]) => Ok(Rv::U64(low64(v)?)),
        (B::IntOfI64, [Rv::I64(n)]) => Ok(Rv::Int(*n)),
        (B::IntOfU64, [Rv::U64(n)]) => {
            Ok(i64::try_from(*n).map_or_else(|_| Rv::Big(BigInt::from(*n)), Rv::Int))
        }
        // The native kernel keys off `kind`. The interpreter compares the runtime
        // values directly, which gives the same stable order for every element
        // type the elaborator specializes.
        (B::SortPrim, [_kind, list]) => {
            let Some(elems) = list.list_elems() else {
                return Err("sort_prim: not a list".into());
            };
            let mut v: Vec<Rv> = elems.into_iter().cloned().collect();
            v.sort_by(rv_key_cmp);
            let mut acc = Rv::Data(NIL.into(), Vec::new().into());
            for e in v.into_iter().rev() {
                acc = Rv::Data(CONS.into(), vec![e, acc].into());
            }
            Ok(acc)
        }
        // `bump` is the arena allocator's raw-cell primitive, emitted only by the
        // arena-lowering pass into effect-lowered Core. The interpreter runs
        // un-lowered Core, so a well-formed program never performs `alloc` there
        // and never reaches this; a direct call is a misuse, reported as such.
        (B::Bump, _) => Err(
            "bump: the arena raw-cell allocator is native-only and has no interpreter form".into(),
        ),
        (op, _) => Err(format!("str builtin {}: wrong args", op.name())),
    }
}
// Total order on the primitive element types the sort kernel specializes,
// matching each canonical `Ord` instance: floats by IEEE total order (the same
// bit order the native radix uses), fixed-width ints by their signedness, and
// Integer (and Char-as-codepoint) by numeric value.
fn rv_key_cmp(a: &Rv, b: &Rv) -> Ordering {
    match (a, b) {
        (Rv::Float(x), Rv::Float(y)) => x.total_cmp(y),
        (Rv::I64(x), Rv::I64(y)) => x.cmp(y),
        (Rv::U64(x), Rv::U64(y)) => x.cmp(y),
        (Rv::Bool(x), Rv::Bool(y)) => x.cmp(y),
        _ => to_big(a)
            .zip(to_big(b))
            .map_or(Ordering::Equal, |(x, y)| x.cmp(&y)),
    }
}

// Render a float as the shortest decimal that round-trips back to `d`, laid out
// like a Python `repr`: full precision with no truncation, scientific notation
// only outside the `[-4, 16)` decimal-exponent window. Both the interpreter and
// the C runtime (`prism_show_float`) and the Lean oracle (`fmtG`) must implement
// the identical algorithm, since they are differentially tested against each
// other; `Float::to_string`'s exact-integer expansion would not be portable.
//
// `0.1` stays "0.1", `0.1 +. 0.2` shows "0.30000000000000004", `100.0` is
// "100", `1e100` is "1e+100". Rust's `{:e}` is correctly rounded (round half to
// even) like the printf family, so the digits and exponent agree with C.
// `pub` so the native float-formatter parity test (`tests/float_fmt.rs`) can
// diff the C runtime's shortest-round-trip output against this, the canonical
// interpreter form. Exposing it changes no output; the C side conforms to this.
// The `unwrap`s rest on `{:e}` invariants (always an `e`, always parseable), so
// the function does not panic for any finite or non-finite `f64`.
#[must_use]
#[allow(clippy::missing_panics_doc)]
pub fn fmt_g(d: f64) -> String {
    if d.is_nan() {
        return "nan".to_string();
    }
    if d.is_infinite() {
        return if d < 0.0 { "-inf" } else { "inf" }.to_string();
    }
    if d == 0.0 {
        return if d.is_sign_negative() { "-0" } else { "0" }.to_string();
    }
    // Shortest scientific form (fewest significant digits, 1..=17) that round-
    // trips; 17 digits always suffice for an IEEE double, so the fallback always
    // parses. `find` formats only up to the winning precision, so the chosen
    // string is reused rather than reformatted.
    let sci = (1..17usize)
        .map(|cand| format!("{:.*e}", cand - 1, d))
        .find(|s| s.parse::<f64>() == Ok(d))
        .unwrap_or_else(|| format!("{:.*e}", 16, d)); // "[-]D[.DDD]e±XX"
    let neg = sci.starts_with('-');
    let (mant, exp) = sci.trim_start_matches('-').split_once('e').unwrap();
    let e10: i32 = exp.parse().unwrap();
    let digits: String = mant.chars().filter(|c| *c != '.').collect();
    let body = if (-4..16).contains(&e10) {
        layout_fixed(&digits, e10)
    } else {
        // Scientific: one digit before the point, the rest after (`layout_fixed`
        // at exponent 0 does exactly this), then the `e±XX` suffix.
        let m = layout_fixed(&digits, 0);
        let sign = if e10 < 0 { '-' } else { '+' };
        format!("{m}e{sign}{:02}", e10.abs())
    };
    if neg {
        format!("-{body}")
    } else {
        body
    }
}

// Place the decimal point in `digits` (the significant figures, no point) so the
// leading digit has place value 10^`e10`. Trailing zeros are stripped.
fn layout_fixed(digits: &str, e10: i32) -> String {
    if e10 >= 0 {
        let k = e10.unsigned_abs() as usize + 1;
        if digits.len() <= k {
            format!("{digits}{}", "0".repeat(k - digits.len()))
        } else {
            strip_zeros(format!("{}.{}", &digits[..k], &digits[k..]))
        }
    } else {
        let zeros = "0".repeat((-e10 - 1).unsigned_abs() as usize);
        strip_zeros(format!("0.{zeros}{digits}"))
    }
}

fn strip_zeros(s: String) -> String {
    if s.contains('.') {
        s.trim_end_matches('0').trim_end_matches('.').to_string()
    } else {
        s
    }
}

// IEEE 754 value equality is the intended semantics of Eqf/Nef (NaN never
// equal, +0.0 == -0.0), matching the backend's `fcmp oeq`/`une`. This is not
// bit equality.
#[allow(clippy::float_cmp)]
fn dispatch_float_op(op: CoreOp, x: f64, y: f64) -> Result<Rv, String> {
    Ok(match op {
        CoreOp::Addf => Rv::Float(x + y),
        CoreOp::Subf => Rv::Float(x - y),
        CoreOp::Mulf => Rv::Float(x * y),
        CoreOp::Divf => Rv::Float(x / y),
        CoreOp::Eqf => Rv::Bool(x == y),
        CoreOp::Nef => Rv::Bool(x != y),
        CoreOp::Ltf => Rv::Bool(x < y),
        CoreOp::Lef => Rv::Bool(x <= y),
        CoreOp::Gtf => Rv::Bool(x > y),
        CoreOp::Gef => Rv::Bool(x >= y),
        _ => return Err(format!("op {op:?} not defined for Float")),
    })
}

// i64 fast path: arithmetic that overflows i64 promotes to a normalized Big.
// The six ordering/equality ops are identical across every numeric type; only
// the arithmetic arms differ, so each `dispatch_*_op` consults this first.
fn cmp_op<T: Ord>(op: CoreOp, x: &T, y: &T) -> Option<Rv> {
    Some(Rv::Bool(match op {
        CoreOp::Eq => x == y,
        CoreOp::Ne => x != y,
        CoreOp::Lt => x < y,
        CoreOp::Le => x <= y,
        CoreOp::Gt => x > y,
        CoreOp::Ge => x >= y,
        _ => return None,
    }))
}

fn dispatch_int_op(op: CoreOp, x: i64, y: i64) -> Result<Rv, String> {
    if matches!(op, CoreOp::Div | CoreOp::Rem) && y == 0 {
        return Err("division by zero".into());
    }
    if let Some(r) = cmp_op(op, &x, &y) {
        return Ok(r);
    }
    let wide = |r: Option<i64>, f: fn(BigInt, BigInt) -> BigInt| {
        r.map_or_else(|| norm(f(BigInt::from(x), BigInt::from(y))), Rv::Int)
    };
    Ok(match op {
        CoreOp::Add => wide(x.checked_add(y), |a, b| a + b),
        CoreOp::Sub => wide(x.checked_sub(y), |a, b| a - b),
        CoreOp::Mul => wide(x.checked_mul(y), |a, b| a * b),
        CoreOp::Div => wide(x.checked_div(y), |a, b| a / b),
        CoreOp::Rem => Rv::Int(x.wrapping_rem(y)),
        _ => return Err(format!("op {op:?} not defined for Int")),
    })
}

fn dispatch_bigint_op(op: CoreOp, x: BigInt, y: BigInt) -> Result<Rv, String> {
    if matches!(op, CoreOp::Div | CoreOp::Rem) && y.sign() == Sign::NoSign {
        return Err("division by zero".into());
    }
    if let Some(r) = cmp_op(op, &x, &y) {
        return Ok(r);
    }
    Ok(match op {
        CoreOp::Add => norm(x + y),
        CoreOp::Sub => norm(x - y),
        CoreOp::Mul => norm(x * y),
        CoreOp::Div => norm(x / y),
        CoreOp::Rem => norm(x % y),
        _ => return Err(format!("op {op:?} not defined for Int")),
    })
}

pub(super) fn prim(op: CoreOp, a: &Rv, b: &Rv) -> Result<Rv, String> {
    if let (Rv::Float(x), Rv::Float(y)) = (a, b) {
        return dispatch_float_op(op, *x, *y);
    }
    if let (Rv::Int(x), Rv::Int(y)) = (a, b) {
        return dispatch_int_op(op, *x, *y);
    }
    let (Some(x), Some(y)) = (to_big(a), to_big(b)) else {
        return Err("arithmetic on non-numeric value".into());
    };
    dispatch_bigint_op(op, x, y)
}

fn norm(n: BigInt) -> Rv {
    i64::try_from(&n).map_or_else(|_| Rv::Big(n), Rv::Int)
}

fn to_big(v: &Rv) -> Option<BigInt> {
    match v {
        Rv::Int(n) => Some(BigInt::from(*n)),
        Rv::Big(n) => Some(n.clone()),
        _ => None,
    }
}

fn low64(v: &Rv) -> Result<u64, String> {
    match v {
        Rv::Int(n) => Ok(n.cast_unsigned()),
        Rv::Big(n) => {
            let lo = n.iter_u64_digits().next().unwrap_or(0);
            Ok(if n.sign() == Sign::Minus {
                lo.wrapping_neg()
            } else {
                lo
            })
        }
        _ => Err("to_i64/to_u64: wrong args".into()),
    }
}

fn probe_enabled(name: &str) -> bool {
    let Ok(filter) = env::var("PRISM_PROBES") else {
        return false;
    };
    filter
        .split(',')
        .map(str::trim)
        .any(|pat| pat == "*" || pat == name)
}

fn fixed2(a: &Rv, b: &Rv, f: fn(u64, u64) -> u64) -> Result<Rv, String> {
    match (a, b) {
        (Rv::I64(x), Rv::I64(y)) => Ok(Rv::I64(
            f(x.cast_unsigned(), y.cast_unsigned()).cast_signed(),
        )),
        (Rv::U64(x), Rv::U64(y)) => Ok(Rv::U64(f(*x, *y))),
        _ => Err("fixed-width op: wrong args".into()),
    }
}

const fn ord(o: Ordering) -> Rv {
    Rv::Int(match o {
        Ordering::Less => -1,
        Ordering::Equal => 0,
        Ordering::Greater => 1,
    })
}
