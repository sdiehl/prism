# Endo's Passable as a Prism ADT

Based on [@endo/pass-style](https://docs.endojs.org/types/_endo_pass-style.Passable.html).

## What Passable Is

A Passable is acyclic data that can be marshalled (serialized for cross-vat communication). It must be hardened (deep-frozen) and is classified by **PassStyle**:

| PassStyle | Kind | Marshalling |
|---|---|---|
| `undefined`, `null`, `boolean`, `number`, `bigint`, `string`, `symbol`, `byteArray` | **Atom** | Pass-by-copy |
| `copyArray` | **Container** | Pass-by-copy (recursive) |
| `copyRecord` | **Container** | Pass-by-copy (recursive) |
| `tagged` | **Container** | Pass-by-copy (recursive) |
| `remotable` | **Capability** | Pass-by-reference (slot) |
| `promise` | **Capability** | Pass-by-reference (slot) |
| `error` | **Special** | Pass-by-copy (marshalled as tagged) |

In Prism, this recursive structure maps naturally to an algebraic data type.

## Core ADT

The full implementation lives at [examples/passable.pr](../../../examples/passable.pr) with a parametric formulation.
For doctest purposes, we import `Passable` and show a concrete (non-parametric) instantiation of it:

```prism
import Passable (..)

-- | A concrete instantiation of Passable using SlotIndex and ErrorRepr.
type MyPassable = Passable(SlotIndex, SlotIndex, ErrorRepr)

-- | A slot index in the CapTP import/export table. Capabilities
-- (remotables and promises) are never serialized as values; they
-- are referenced by position in the per-session slot table.
pub newtype SlotIndex = SlotIndex(Int)

-- | Error representation: a message string plus optional data.
pub type ErrorRepr = ErrorRepr {
  message : String,
  data : Option(MyPassable)
}

fn main() =
  let atom = Atom(ABool(true))
  let arr = CopyArray(Cons(Atom(ANumber(42.0)), Nil))
  let tagged = CopyTagged("error", Atom(AString("oops")))
  let slot = SlotIndex(0)
  let ref = Remotable(slot)
  let prom = Promise(SlotIndex(1))
  let err = PassError(ErrorRepr { message = "fail", data = None })
  let _ = atom
  let _ = arr
  let _ = tagged
  let _ = ref
  let _ = prom
  let _ = err
  println("Passable ADT ok")
```

## Structural Properties

### Acyclic by Construction

Prism's data types are inductive (no lazy cycles via thunks in the value space), so `Passable` is naturally acyclic. The `List(Passable(p, r, e))` and `List((String, Passable(p, r, e)))` fields cannot form cycles. Endo's Passable must enforce acyclicity at runtime; Prism's type system guarantees it.

### Immutable (Hardened) by Default

All Prism values are immutable by default (reference-counted, no shared mutation). This corresponds to Endo's `harden()` requirement. There is no unhardened state to worry about.

### No `this`-style Identity

Prism records have structural equality by default (via `Eq`), not identity-based equality. This matches Endo's pass-by-copy semantics for atoms and containers. Capabilities (`Remotable`, `Promise`) use slot-index identity, which is pointer-like but session-scoped.

## Separating Data from References (Slots)

There is an active debate in OCapN standardization ([Issue #172: Reusability of passable data](https://github.com/ocapn/ocapn/issues/172)) regarding how heavily data and references should be commingled on the wire.

Endo's JavaScript implementation serializes capabilities directly in-line with data. However, **Cap'n Proto RPC** takes a different approach: it strictly separates the pure-data payload from an out-of-band "Capability Table" (or list of Slots). 

The out-of-band approach has a massive performance benefit for distributed capability systems: **Relay Optimization**. If a "kernel" vat or a "comms" vat needs to relay a message from one peer to another, it must translate the capability indices (e.g., mapping Import 5 on connection A to Export 2 on connection B). If capabilities are separate from the byte payload:
1. The kernel can blindly copy the data bytes without parsing, traversing, or reserializing the payload.
2. It only needs to rewrite the small, fixed-size capability table shipped alongside the payload.
3. This enables extremely high-throughput routing.

### Modeling Out-of-Band Slots in Prism

If Prism adopts the Cap'n Proto / OCapN #172 design, live capabilities are not variants of the recursive data type used in the payload; instead, they are stripped during serialization. The resulting network payload treats the body as an opaque byte stream, keeping the routing layer entirely agnostic to the data schema:

```prism
-- | A Payload strictly separates the data body from the capability table.
-- (Cap'n Proto calls this Payload; Endo calls it CapData)
pub type Payload = Payload {
  -- The pre-serialized, pure-data body of the message.
  -- Treated as opaque bytes by the routing/relay layer.
  body : String, -- (Prism's representation of byte arrays)
  
  -- The out-of-band array of capabilities (Remotables and Promises)
  slots : List(CapDescriptor) 
}

-- | CapDescriptors define what each slot index resolves to
pub type CapDescriptor
  = ImportObject(Int)
  | ImportPromise(Int)
  | Handoff(String)
```

In this model, when the serialization layer encounters a capability, it appends the capability to the `slots` list and emits a slot index into the serialized `body` stream. The routing kernel or comms vat can then blindly forward the `body` bytes without parsing them, only ever inspecting or rewriting the small, fixed-size `slots` table.

## Tagged Values (CopyTagged)

Endo's `CopyTagged` represents "pass-by-copy data with a semantic tag" -- e.g., errors, brands, and custom copyable types. The tag identifies the kind and the body carries the payload.

```prism
-- | A tagged value: `@@tag` identifies the kind, `@@body` is the payload.
-- In Prism this is just a pair of a tag string and a body value.
pub type Tagged(a) = Tagged(String, a)

fn main() =
  let t = Tagged("error", "oops")
  match t of
    Tagged(tag, _) => println(tag)
```

This enables open extension: new wire formats can be defined as new tags without changing the core ADT.

## Prism Typeclass: `Marshallable`

Just as Endo has a `Passable` type in TypeScript, Prism has a `Marshallable` class that types can implement (see `examples/Marshallable.pr` for the complete implementation with recursive container instances):

```prism
import Passable (..)

-- | A slot index in the CapTP import/export table.
pub newtype SlotIndex = SlotIndex(Int)

-- | Error representation: a message string plus optional data.
pub type ErrorRepr = ErrorRepr {
  message : String,
  data : Option(MyPassable)
}

-- | A concrete instantiation of Passable using SlotIndex and ErrorRepr.
pub alias MyPassable = Passable(SlotIndex, SlotIndex, ErrorRepr)

-- | A type whose values can be marshalled across vat boundaries.
pub class Marshallable(a) {
  encode : (a) -> MyPassable,
  decode : (MyPassable) -> Option(a)
}

instance marshallableInt : Marshallable(Int) {
  fn encode(n) = Atom(ABigInt(n)),
  fn decode(p) =
    match p of {
      Atom(ABigInt(n)) => Some(n),
      _ => None
    }
}

fn main() =
  let encoded = encode(42)
  let decoded = (decode(encoded) : Option(Int))
  match decoded of {
    Some(42) => println("Marshallable ok"),
    _ => println("failed")
  }
```

Derivable instances (aspirational — `deriving instance` is not yet implemented):
```prism,ignore
-- | All scalar types are atoms.
deriving instance Marshallable(Bool)
deriving instance Marshallable(Int)
deriving instance Marshallable(Float)
deriving instance Marshallable(String)

-- | Containers are deriveable when their elements are Marshallable.
deriving instance Marshallable(Passable)  -- identity

-- | Recursive derivation.
type User = User { name : String, age : Int }
deriving instance Marshallable(User)  -- becomes CopyRecord
```

## Wire Format Summary

The wire format follows the same length-prefixed tag scheme as Prism's
[durability serialization](https://github.com/sdiehl/prism/blob/main/lib/std/Replay.pr):
each entry is encoded as a single-character tag, a decimal length prefix, a `:`
delimiter, then the payload of exactly that many characters. Nested containers
encode recursively.

| Prism Passable | Endo PassStyle | Prism durability serialization |
|---|---|---|
| `AUndefined` | `undefined` | `U0:` |
| `ANull` | `null` | `N0:` |
| `ABool(b)` | `boolean` | `B<len>:<0\|1>` |
| `ANumber(f)` | `number` | `F<len>:<float-str>` |
| `ABigInt(n)` | `bigint` | `Z<len>:<int-str>` |
| `AString(s)` | `string` | `S<len>:<s>` |
| `ASymbol(s)` | `symbol` | `Y<len>:<s>` |
| `AByteArray(b)` | `byteArray` | `X<len>:<hex>` |
| `CopyArray(xs)` | `copyArray` | `[<len>:<encoded-elements...>` |
| `CopyRecord(kvs)` | `copyRecord` | `{<len>:<encoded-kvs...>` |
| `CopyTagged(t, b)` | `tagged` | `T<len>:<tag><body>` |
| `Remotable(i)` | `remotable` | `R<len>:<slot-index>` |
| `Promise(i)` | `promise` | `P<len>:<slot-index>` |
| `PassError(e)` | `error` | `E<len>:<message><data>` |

The length prefix makes encoding self-delimiting — the decoder reads exactly
`length` chars regardless of content, so no escaping is needed. This is the same
design as the `serialize`/`deserialize` functions in `lib/std/Replay.pr`.

## Relationship to Sturdyrefs

A `Sturdyref` (persistent reference) is not a `Passable` in the marshalling sense -- it is a locator (URI + swiss number) used to bootstrap a connection and fetch an initial `Remotable`. Once resolved, the live `Remotable(slot)` is what gets passed in messages.
