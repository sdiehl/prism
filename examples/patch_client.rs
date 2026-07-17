//! Minimal reference client for `prism patch serve`.
//!
//! Usage:
//! `cargo run --example patch_client -- target/debug/prism FILE TARGET REPLACEMENT [--commit]`

use std::fs;
use std::io::{BufRead, BufReader, Write};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};

use serde_json::{json, Value};

const PROTOCOL: &str = "prism-patch-protocol-v1";
const REQUIRED_ARGS: usize = 5;

struct Client {
    child: Child,
    input: ChildStdin,
    output: BufReader<ChildStdout>,
    next_id: u64,
}

impl Client {
    fn start(prism: &str, file: &str) -> Result<Self, String> {
        let mut child = Command::new(prism)
            .args(["patch", "serve", file])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()
            .map_err(|error| format!("could not start patch server: {error}"))?;
        let input = child
            .stdin
            .take()
            .ok_or_else(|| "patch server has no stdin".to_string())?;
        let output = child
            .stdout
            .take()
            .ok_or_else(|| "patch server has no stdout".to_string())?;
        Ok(Self {
            child,
            input,
            output: BufReader::new(output),
            next_id: 1,
        })
    }

    fn request(&mut self, verb: &str, fields: Value) -> Result<Value, String> {
        let id = self.next_id;
        self.next_id += 1;
        let mut request = json!({
            "protocol": PROTOCOL,
            "id": id,
            "verb": verb,
        });
        let object = request
            .as_object_mut()
            .ok_or_else(|| "request is not an object".to_string())?;
        let Value::Object(additions) = fields else {
            return Err("request fields are not an object".to_string());
        };
        object.extend(additions);
        serde_json::to_writer(&mut self.input, &request).map_err(|error| error.to_string())?;
        self.input
            .write_all(b"\n")
            .and_then(|()| self.input.flush())
            .map_err(|error| error.to_string())?;
        let mut line = String::new();
        self.output
            .read_line(&mut line)
            .map_err(|error| error.to_string())?;
        let response: Value = serde_json::from_str(&line).map_err(|error| error.to_string())?;
        if response["id"] != id || response["protocol"] != PROTOCOL {
            return Err(format!("mismatched protocol response: {response}"));
        }
        if response["ok"] != true {
            return Err(format!("patch refused: {}", response["payload"]));
        }
        Ok(response["payload"].clone())
    }
}

impl Drop for Client {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

fn main() -> Result<(), String> {
    let args = std::env::args().collect::<Vec<_>>();
    if args.len() < REQUIRED_ARGS {
        return Err(format!(
            "usage: {} PRISM FILE TARGET REPLACEMENT [--commit]",
            args.first().map_or("patch_client", String::as_str)
        ));
    }
    let prism = &args[1];
    let file = &args[2];
    let target = &args[3];
    let replacement = fs::read_to_string(&args[4])
        .map_err(|error| format!("could not read replacement: {error}"))?;
    let commit = args.get(5).is_some_and(|arg| arg == "--commit");
    let mut client = Client::start(prism, file)?;

    let fetched = client.request("fetch", json!({ "target": target }))?;
    println!("fetched {} @ {}", fetched["name"], fetched["core_hash"]);
    println!("{}", fetched["rendered"].as_str().unwrap_or_default());

    let impact = client.request("impact", json!({ "target": target }))?;
    println!("importer cone: {}", impact["importers"]);

    let patch = client.request(
        "create",
        json!({ "target": target, "replacement": replacement }),
    )?;
    let report = client.request("submit", json!({ "patch": patch }))?;
    println!(
        "tier {} ({}), {} -> {}",
        report["tier"]["level"],
        report["tier"]["claim"],
        report["core_hash_before"],
        report["core_hash_after"]
    );
    println!("impacted: {}", report["importer_cone"]);

    if commit {
        let committed = client.request("commit", json!({}))?;
        println!("committed {}", committed["path"]);
    } else {
        let discarded = client.request("discard", json!({}))?;
        println!("discarded stage {}", discarded["discarded"]);
    }
    Ok(())
}
