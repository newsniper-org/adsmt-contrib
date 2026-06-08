//! Isabelle/HOL emitter, built as a `wasm32-wasip1` command.
//!
//! Host↔emitter protocol: CBOR certificate on stdin, Isabelle
//! source on stdout, exit `0` ok / `3` malformed-cert / else
//! internal. Re-states the certificate via
//! `adsmt_emit_isabelle::emit_isabelle`.

use std::io::{Read, Write};
use std::process::ExitCode;

fn main() -> ExitCode {
    let mut bytes = Vec::new();
    if let Err(e) = std::io::stdin().read_to_end(&mut bytes) {
        eprintln!("isabelle-emitter: reading stdin: {e}");
        return ExitCode::from(1);
    }

    let cert: adsmt_cert::Certificate = match ciborium::from_reader(&bytes[..]) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("isabelle-emitter: malformed certificate: {e}");
            return ExitCode::from(3);
        }
    };

    let text = adsmt_emit_isabelle::emit_isabelle(&cert);
    if std::io::stdout().write_all(text.as_bytes()).is_err() {
        return ExitCode::from(1);
    }
    ExitCode::SUCCESS
}
