//! Rocq emitter, built as a `wasm32-wasip1` command.
//!
//! Host↔emitter protocol (shared by every adsmt emitter): the
//! serialized certificate arrives on **stdin**, the prover source
//! goes to **stdout**, exit code `0` ok / `2` unsupported / `3`
//! malformed-cert / else internal. This wrapper declares
//! `wire = "cbor"`, so it decodes the certificate from CBOR and
//! re-states it as Rocq via `adsmt_emit_rocq::emit_rocq`.

use std::io::{Read, Write};
use std::process::ExitCode;

fn main() -> ExitCode {
    let mut bytes = Vec::new();
    if let Err(e) = std::io::stdin().read_to_end(&mut bytes) {
        eprintln!("rocq-emitter: reading stdin: {e}");
        return ExitCode::from(1);
    }

    let cert: adsmt_cert::Certificate = match ciborium::from_reader(&bytes[..]) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("rocq-emitter: malformed certificate: {e}");
            return ExitCode::from(3);
        }
    };

    let text = adsmt_emit_rocq::emit_rocq(&cert);
    if std::io::stdout().write_all(text.as_bytes()).is_err() {
        return ExitCode::from(1);
    }
    ExitCode::SUCCESS
}
