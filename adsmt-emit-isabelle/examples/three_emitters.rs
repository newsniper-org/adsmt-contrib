//! B-1: run a REAL certificate (produced by an actual native-only solve) through
//! all three emitters, instead of the hand-assembled CertBuilder payloads the
//! existing tests use.
//!
//! usage: cargo run -p adsmt-emit-isabelle --example three_emitters -- <cert.json>

fn main() {
    let path = std::env::args().nth(1).expect("usage: three_emitters <cert.json>");
    let src = std::fs::read_to_string(&path).expect("read cert");
    let cert: adsmt_cert::Certificate = serde_json::from_str(&src).expect("parse cert");

    println!("### certificate: {} steps", cert.steps.len());

    for (name, out) in [
        ("lean", std::panic::catch_unwind(|| adsmt_cert::lean_emit::emit_lean(&cert))),
        ("rocq", std::panic::catch_unwind(|| adsmt_emit_rocq::emit_rocq(&cert))),
        ("isabelle", std::panic::catch_unwind(|| adsmt_emit_isabelle::emit_isabelle(&cert))),
    ] {
        println!("\n=================== {name} ===================");
        match out {
            Ok(s) => println!("{s}"),
            Err(_) => println!("!!! PANICKED"),
        }
    }
}
