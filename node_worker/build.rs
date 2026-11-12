//! Links the engine library built by `build_hybrid_v3.py --engine-abi` (engine_abi.cpp with the
//! legacy library, and the field engine object), and the field engine's and EMP's own
//! libraries in the order the recorded fixture link uses (one argument per line in
//! `engine-abi-link-VARIANT.txt`, written by the same build).
//!
//! Variant: `v3` (malicious, production), `sh-v3` (feature `semi-honest`), each with `-test`
//! under feature `test-engine`. Directory: `NODE_WORKER_ENGINE_DIR`, default
//! `.deps/two-party-comparison` of this repository. Nothing is linked without feature `engine`.
use std::path::PathBuf;

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-env-changed=NODE_WORKER_ENGINE_DIR");
    if std::env::var_os("CARGO_FEATURE_ENGINE").is_none() {
        return;
    }
    let sh = std::env::var_os("CARGO_FEATURE_SEMI_HONEST").is_some();
    let test = std::env::var_os("CARGO_FEATURE_TEST_ENGINE").is_some();
    let variant = format!("{}v3{}", if sh { "sh-" } else { "" }, if test { "-test" } else { "" });
    let dir = match std::env::var_os("NODE_WORKER_ENGINE_DIR") {
        Some(d) => PathBuf::from(d),
        None => PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../.deps/two-party-comparison"),
    };
    let library = dir.join(format!("libengine-abi-{variant}.a"));
    let arguments = dir.join(format!("engine-abi-link-{variant}.txt"));
    if !library.is_file() || !arguments.is_file() {
        panic!(
            "engine library {} or {} missing: build it with `python3 handshake_backend/EmpHybridWork/build_hybrid_v3.py --engine-abi {variant}`, or build without feature `engine`",
            library.display(),
            arguments.display()
        );
    }
    println!("cargo:rerun-if-changed={}", library.display());
    println!("cargo:rerun-if-changed={}", arguments.display());
    println!("cargo:rustc-link-search=native={}", dir.display());
    println!("cargo:rustc-link-lib=static=engine-abi-{variant}");
    let text = std::fs::read_to_string(&arguments).expect("link arguments");
    for line in text.lines().filter(|l| !l.is_empty()) {
        println!("cargo:rustc-link-arg={line}");
    }
}
