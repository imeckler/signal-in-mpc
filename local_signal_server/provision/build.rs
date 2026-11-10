// Compile the schemas this tool needs, from the same sources signal_backend/Oracle compiles:
//   chat_websocket.proto  WebSocketMessage / Request / Response (the MPC client's framing)
//   storage.proto         libsignal SessionRecord (RecordStructure / SessionStructure)
//   pq_ratchet.proto      SPQR state (PqRatchetState)
fn main() {
    let root = std::path::PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap()).join("../..");
    let net = root.join(".deps/libsignal-v0.106.1/rust/net/src/proto");
    let protocol = root.join(".deps/libsignal-v0.106.1/rust/protocol/src/proto");
    let spqr = root.join(".deps/libsignal-vendor/spqr/src/proto");
    let schemas = [
        (net.join("chat_websocket.proto"), net.clone()),
        (protocol.join("storage.proto"), protocol.clone()),
        (spqr.join("pq_ratchet.proto"), spqr.clone()),
    ];
    for (schema, dir) in &schemas {
        println!("cargo:rerun-if-changed={}", schema.display());
        prost_build::Config::new().compile_protos(&[schema], &[dir]).unwrap();
    }
}
