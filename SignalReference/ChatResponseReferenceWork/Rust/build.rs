fn main() {
    let root = std::path::PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap()).join("../../..");
    let directory = root.join(".deps/libsignal-v0.106.1/rust/net/src");
    let schema = directory.join("proto/chat_websocket.proto");
    println!("cargo:rerun-if-changed={}", schema.display());
    // Exact chat-websocket generator options from the pinned net/build.rs.
    prost_build::Config::new()
        .bytes([".signal.proto.chat_provisioning", ".signal.proto.chat_websocket"])
        .compile_protos(&[schema], &[directory])
        .unwrap();
}
