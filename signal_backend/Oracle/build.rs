fn main(){
 let root=std::path::PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap()).join("../..");
 let directory=root.join(".deps/libsignal-v0.106.1/rust/net/src/proto");
 let schema=directory.join("chat_websocket.proto");
 println!("cargo:rerun-if-changed={}",schema.display());
 prost_build::Config::new().compile_protos(&[schema],&[directory]).unwrap();
}
