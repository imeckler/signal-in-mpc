fn main(){
 let root=std::path::PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap()).join("../..");
 let directory=root.join(".deps/libsignal-v0.106.1/rust/net/src/proto");
 let schema=directory.join("chat_websocket.proto");
 println!("cargo:rerun-if-changed={}",schema.display());
 prost_build::Config::new().compile_protos(&[schema],&[directory]).unwrap();
 let protocol=root.join(".deps/libsignal-v0.106.1/rust/protocol/src/proto");
 let schemas=[protocol.join("storage.proto"),protocol.join("service.proto")];
 for schema in &schemas {println!("cargo:rerun-if-changed={}",schema.display());}
 prost_build::Config::new().compile_protos(&schemas,&[protocol]).unwrap();
 let spqr=root.join(".deps/libsignal-vendor/spqr/src/proto");
 let schema=spqr.join("pq_ratchet.proto");
 println!("cargo:rerun-if-changed={}",schema.display());
 prost_build::Config::new().compile_protos(&[schema],&[spqr]).unwrap();
}
