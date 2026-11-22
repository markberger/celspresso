//! Compile the pinned cel-spec protos into a descriptor set the runner can load.
use std::path::PathBuf;

fn main() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../third_party/cel-spec/proto");
    let files = [
        "cel/expr/conformance/test/simple.proto",
        "cel/expr/conformance/proto2/test_all_types.proto",
        "cel/expr/conformance/proto2/test_all_types_extensions.proto",
        "cel/expr/conformance/proto3/test_all_types.proto",
    ];
    println!("cargo:rerun-if-changed={}", root.display());
    let fds = protox::compile(files, [&root])
        .unwrap_or_else(|e| panic!("compiling cel-spec protos failed ({e}); run `git submodule update --init`"));
    let out = PathBuf::from(std::env::var("OUT_DIR").unwrap()).join("cel_spec.bin");
    std::fs::write(out, prost::Message::encode_to_vec(&fds)).unwrap();
}
