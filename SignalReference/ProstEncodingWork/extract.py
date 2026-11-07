#!/usr/bin/env python3
"""Extract unchanged locked prost encoding functions; never substitute Rust."""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parent
ROOT = REFERENCE.parent
spec = importlib.util.spec_from_file_location("canonical_extract", REFERENCE / "extract.py")
canonical = importlib.util.module_from_spec(spec)
spec.loader.exec_module(canonical)
PINS = canonical.PINS
digest = canonical.digest
PROFILES = {
    "Length": {"starts": ["crate::encoding::varint::encoded_len_varint"]},
    "Encode": {"starts": ["crate::encoding::varint::encode_varint"]},
    "EncodeBody": {"starts": ["crate::encoding::varint::encode_varint"],
                   "extra": ["--include=bytes::buf::buf_mut::BufMut::put_u8"]},
    "UInt32": {"starts": ["crate::encoding::uint32::encode"]},
    "VecPutSlice": {"package": "bytes@1.12.0",
                    "starts": ["{crate::buf::buf_mut::BufMut for alloc::vec::Vec}::put_slice"]},
}
SOURCE_HASHES = {
    ".deps/libsignal-vendor/prost-0.14.4/src/encoding/varint.rs": "29f75ff30f6a30e07ec017f3260cff9ffbf52cddbd9e4f26f72d705725cebc10",
    ".deps/libsignal-vendor/prost-0.14.4/src/encoding.rs": "2262da48addaf0544bb7c1f38ae617160fc4fba1781bd9c99fdc96b0dd6288d4",
    ".deps/libsignal-vendor/prost-0.14.4/Cargo.toml": "0d6f06dd96d0b54342ea7e1d9a3fdc8d166782bde60771b06c5cb0bb38a06592",
    ".deps/libsignal-vendor/bytes-1.12.0/src/buf/buf_mut.rs": "c76d0a846cf6e2c42af7acf0bbedc49a30ce3b9185392835c6a6f8b06a128b9e",
    ".deps/libsignal-v0.106.1/Cargo.lock": "5a8597e00b115284fa2fadd622ad7340bcb1e135ee435530f075d66b576a620e",
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("profile", choices=PROFILES)
    parser.add_argument("--charon-only", action="store_true")
    args = parser.parse_args()
    profile = PROFILES[args.profile]
    package = profile.get("package", "prost@0.14.4")
    source = canonical.check_sources()
    for filename, expected in SOURCE_HASHES.items():
        if digest(ROOT / filename) != expected:
            raise ValueError(f"Pinned source differs: {filename}")
    rust = ROOT / ".deps/rust-nightly-2026-08-18"
    charon = (REFERENCE / PINS["charon"]["directory"] / "target/release/charon").resolve()
    aeneas = (REFERENCE / PINS["aeneas"]["directory"] / "aeneas").resolve()
    versions = {"charon": subprocess.check_output([str(charon), "version"], text=True).strip(),
                "aeneas": subprocess.check_output([str(aeneas), "-version"], text=True).strip(),
                "rustc": subprocess.check_output([str(rust / "bin/rustc"), "--version"], text=True).strip()}
    if (PINS["charon"]["commit"] not in versions["charon"] or
            PINS["aeneas"]["release"] not in versions["aeneas"] or
            versions["rustc"] != PINS["charon"]["rustc_version"]):
        raise ValueError(f"Wrong tool versions: {versions}")
    destination = HERE / "Artifacts" / args.profile
    destination.mkdir(parents=True, exist_ok=True)
    llbc = destination / "prost_encoding.llbc"
    env = os.environ.copy()
    env.update({"PATH": str(rust / "bin") + os.pathsep + env.get("PATH", ""),
                "CHARON_TOOLCHAIN_IS_IN_PATH": "1", "DYLD_LIBRARY_PATH": str(rust / "lib"),
                "LD_LIBRARY_PATH": str(rust / "lib"),
                "CARGO_HOME": str(ROOT / ".deps/libsignal-cargo-home"),
                "CARGO_TARGET_DIR": str(HERE / "Build"), "RUSTFLAGS": ""})
    subprocess.run([str(rust / "bin/cargo"), "clean", "--package", package,
                    "--target", "aarch64-apple-darwin"], cwd=source, env=env, check=True,
                   stdout=subprocess.DEVNULL)
    command = [str(charon), "cargo", "--preset=aeneas", "--no-dedup-serialized-ast",
               "--sysroot=default", "--error-on-warnings", "--start-from=" + ",".join(profile["starts"]),
               *profile.get("extra", []), "--dest-file=" + str(llbc),
               "--", "--package", package, "--lib", "--locked", "--offline", "--target", "aarch64-apple-darwin"]
    llbc.unlink(missing_ok=True)
    with (destination / "charon.log").open("w") as log:
        status = subprocess.run(command, cwd=source, env=env, stdout=log, stderr=subprocess.STDOUT)
    report = {"candidate_reference": True, "accepted_reference": False, "versions": versions,
              "source_patches": [], "source_sha256": SOURCE_HASHES, "profile": args.profile,
              "charon_command": [x.replace(str(ROOT), "$WORKSPACE") for x in command],
              "charon_exit_code": status.returncode, "rustflags": env["RUSTFLAGS"]}
    if llbc.exists():
        report.update(canonical.inventory(llbc))
    report_path = destination / "inventory.json"
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    if status.returncode or not llbc.exists() or report["has_errors"]:
        print(f"Incomplete Charon extraction: {destination.relative_to(ROOT)}")
        return 1
    if args.charon_only:
        print(f"Charon complete: {destination.relative_to(ROOT)}")
        return 0
    generated = HERE / "Generated" / args.profile
    generated.mkdir(parents=True, exist_ok=True)
    for previous in generated.glob("*.lean"):
        previous.unlink()
    command = [str(aeneas), "-backend", "lean", str(llbc), "-dest", str(REFERENCE),
               "-subdir", "/ProstEncodingWork/Generated/" + args.profile, "-split-files",
               "-namespace", "ProstEncoding", "-warnings-as-errors", "-no-progress-bar"]
    with (destination / "aeneas.log").open("w") as log:
        status = subprocess.run(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
    report["aeneas_command"] = [x.replace(str(ROOT), "$WORKSPACE") for x in command]
    report["aeneas_exit_code"] = status.returncode
    report["generated_files"] = {str(p.relative_to(REFERENCE)): digest(p)
                                 for p in sorted(generated.glob("*.lean"))}
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Charon complete; Aeneas exit={status.returncode}: {destination.relative_to(ROOT)}")
    return status.returncode


if __name__ == "__main__":
    raise SystemExit(main())
