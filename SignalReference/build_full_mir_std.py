#!/usr/bin/env python3
"""Build the official matching Rust core MIR in an isolated workspace cache."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[1]
HERE = ROOT / ".deps/full-mir-std-2026-08-18"
HERE.mkdir(exist_ok=True)
RUST = ROOT / ".deps/rust-nightly-2026-08-18"
MIRI_HASH = "912904e20c37ffe461264ac7c005bc56b778d7a58fcbb29deed3445912283d21"
RUST_SOURCE_HASH = "f8b984f0f9a4f542a73c85be1bc379fe88455c5e96f70bd19052511d0195f5e4"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--miri-archive', type=Path, default=ROOT / 'SignalReference/PaddingWork/Unpad/miri-nightly-2026-08-18.tar.xz')
    args = parser.parse_args()
    archive = args.miri_archive
    if hashlib.sha256(archive.read_bytes()).hexdigest() != MIRI_HASH:
        raise ValueError("Official Miri archive differs")
    rust_archive = ROOT / ".deps/rust-src-nightly-2026-08-18.tar.xz"
    if hashlib.sha256(rust_archive.read_bytes()).hexdigest() != RUST_SOURCE_HASH:
        raise ValueError("Official matching Rust source archive differs")
    binary = HERE / "Miri/bin"
    binary.mkdir(parents=True, exist_ok=True)
    with tarfile.open(archive) as bundle:
        for member in bundle:
            if member.name.endswith(("/bin/miri", "/bin/cargo-miri")):
                path = binary / member.name.rsplit("/", 1)[1]
                path.write_bytes(bundle.extractfile(member).read())
                path.chmod(0o755)
    cargo_home = HERE / "CargoHome"
    cargo_home.mkdir(exist_ok=True)
    rust_source = RUST / "lib/rustlib/src/rust/library"
    (cargo_home / "config.toml").write_text(
        '[net]\noffline = true\n[source.crates-io]\nreplace-with = "vendored-sources"\n'
        '[source.vendored-sources]\ndirectory = ' + json.dumps(str(rust_source / "vendor")) + '\n')
    env = os.environ.copy()
    env.update({"PATH": str(binary) + os.pathsep + str(RUST / "bin") + os.pathsep + env.get("PATH", ""),
                "CARGO": str(RUST / "bin/cargo"), "RUSTC": str(RUST / "bin/rustc"),
                "DYLD_LIBRARY_PATH": str(RUST / "lib"), "CARGO_HOME": str(cargo_home),
                "MIRI_HOST_SYSROOT": str(RUST), "MIRI_SYSROOT": str(HERE / "Sysroot"),
                "MIRI_LIB_SRC": str(rust_source), "CARGO_NET_OFFLINE": "true"})
    command = [str(binary / "cargo-miri"), "miri", "setup", "--target=aarch64-apple-darwin", "--print-sysroot"]
    with (HERE / "sysroot-build.log").open("w") as log:
        status = subprocess.run(command, cwd=HERE, env=env, stdout=log, stderr=subprocess.STDOUT)
    print(f"Miri setup exit={status.returncode}; {HERE / 'sysroot-build.log'}")
    if status.returncode == 0:
        source_files = ["core/src/slice/iter/macros.rs", "core/src/iter/traits/iterator.rs",
                        "core/src/slice/iter.rs", "core/src/result.rs", "core/src/option.rs",
                        "core/src/iter/range.rs", "core/Cargo.toml", "std/Cargo.toml", "Cargo.lock", "Cargo.toml"]
        source_hashes = {}
        with tarfile.open(rust_archive) as bundle:
            names = bundle.getnames()
            for name in source_files:
                member = next(n for n in names if n.endswith("/library/" + name))
                data = (rust_source / name).read_bytes()
                if data != bundle.extractfile(member).read():
                    raise ValueError(f"Rust source differs from official archive: {name}")
                source_hashes[name] = hashlib.sha256(data).hexdigest()
        report = {
            "miri_archive_sha256": MIRI_HASH, "rust_source_archive_sha256": RUST_SOURCE_HASH,
            "rust_commit": "8fa1c96cfd489e4c27654c144ae871ce2c4db6c6",
            "source_patches": [], "target": "aarch64-apple-darwin", "no_std": False,
            "command": [x.replace(str(ROOT), "$WORKSPACE") for x in command],
            "source_directory": str(rust_source.relative_to(ROOT)),
            "sysroot_directory": str((HERE / "Sysroot").relative_to(ROOT)),
            "sysroot_source_files_sha256": source_hashes,
            "sysroot_artifact_sha256": {str(p.relative_to(HERE / "Sysroot")): hashlib.sha256(p.read_bytes()).hexdigest()
                for p in sorted((HERE / "Sysroot/lib/rustlib/aarch64-apple-darwin/lib").iterdir())
                if p.suffix in (".rmeta", ".rlib")},
            "charon_usage": {"sysroot_argument": "--sysroot=miri", "environment":
                {"CHARON_MIRI_SYSROOTS": "$WORKSPACE/.deps/full-mir-std-2026-08-18/Sysroot"}},
            "builder_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "note": "Full MIR prevents prebuilt optimized std MIR from inlining next() into raw-pointer operations.",
        }
        (ROOT / "SignalReference/Extraction/full-mir-std-sysroot.json").write_text(json.dumps(report, indent=2) + "\n")
    return status.returncode


if __name__ == "__main__":
    raise SystemExit(main())
