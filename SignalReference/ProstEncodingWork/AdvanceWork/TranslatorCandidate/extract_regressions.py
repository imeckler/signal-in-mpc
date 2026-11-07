#!/usr/bin/env python3
"""Extract synthetic translator regressions with the accepted unchanged Charon."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("profile", choices=["all", "calls"], default="calls", nargs="?")
    args = parser.parse_args()
    rust = ROOT / ".deps/rust-nightly-2026-08-18"
    charon = ROOT / ".deps/charon-4ad295c1bf982b5533ce7d85f4ddc889ff3127f8/charon/target/release/charon"
    destination = HERE / "Regressions"
    destination.mkdir(exist_ok=True)
    llbc = destination / ("regressions.llbc" if args.profile == "all" else "calls.llbc")
    env = os.environ.copy()
    env.update({"PATH": str(rust / "bin") + os.pathsep + env.get("PATH", ""),
                "CHARON_TOOLCHAIN_IS_IN_PATH": "1", "DYLD_LIBRARY_PATH": str(rust / "lib"),
                "LD_LIBRARY_PATH": str(rust / "lib"), "CARGO_HOME": str(ROOT / ".deps/libsignal-cargo-home"),
                "CARGO_TARGET_DIR": str(HERE / "RegressionBuild"), "RUSTFLAGS": ""})
    selected = ([] if args.profile == "all" else ["--start-from=crate::call",
                "--start-from=crate::guarded", "--start-from=crate::panic_caller"])
    command = [str(charon), "cargo", "--preset=aeneas", "--no-dedup-serialized-ast",
               "--sysroot=default", "--error-on-warnings", *selected, "--dest-file=" + str(llbc), "--",
               "--manifest-path=" + str(HERE / "RegressionRust/Cargo.toml"),
               "--lib", "--offline", "--target", "aarch64-apple-darwin"]
    with (destination / (args.profile + "-charon.log")).open("w") as log:
        result = subprocess.run(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
    assert result.returncode == 0
    contents = json.loads(llbc.read_text())
    assert not contents.get("has_errors", False)
    paths = [Path(__file__), HERE / "RegressionRust/Cargo.toml", HERE / "RegressionRust/src/lib.rs", llbc, charon]
    report = {"synthetic_translator_regression_only": True, "accepted_signal_reference": False,
              "profile": args.profile,
              "rust_version": subprocess.check_output([str(rust / "bin/rustc"), "--version"], text=True).strip(),
              "charon_version": subprocess.check_output([str(charon), "version"], text=True).strip(),
              "command": command, "source_patches": [],
              "sha256": {str(p.relative_to(ROOT)): digest(p) for p in paths}}
    (destination / (args.profile + "-inventory.json")).write_text(json.dumps(report, indent=2) + "\n")
    print("Extracted actual synthetic regression functions; not a Signal reference.")


if __name__ == "__main__":
    main()
