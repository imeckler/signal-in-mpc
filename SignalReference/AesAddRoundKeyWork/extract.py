#!/usr/bin/env python3
"""Extract actual unchanged RustCrypto AES add_round_key."""

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parent
ROOT = REFERENCE.parent
sys.path.insert(0, str(REFERENCE))
from extract import PINS, check_sources, digest, inventory


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--charon-only", action="store_true")
    parser.add_argument("--variant", choices=("Base", "IncludeXor", "Mono", "MonoZip", "Mut", "MutZip"), default="Base")
    args = parser.parse_args()
    source = check_sources()
    rust = ROOT / ".deps/rust-nightly-2026-08-18"
    charon = (REFERENCE / PINS["charon"]["directory"] / "target/release/charon").resolve()
    aeneas = (REFERENCE / PINS["aeneas"]["directory"] / "aeneas").resolve()
    versions = {"charon": subprocess.check_output([str(charon), "version"], text=True).strip(),
                "aeneas": subprocess.check_output([str(aeneas), "-version"], text=True).strip(),
                "rustc": subprocess.check_output([str(rust / "bin/rustc"), "--version"], text=True).strip()}
    if (PINS["charon"]["commit"] not in versions["charon"] or
            PINS["aeneas"]["release"] not in versions["aeneas"] or
            versions["rustc"] != PINS["charon"]["rustc_version"]):
        raise ValueError("Tool versions differ")
    destination = (HERE / "Artifacts") if args.variant == "Base" else (HERE / "Artifacts" / args.variant)
    destination.mkdir(parents=True, exist_ok=True)
    llbc = destination / "add_round_key.llbc"
    env = os.environ.copy()
    env.update({"PATH": str(rust / "bin") + os.pathsep + env.get("PATH", ""),
                "CHARON_TOOLCHAIN_IS_IN_PATH": "1", "DYLD_LIBRARY_PATH": str(rust / "lib"),
                "LD_LIBRARY_PATH": str(rust / "lib"),
                "CARGO_HOME": str(ROOT / ".deps/libsignal-cargo-home"),
                "CARGO_TARGET_DIR": str(HERE / "Build" / args.variant), "RUSTFLAGS": '--cfg aes_backend="soft"'})
    extras = []
    if args.variant != "Base":
        env["CHARON_MIRI_SYSROOTS"] = str(REFERENCE / "PaddingWork/Unpad/Sysroot")
        extras.append("--include=core::ops::bit::*::bitxor_assign")
    if args.variant.startswith("Mono"):
        extras.append("--monomorphize")
    if args.variant.startswith("Mut"):
        extras += ["--monomorphize-mut=except-types", "--remove-adt-clauses", "--lift-associated-types=*"]
    if args.variant.endswith("Zip"):
        extras += ["--include=core::iter::traits::iterator::Iterator::zip",
                   "--include=core::iter::adapters::zip::*", "--include=core::iter::traits::collect::*::into_iter"]
    subprocess.run([str(rust / "bin/cargo"), "clean", "--package", "aes@0.9.1",
                    "--target", "aarch64-apple-darwin"], cwd=source, env=env, check=True,
                   stdout=subprocess.DEVNULL)
    command = [str(charon), "cargo", "--preset=aeneas", "--sysroot=" + ("default" if args.variant == "Base" else "miri"),
               "--no-dedup-serialized-ast", "--error-on-warnings",
               *extras,
               "--start-from=crate::soft::fixslice::add_round_key", "--dest-file=" + str(llbc),
               "--", "--package", "aes@0.9.1", "--lib", "--locked", "--offline",
               "--target", "aarch64-apple-darwin"]
    llbc.unlink(missing_ok=True)
    with (destination / "charon.log").open("w") as log:
        status = subprocess.run(command, cwd=source, env=env, stdout=log, stderr=subprocess.STDOUT)
    report = {"accepted_reference": False, "versions": versions, "source_patches": [],
              "charon_command": [x.replace(str(ROOT), "$WORKSPACE") for x in command],
              "charon_exit_code": status.returncode, "rustflags": env["RUSTFLAGS"], "variant": args.variant}
    if llbc.exists():
        report.update(inventory(llbc))
    report_path = destination / "inventory.json"
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    if status.returncode or not llbc.exists() or report["has_errors"]:
        print(f"Incomplete Charon extraction: {destination.relative_to(ROOT)}")
        return 1
    if args.charon_only:
        print(f"Charon complete: {destination.relative_to(ROOT)}")
        return 0
    generated = (HERE / "Generated") if args.variant == "Base" else (HERE / "Generated" / args.variant)
    generated.mkdir(parents=True, exist_ok=True)
    for previous in generated.glob("*.lean"):
        previous.unlink()
    command = [str(aeneas), "-backend", "lean", str(llbc), "-dest", str(REFERENCE),
               "-subdir", "/" + str(generated.relative_to(REFERENCE)), "-split-files",
               "-namespace", "RustCryptoAesAddRoundKey", "-warnings-as-errors", "-no-progress-bar"]
    with (destination / "aeneas.log").open("w") as log:
        status = subprocess.run(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
    report["aeneas_command"] = [part.replace(str(ROOT), "$WORKSPACE") for part in command]
    report["aeneas_exit_code"] = status.returncode
    report["generated_files"] = {str(p.relative_to(REFERENCE)): digest(p) for p in sorted(generated.glob("*.lean"))}
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Charon complete; Aeneas exit={status.returncode}: {destination.relative_to(ROOT)}")
    return status.returncode


if __name__ == "__main__":
    raise SystemExit(main())
