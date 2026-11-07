#!/usr/bin/env python3
"""Diagnostic-only actual AES mutable-Zip extraction variants."""
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

VARIANTS = {
    "MutAll": ["--monomorphize-mut=all"],
    "MutAllZip": ["--monomorphize-mut=all"],
    "MutExceptZip": ["--monomorphize-mut=except-types", "--remove-adt-clauses", "--lift-associated-types=*"],
    "MutExceptConstructor": ["--monomorphize-mut=except-types", "--remove-adt-clauses", "--lift-associated-types=*"],
    "MutExceptNext": ["--monomorphize-mut=except-types", "--remove-adt-clauses", "--lift-associated-types=*"],
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("variant", choices=VARIANTS)
    args = parser.parse_args()
    source = check_sources()
    rust = ROOT / ".deps/rust-nightly-2026-08-18"
    charon = (REFERENCE / PINS["charon"]["directory"] / "target/release/charon").resolve()
    aeneas = (REFERENCE / PINS["aeneas"]["directory"] / "aeneas").resolve()
    destination = HERE / "Artifacts" / args.variant
    destination.mkdir(parents=True, exist_ok=True)
    llbc = destination / "add_round_key.llbc"
    env = os.environ.copy()
    env.update({"PATH": str(rust / "bin") + os.pathsep + env.get("PATH", ""),
                "CHARON_TOOLCHAIN_IS_IN_PATH": "1", "DYLD_LIBRARY_PATH": str(rust / "lib"),
                "LD_LIBRARY_PATH": str(rust / "lib"),
                "CARGO_HOME": str(ROOT / ".deps/libsignal-cargo-home"),
                "CARGO_TARGET_DIR": str(HERE / "Build"),
                "CHARON_MIRI_SYSROOTS": str(REFERENCE / "PaddingWork/Unpad/Sysroot"),
                "RUST_BACKTRACE": "1",
                "RUSTFLAGS": '--cfg aes_backend="soft"'})
    versions = {"charon": subprocess.check_output([str(charon), "version"], text=True).strip(),
                "aeneas": subprocess.check_output([str(aeneas), "-version"], text=True).strip(),
                "rustc": subprocess.check_output([str(rust / "bin/rustc"), "--version"], text=True).strip()}
    if (PINS["charon"]["commit"] not in versions["charon"] or PINS["aeneas"]["release"] not in versions["aeneas"]
            or versions["rustc"] != PINS["charon"]["rustc_version"]):
        raise ValueError("Pinned tool version mismatch")
    extras = ["--include=core::ops::bit::*::bitxor_assign", *VARIANTS[args.variant]]
    if args.variant.endswith("Zip"):
        extras += ["--include=core::iter::traits::iterator::Iterator::zip",
                   "--include=core::iter::adapters::zip::*", "--include=core::iter::traits::collect::*::into_iter"]
    if args.variant.endswith("Constructor"):
        extras.append("--include=core::iter::traits::iterator::Iterator::zip")
    if args.variant.endswith("Next"):
        extras.append("--include=core::iter::adapters::zip::*::next")
    subprocess.run([str(rust / "bin/cargo"), "clean", "--package", "aes@0.9.1",
                    "--target", "aarch64-apple-darwin"], cwd=source, env=env, check=True,
                   stdout=subprocess.DEVNULL)
    command = [str(charon), "cargo", "--preset=aeneas", "--sysroot=miri",
               "--no-dedup-serialized-ast", "--error-on-warnings", *extras,
               "--start-from=crate::soft::fixslice::add_round_key", "--dest-file=" + str(llbc),
               "--", "--package", "aes@0.9.1", "--lib", "--locked", "--offline",
               "--target", "aarch64-apple-darwin"]
    with (destination / "charon.log").open("w") as log:
        result = subprocess.run(command, cwd=source, env=env, stdout=log, stderr=subprocess.STDOUT)
    report = {"accepted_reference": False, "diagnostic_only": True, "variant": args.variant,
              "versions": versions, "source_patches": [], "standard_model_changes": [],
              "charon_command": [x.replace(str(ROOT), "$WORKSPACE") for x in command],
              "charon_exit_code": result.returncode, "rustflags": env["RUSTFLAGS"],
              "sysroot_directory": "PaddingWork/Unpad/Sysroot"}
    if llbc.exists():
        report.update(inventory(llbc))
    if not result.returncode and llbc.exists() and not report["has_errors"]:
        generated = HERE / "Generated" / args.variant
        generated.mkdir(parents=True, exist_ok=True)
        command = [str(aeneas), "-backend", "lean", str(llbc), "-dest", str(REFERENCE),
                   "-subdir", "/" + str(generated.relative_to(REFERENCE)), "-split-files",
                   "-namespace", "RustCryptoAesZipDiagnostic", "-warnings-as-errors",
                   "-no-progress-bar", "-print-error-emitters"]
        with (destination / "aeneas.log").open("w") as log:
            result = subprocess.run(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
        report["aeneas_command"] = [x.replace(str(ROOT), "$WORKSPACE") for x in command]
        report["aeneas_exit_code"] = result.returncode
        report["generated_files"] = {str(p.relative_to(REFERENCE)): digest(p) for p in sorted(generated.glob("*.lean"))}
    (destination / "inventory.json").write_text(json.dumps(report, indent=2) + "\n")
    print(args.variant, "Charon", report["charon_exit_code"], "Aeneas", report.get("aeneas_exit_code", "not run"))


if __name__ == "__main__":
    main()
