#!/usr/bin/env python3
"""Isolated actual-Rust unpadding extraction; never changes accepted padding."""

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parents[1]
ROOT = REFERENCE.parent
sys.path.insert(0, str(REFERENCE))
from extract import PINS, check_sources, digest, inventory

BASE = ["--exclude=crate::Padding::pad", "--exclude=crate::Padding::unpad",
        "--exclude=crate::Padding::pad_detached", "--exclude=crate::Padding::unpad_blocks",
        "--exclude=crate::*::raw_pad", "--exclude=hybrid_array::traits::ArraySize"]
VARIANTS = {
    "Raw": [*BASE],
    "RawIterator": [*BASE, "--include=core::iter::traits::iterator::Iterator::any"],
    "RawSliceIterator": [*BASE, "--include=core::slice::iter::*::any"],
    "RawMono": [*BASE, "--monomorphize"],
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("variant", choices=VARIANTS)
    parser.add_argument("--full-mir", action="store_true")
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
        raise ValueError(f"Wrong tool versions: {versions}")
    tag = args.variant + ("FullMir" if args.full_mir else "")
    destination = HERE / "Artifacts" / tag
    destination.mkdir(parents=True, exist_ok=True)
    llbc = destination / "pkcs7_unpad.llbc"
    env = os.environ.copy()
    env.update({"PATH": str(rust / "bin") + os.pathsep + env.get("PATH", ""),
                "CHARON_TOOLCHAIN_IS_IN_PATH": "1", "DYLD_LIBRARY_PATH": str(rust / "lib"),
                "LD_LIBRARY_PATH": str(rust / "lib"),
                "CARGO_HOME": str(ROOT / ".deps/libsignal-cargo-home"),
                "CARGO_TARGET_DIR": str(HERE / ("BuildFullMir" if args.full_mir else "Build"))})
    if args.full_mir:
        if not (HERE / "Sysroot/lib/rustlib/aarch64-apple-darwin").is_dir():
            raise ValueError("Build the isolated full-MIR sysroot first")
        env["CHARON_MIRI_SYSROOTS"] = str(HERE / "Sysroot")
    subprocess.run([str(rust / "bin/cargo"), "clean", "--package", "block-padding@0.4.2",
                    "--target", "aarch64-apple-darwin"], cwd=source, env=env, check=True,
                   stdout=subprocess.DEVNULL)
    command = [str(charon), "cargo", "--preset=aeneas", "--sysroot=" + ("miri" if args.full_mir else "default"), "--error-on-warnings",
               "--start-from={crate::Padding for crate::Pkcs7}::raw_unpad",
               "--start-from-if-exists=crate::*::raw_unpad", *VARIANTS[args.variant],
               "--dest-file=" + str(llbc), "--", "--package", "block-padding@0.4.2",
               "--lib", "--locked", "--offline", "--target", "aarch64-apple-darwin"]
    llbc.unlink(missing_ok=True)
    with (destination / "charon.log").open("w") as log:
        status = subprocess.run(command, cwd=source, env=env, stdout=log, stderr=subprocess.STDOUT)
    report = {"candidate_reference": True, "accepted_reference": False, "versions": versions,
              "source_patches": [], "variant": args.variant, "full_mir_sysroot": args.full_mir,
              "charon_command": [x.replace(str(ROOT), "$WORKSPACE") for x in command],
              "charon_exit_code": status.returncode}
    if llbc.exists():
        report.update(inventory(llbc))
    report_path = destination / "inventory.json"
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    if status.returncode or not llbc.exists() or report["has_errors"]:
        print(f"Incomplete Charon extraction: {destination.relative_to(ROOT)}")
        return 1
    generated = HERE / "Generated" / tag
    generated.mkdir(parents=True, exist_ok=True)
    for previous in generated.glob("*.lean"):
        previous.unlink()
    command = [str(aeneas), "-backend", "lean", str(llbc), "-dest", str(REFERENCE),
               "-subdir", "/PaddingWork/Unpad/Generated/" + tag, "-split-files",
               "-namespace", "RustCryptoUnpadding", "-warnings-as-errors", "-no-progress-bar"]
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
