#!/usr/bin/env python3
"""Isolated extraction experiments for the locked RustCrypto PKCS7 leaf."""

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
from extract import check_sources, digest, inventory

SCOPED = ["--exclude=crate::Padding::pad", "--exclude=crate::Padding::unpad",
          "--exclude=crate::Padding::pad_detached", "--exclude=crate::Padding::unpad_blocks",
          "--exclude=crate::*::raw_unpad", "--exclude=crate::*::unpad"]
VARIANTS = {
    "ExcludeArraySize": [*SCOPED, "--exclude=hybrid_array::traits::ArraySize"],
    "ExcludeArray": [*SCOPED, "--exclude=hybrid_array"],
    "ExcludeTrait": ["--exclude=crate::Padding"],
    "Mono": ["--monomorphize"],
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("variant", choices=VARIANTS)
    parser.add_argument("--candidate", action="store_true")
    args = parser.parse_args()
    source = check_sources()
    pin = json.loads((REFERENCE / "pins.json").read_text())
    if args.candidate:
        candidate = json.loads((REFERENCE / "candidate-pins.json").read_text())
        tool = (REFERENCE / candidate["aeneas_directory"]).resolve()
        rust = (REFERENCE / candidate["rust_directory"]).resolve()
        charon, aeneas = tool / "charon", tool / "aeneas"
        expected = candidate["versions"]
    else:
        rust = ROOT / ".deps/rust-nightly-2026-08-18"
        charon = (REFERENCE / pin["charon"]["directory"] / "target/release/charon").resolve()
        aeneas = (REFERENCE / pin["aeneas"]["directory"] / "aeneas").resolve()
        expected = {"charon": f'{pin["charon"]["version"]} ({pin["charon"]["commit"]})',
                    "aeneas": "aeneas " + pin["aeneas"]["release"],
                    "rustc": pin["charon"]["rustc_version"]}
    actual = {"charon": subprocess.check_output([str(charon), "version"], text=True).strip(),
              "aeneas": subprocess.check_output([str(aeneas), "-version"], text=True).strip(),
              "rustc": subprocess.check_output([str(rust / "bin/rustc"), "--version"], text=True).strip()}
    if actual != expected:
        raise ValueError(f"Wrong tool versions: {actual}")
    tag = args.variant + ("Candidate" if args.candidate else "")
    destination = HERE / "Artifacts" / tag
    destination.mkdir(parents=True, exist_ok=True)
    llbc = destination / "pkcs7.llbc"
    env = os.environ.copy()
    env.update({"PATH": str(rust / "bin") + os.pathsep + env.get("PATH", ""),
                "CHARON_TOOLCHAIN_IS_IN_PATH": "1", "DYLD_LIBRARY_PATH": str(rust / "lib"),
                "LD_LIBRARY_PATH": str(rust / "lib"),
                "CARGO_HOME": str(ROOT / ".deps/libsignal-cargo-home"),
                "CARGO_TARGET_DIR": str(HERE / "Build" / ("Candidate" if args.candidate else "Accepted"))})
    subprocess.run([str(rust / "bin/cargo"), "clean", "--package", "block-padding@0.4.2",
                    "--target", "aarch64-apple-darwin"], cwd=source, env=env, check=True,
                   stdout=subprocess.DEVNULL)
    command = [str(charon), "cargo", "--preset=aeneas", "--sysroot=default", "--error-on-warnings",
               "--start-from={crate::Padding for crate::Pkcs7}::raw_pad",
               "--start-from-if-exists=crate::*::raw_pad", *VARIANTS[args.variant],
               "--dest-file=" + str(llbc), "--", "--package", "block-padding@0.4.2",
               "--lib", "--locked", "--offline", "--target", "aarch64-apple-darwin"]
    llbc.unlink(missing_ok=True)
    with (destination / "charon.log").open("w") as log:
        status = subprocess.run(command, cwd=source, env=env, stdout=log, stderr=subprocess.STDOUT)
    report = {"candidate_reference": True, "accepted_reference": False,
              "versions": actual, "source_patches": [], "variant": args.variant,
              "charon_command": [x.replace(str(ROOT), "$WORKSPACE") for x in command],
              "charon_exit_code": status.returncode,
              "block_padding_source_sha256": digest(ROOT / ".deps/libsignal-vendor/block-padding-0.4.2/src/lib.rs")}
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
               "-subdir", "/PaddingWork/Generated/" + tag, "-split-files",
               "-namespace", "RustCryptoPadding", "-warnings-as-errors", "-no-progress-bar"]
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
