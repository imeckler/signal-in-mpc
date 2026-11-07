#!/usr/bin/env python3
"""Isolated extraction of the actual bytes &[u8] advance operation."""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parents[1]
ROOT = REFERENCE.parent
spec = importlib.util.spec_from_file_location("prost_extraction", HERE.parent / "extract.py")
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)
digest = base.digest
PINS = base.PINS
SOURCE_HASHES = {**base.SOURCE_HASHES,
    ".deps/libsignal-vendor/bytes-1.12.0/src/lib.rs": "053fc1b7e028cd1ccab019ea695f3e620129ef26a5b3f80a747b402a9871dfbf",
    ".deps/libsignal-vendor/bytes-1.12.0/src/buf/buf_impl.rs": "f1095872bba7c9d5170207750f4ebe4fa61c4e35a282569491c2ee8ea2dc6714"}
PROFILES = {
    "Slice": ["--start-from={crate::buf::buf_impl::Buf for &Slice<u8>}::advance"],
    "SliceModule": ["--start-from=crate::buf::buf_impl", "--opaque=crate",
                    "--include={crate::buf::buf_impl::Buf for &Slice<_>}::advance"],
    "SliceModulePanic": ["--start-from=crate::buf::buf_impl", "--opaque=crate",
                    "--include={crate::buf::buf_impl::Buf for &Slice<_>}::advance",
                    "--include=crate::panic_advance"],
    "SliceImplsPanic": ["--start-from={crate::buf::buf_impl::Buf for _}::advance",
                    "--opaque=crate",
                    "--include={crate::buf::buf_impl::Buf for &Slice<_>}::advance",
                    "--include=crate::panic_advance"],
    "SliceImplsClosed": ["--start-from={crate::buf::buf_impl::Buf for _}::advance",
                    "--opaque=crate",
                    "--include={crate::buf::buf_impl::Buf for &Slice<_>}::advance",
                    "--include=crate::panic_advance", "--include=crate::TryGetError"],
}
PROFILES["SliceInlinePanic"] = [*PROFILES["SliceImplsClosed"], "--mir=optimized"]
RUSTFLAGS = {"SliceInlinePanic": "-Zmir-enable-passes=+Inline -Zinline-mir-threshold=100000 "
             "-Zinline-mir-hint-threshold=100000 -Zinline-mir-preserve-debug=no "
             "-Cdebug-assertions=yes -Coverflow-checks=yes"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("profile", choices=PROFILES)
    args = parser.parse_args()
    source = base.canonical.check_sources()
    for filename, expected in SOURCE_HASHES.items():
        if digest(ROOT / filename) != expected:
            raise ValueError(f"Pinned source changed: {filename}")
    rust = ROOT / ".deps/rust-nightly-2026-08-18"
    charon = (REFERENCE / PINS["charon"]["directory"] / "target/release/charon").resolve()
    aeneas = (REFERENCE / PINS["aeneas"]["directory"] / "aeneas").resolve()
    versions = {"charon": subprocess.check_output([str(charon), "version"], text=True).strip(),
                "aeneas": subprocess.check_output([str(aeneas), "-version"], text=True).strip(),
                "rustc": subprocess.check_output([str(rust / "bin/rustc"), "--version"], text=True).strip()}
    if (PINS["charon"]["commit"] not in versions["charon"] or
            PINS["aeneas"]["release"] not in versions["aeneas"] or
            PINS["charon"]["rustc_version"] != versions["rustc"]):
        raise ValueError("The actual extraction toolchain differs from its pins")
    destination = HERE / "Artifacts" / args.profile
    destination.mkdir(parents=True, exist_ok=True)
    llbc = destination / "slice_advance.llbc"
    env = os.environ.copy()
    env.update({"PATH": str(rust / "bin") + os.pathsep + env.get("PATH", ""),
                "CHARON_TOOLCHAIN_IS_IN_PATH": "1", "DYLD_LIBRARY_PATH": str(rust / "lib"),
                "LD_LIBRARY_PATH": str(rust / "lib"), "CARGO_HOME": str(ROOT / ".deps/libsignal-cargo-home"),
                "CARGO_TARGET_DIR": str(HERE / "Build"), "RUSTFLAGS": RUSTFLAGS.get(args.profile, "")})
    subprocess.run([str(rust / "bin/cargo"), "clean", "--package", "bytes@1.12.0",
                    "--target", "aarch64-apple-darwin"], cwd=source, env=env, check=True,
                   stdout=subprocess.DEVNULL)
    command = [str(charon), "cargo", "--preset=aeneas", "--no-dedup-serialized-ast",
               "--sysroot=default", "--error-on-warnings",
               *PROFILES[args.profile], "--dest-file=" + str(llbc), "--",
               "--package", "bytes@1.12.0", "--lib", "--locked", "--offline", "--target", "aarch64-apple-darwin"]
    llbc.unlink(missing_ok=True)
    with (destination / "charon.log").open("w") as log:
        status = subprocess.run(command, cwd=source, env=env, stdout=log, stderr=subprocess.STDOUT)
    report = {"candidate_reference": True, "accepted_reference": False, "versions": versions,
              "source_patches": [], "source_sha256": SOURCE_HASHES,
              "rustflags": env["RUSTFLAGS"],
              "charon_command": [x.replace(str(ROOT), "$WORKSPACE") for x in command],
              "charon_exit_code": status.returncode, "script_sha256": digest(Path(__file__))}
    if llbc.exists():
        report.update(base.canonical.inventory(llbc))
        declarations = json.loads(llbc.read_text())["translated"]["fun_decls"]
        report["selected_advance_has_body"] = any(f and f["body"] != "Opaque" and
            f["item_meta"]["name"][-1] == {"Ident": ["advance", 0]} for f in declarations)
    report_path = destination / "inventory.json"
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    if status.returncode or not llbc.exists() or report["has_errors"] or not report["selected_advance_has_body"]:
        print(f"Incomplete actual advance extraction: {destination.relative_to(ROOT)}")
        return 1
    generated = HERE / "Generated" / args.profile
    generated.mkdir(parents=True, exist_ok=True)
    for path in generated.glob("*.lean"):
        path.unlink()
    command = [str(aeneas), "-backend", "lean", str(llbc), "-dest", str(REFERENCE),
               "-subdir", "/ProstEncodingWork/AdvanceWork/Generated/" + args.profile,
               "-split-files", "-namespace", "BytesSliceAdvance", "-warnings-as-errors", "-no-progress-bar"]
    with (destination / "aeneas.log").open("w") as log:
        status = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    report.update({"aeneas_exit_code": status.returncode,
                   "aeneas_command": [x.replace(str(ROOT), "$WORKSPACE") for x in command],
                   "generated_files": {str(p.relative_to(REFERENCE)): digest(p) for p in generated.glob("*.lean")},
                   "remaining_external_templates": [p.name for p in generated.glob("*_Template.lean")]})
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Actual advance: Aeneas exit{status.returncode}; templates {report['remaining_external_templates']}")
    return status.returncode


if __name__ == "__main__":
    raise SystemExit(main())
