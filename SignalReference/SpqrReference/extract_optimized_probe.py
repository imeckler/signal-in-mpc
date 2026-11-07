#!/usr/bin/env python3
"""Extract actual locked SPQR 1.6.0 serializer/varint with the accepted tools.

Normal Rust configuration is selected: cfg(hax) is not enabled. The source's
hax assume macros expand to unit and are not translated into proof assumptions.
The original Rust and generated Lean files are never edited by this runner.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parent
ROOT = REFERENCE.parent
spec = importlib.util.spec_from_file_location("canonical_extract", REFERENCE / "extract.py")
canonical = importlib.util.module_from_spec(spec)
spec.loader.exec_module(canonical)
digest = canonical.digest
PROFILES = {
    "varint": ["--start-from=crate::encode_varint"],
    # Rust resolution follows the type's defining path, while Charon's final
    # name matcher retains the module containing the inherent impl. Both
    # patterns are required by this pinned Charon; neither changes a body.
    "serialize": ["--start-from=crate::v1::chunked::states::*::serialize",
                  "--start-from-if-exists=crate::v1::chunked::states::serialize::*::serialize"],
}
PROFILES["serialize_closed"] = PROFILES["serialize"] + ["--include=core::slice::index"]
PROFILES["serialize_mono"] = PROFILES["serialize"] + ["--include=core::slice::index::*::index", "--monomorphize"]
PROFILES["serialize_inline"] = PROFILES["serialize"] + ["--include=core::slice::index::*::index", "--mir=optimized"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("profile", choices=PROFILES)
    parser.add_argument("--charon-only", action="store_true")
    args = parser.parse_args()
    source = canonical.check_sources()
    pins = canonical.PINS
    rust = ROOT / ".deps/rust-nightly-2026-08-18"
    charon = (REFERENCE / pins["charon"]["directory"] / "target/release/charon").resolve()
    aeneas = (REFERENCE / pins["aeneas"]["directory"] / "aeneas").resolve()
    versions = {
        "charon": subprocess.check_output([str(charon), "version"], text=True).strip(),
        "aeneas": subprocess.check_output([str(aeneas), "-version"], text=True).strip(),
        "rustc": subprocess.check_output([str(rust / "bin/rustc"), "--version"], text=True).strip(),
    }
    assert pins["charon"]["commit"] in versions["charon"]
    assert pins["aeneas"]["release"] in versions["aeneas"]
    assert pins["charon"]["rustc_version"] == versions["rustc"]
    env = os.environ.copy()
    env.update({"PATH": str(rust / "bin") + os.pathsep + env.get("PATH", ""),
                "CHARON_TOOLCHAIN_IS_IN_PATH": "1", "DYLD_LIBRARY_PATH": str(rust / "lib"),
                "LD_LIBRARY_PATH": str(rust / "lib"), "CARGO_HOME": str(ROOT / ".deps/libsignal-cargo-home"),
                "CARGO_TARGET_DIR": str(ROOT / ".deps/libsignal-charon-target"), "RUSTFLAGS": "-Cdebug-assertions=yes -Coverflow-checks=yes -Zmir-enable-passes=+Inline,+GVN,+SimplifyLocals-final"})
    spqr = ROOT / ".deps/libsignal-vendor/spqr"
    assert "06959b4708f9b7b1e94d0f8cc835f3958c077e94" in (source / "Cargo.lock").read_text()
    checksum_file = spqr / ".cargo-checksum.json"
    checksums = json.loads(checksum_file.read_text())
    for name, expected in checksums["files"].items():
        assert digest(spqr / name) == expected, name
    destination = HERE / "Artifacts" / args.profile
    destination.mkdir(parents=True, exist_ok=True)
    llbc = destination / "spqr.llbc"
    llbc.unlink(missing_ok=True)
    clean = [str(rust / "bin/cargo"), "clean", "--package", "spqr@1.6.0", "--target", "aarch64-apple-darwin"]
    subprocess.run(clean, cwd=source, env=env, check=True, stdout=subprocess.DEVNULL)
    command = [str(charon), "cargo", "--preset=aeneas", "--no-dedup-serialized-ast", "--sysroot=default",
               "--error-on-warnings", *PROFILES[args.profile], "--dest-file=" + str(llbc), "--",
               "--package", "spqr@1.6.0", "--lib", "--locked", "--offline"]
    with (destination / "charon.log").open("w") as log:
        result = subprocess.run(command, cwd=source, env=env, stdout=log, stderr=subprocess.STDOUT)
    sources = [source / "Cargo.lock", checksum_file,
               *[spqr / name for name in ("Cargo.toml", "build.rs", "src/lib.rs", "src/proto.rs",
                                          "src/v1/chunked/states.rs", "src/v1/chunked/states/serialize.rs",
                                          "src/encoding.rs")],
               *[ROOT / ".deps/libsignal-vendor" / name for name in
                 ("hax-lib-0.3.7/src/lib.rs", "hax-lib-0.3.7/src/dummy.rs",
                  "hax-lib-macros-0.3.7/src/lib.rs", "hax-lib-macros-0.3.7/src/dummy.rs")]]
    report = {"candidate_only": True, "accepted_reference": False, "source_patches": [],
              "profile": args.profile, "spqr_commit": "06959b4708f9b7b1e94d0f8cc835f3958c077e94",
              "versions": versions, "script_sha256": digest(Path(__file__)),
              "source_sha256": {str(p.relative_to(ROOT)): digest(p) for p in sources},
              "all_vendor_source_checksums_verified": len(checksums["files"]),
              "hax_cfg_enabled": False,
              "rustflags": env["RUSTFLAGS"],
              "hax_assume_semantics": "Actual cfg(not(hax)) dummy macro expands to unit; no proof assumption introduced.",
              "charon_command": [x.replace(str(ROOT), "$WORKSPACE") for x in command],
              "charon_exit_code": result.returncode}
    if llbc.exists():
        report.update(canonical.inventory(llbc))
    target = destination / "inventory.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    if result.returncode or not llbc.exists() or report["has_errors"] or not report["counts"]["ordered_decls"]:
        print("Incomplete Charon extraction; see " + str(target.relative_to(ROOT)))
        return 1
    if args.charon_only:
        return 0
    generated = HERE / "Generated" / args.profile
    generated.mkdir(parents=True, exist_ok=True)
    for old in generated.glob("*.lean"):
        old.unlink()
    command = [str(aeneas), "-backend", "lean", str(llbc), "-dest", str(REFERENCE),
               "-subdir", "/SpqrReference/Generated/" + args.profile, "-split-files", "-namespace", "SpqrReference",
               "-warnings-as-errors", "-no-progress-bar"]
    with (destination / "aeneas.log").open("w") as log:
        result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    report.update({"aeneas_exit_code": result.returncode,
                   "aeneas_command": [x.replace(str(ROOT), "$WORKSPACE") for x in command],
                   "generated_files": {str(p.relative_to(REFERENCE)): digest(p) for p in generated.glob("*.lean")},
                   "remaining_external_templates": [p.name for p in generated.glob("*_Template.lean")]})
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Actual SPQR " + args.profile + ": Aeneas exit " + str(result.returncode))
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
