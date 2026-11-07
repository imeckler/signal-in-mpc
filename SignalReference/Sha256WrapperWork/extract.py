#!/usr/bin/env python3
"""Isolated actual RustCrypto SHA256 wrapper extraction; no source/model patches."""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tomllib

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parent
ROOT = REFERENCE.parent
spec = importlib.util.spec_from_file_location("canonical_extract", REFERENCE / "extract.py")
canonical = importlib.util.module_from_spec(spec)
spec.loader.exec_module(canonical)
digest = canonical.digest
PROFILES = {
    "core_new": {"start": "{impl digest::block_api::VariableOutputCore for crate::block_api::Sha256VarCore}::new", "extra": []},
    "core_update": {"start": "{impl digest::block_api::UpdateCore for crate::block_api::Sha256VarCore}::update_blocks", "extra": []},
    "core_finalize": {"start": "{impl digest::block_api::VariableOutputCore for crate::block_api::Sha256VarCore}::finalize_variable_core", "extra": []},
    "buffer_update": {"start": "{impl digest::Update for crate::Sha256}::update", "extra": ["--include=digest", "--include=block_buffer", "--include=hybrid_array"]},
    "buffer_finalize": {"start": "{impl digest::FixedOutput for crate::Sha256}::finalize_into", "extra": ["--include=digest", "--include=block_buffer", "--include=hybrid_array"]},
}
PROFILES["core_new_scoped"] = {**PROFILES["core_new"], "extra": ["--exclude=hybrid_array::traits::ArraySize"]}
PROFILES["core_update_scoped"] = {**PROFILES["core_update"], "extra": ["--exclude=hybrid_array::traits::ArraySize"]}
PROFILES["core_finalize_scoped"] = {**PROFILES["core_finalize"], "extra": ["--exclude=hybrid_array::traits::ArraySize"]}
for operation in ("new", "update", "finalize"):
    source_profile = PROFILES["core_" + operation + "_scoped"]
    implementation = "crate::block_api::*::" + source_profile["start"].rsplit("::", 1)[1]
    PROFILES["core_" + operation + "_closed"] = {
        **source_profile,
        "extra": [*source_profile["extra"], "--start-from-if-exists=" + implementation],
    }
DEPENDENCIES = {"sha2": "0.11.0", "digest": "0.11.3", "block-buffer": "0.12.1",
                "crypto-common": "0.2.2", "hybrid-array": "0.4.13"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("profile", choices=PROFILES)
    parser.add_argument("--charon-only", action="store_true")
    args = parser.parse_args()
    source = canonical.check_sources()
    lock = tomllib.loads((source / "Cargo.lock").read_text())
    source_files = {str((source / "Cargo.lock").relative_to(ROOT)): digest(source / "Cargo.lock")}
    dependencies = {}
    for name, version in DEPENDENCIES.items():
        package = next(p for p in lock["package"] if p["name"] == name and p["version"] == version)
        directory = ROOT / ".deps/libsignal-vendor" / (name + "-" + version)
        checksum = directory / ".cargo-checksum.json"
        checksums = json.loads(checksum.read_text())
        assert checksums["package"] == package["checksum"] and checksums["files"]
        for filename, expected in checksums["files"].items():
            path = directory / filename
            assert digest(path) == expected, path
            source_files[str(path.relative_to(ROOT))] = expected
        source_files[str(checksum.relative_to(ROOT))] = digest(checksum)
        dependencies[name] = {"version": version, "package_sha256": package["checksum"],
                              "source_files_checked": len(checksums["files"])}
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
    rustflags = '--cfg sha2_256_backend="soft" --cfg sha2_backend_soft="compact"'
    env = os.environ.copy()
    env.update({"PATH": str(rust / "bin") + os.pathsep + env.get("PATH", ""),
                "CHARON_TOOLCHAIN_IS_IN_PATH": "1", "DYLD_LIBRARY_PATH": str(rust / "lib"),
                "LD_LIBRARY_PATH": str(rust / "lib"), "CARGO_HOME": str(ROOT / ".deps/libsignal-cargo-home"),
                "CARGO_TARGET_DIR": str(ROOT / ".deps/libsignal-charon-target"), "RUSTFLAGS": rustflags})
    destination = HERE / "Artifacts" / args.profile
    destination.mkdir(parents=True, exist_ok=True)
    llbc = destination / "sha_wrapper.llbc"
    llbc.unlink(missing_ok=True)
    subprocess.run([str(rust / "bin/cargo"), "clean", "--package", "sha2@0.11.0", "--target", "aarch64-apple-darwin"],
                   cwd=source, env=env, check=True, stdout=subprocess.DEVNULL)
    profile = PROFILES[args.profile]
    command = [str(charon), "cargo", "--preset=aeneas", "--no-dedup-serialized-ast", "--sysroot=default",
               "--error-on-warnings", "--start-from=" + profile["start"], *profile["extra"],
               "--dest-file=" + str(llbc), "--", "--package", "sha2@0.11.0", "--lib", "--locked", "--offline"]
    with (destination / "charon.log").open("w") as log:
        result = subprocess.run(command, cwd=source, env=env, stdout=log, stderr=subprocess.STDOUT)
    report = {"candidate_only": True, "accepted_reference": False, "source_patches": [], "custom_models": [],
              "profile": args.profile, "versions": versions, "rustflags": rustflags,
              "script_sha256": digest(Path(__file__)), "source_sha256": source_files, "dependencies": dependencies,
              "charon_command": [x.replace(str(ROOT), "$WORKSPACE") for x in command], "charon_exit_code": result.returncode}
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
               "-subdir", "/Sha256WrapperWork/Generated/" + args.profile, "-split-files", "-namespace", "Sha256Wrapper",
               "-warnings-as-errors", "-no-progress-bar"]
    with (destination / "aeneas.log").open("w") as log:
        result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    report.update({"aeneas_exit_code": result.returncode,
                   "aeneas_command": [x.replace(str(ROOT), "$WORKSPACE") for x in command],
                   "generated_files": {str(p.relative_to(REFERENCE)): digest(p) for p in generated.glob("*.lean")},
                   "remaining_external_templates": [p.name for p in generated.glob("*_Template.lean")]})
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Actual SHA wrapper " + args.profile + ": Aeneas exit " + str(result.returncode))
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
