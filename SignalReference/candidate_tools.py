#!/usr/bin/env python3
"""Try a separately pinned extraction stack; never replace accepted references."""

import argparse
import json
import os
from pathlib import Path
import subprocess

from extract import HERE, ROOT, PROFILES, check_sources, digest, inventory


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("profile", choices=PROFILES)
    parser.add_argument("--filter-unused-trait-methods", action="store_true")
    parser.add_argument("--resugar-drops", action="store_true")
    args = parser.parse_args()
    pin = json.loads((HERE / "candidate-pins.json").read_text())
    for name, expected in pin["download_sha256"].items():
        if digest(ROOT / ".deps" / name) != expected:
            raise ValueError(f"candidate archive differs: {name}")
    package = PROFILES[args.profile]
    source = check_sources()
    tool = (HERE / pin["aeneas_directory"]).resolve()
    rust = (HERE / pin["rust_directory"]).resolve()
    actual = {
        "aeneas": subprocess.check_output([str(tool / "aeneas"), "-version"], text=True).strip(),
        "charon": subprocess.check_output([str(tool / "charon"), "version"], text=True).strip(),
        "rustc": subprocess.check_output([str(rust / "bin/rustc"), "--version"], text=True).strip(),
    }
    if actual != pin["versions"]:
        raise ValueError(f"candidate version mismatch: {actual}")
    if (tool / "backends/lean/lean-toolchain").read_text().strip() != pin["lean_toolchain"]:
        raise ValueError("candidate Lean version differs")
    suffix = "-filtered" if args.filter_unused_trait_methods else ""
    if args.resugar_drops:
        suffix += "-resugared"
    destination = HERE / "Extraction/Candidates/2026-09-30" / (args.profile + suffix)
    destination.mkdir(parents=True, exist_ok=True)
    llbc = destination / (args.profile + ".llbc")
    env = os.environ.copy()
    env.update({"PATH": str(rust / "bin") + os.pathsep + env.get("PATH", ""),
                "CHARON_TOOLCHAIN_IS_IN_PATH": "1", "DYLD_LIBRARY_PATH": str(rust / "lib"),
                "LD_LIBRARY_PATH": str(rust / "lib"),
                "CARGO_HOME": str(ROOT / ".deps/libsignal-cargo-home"),
                "CARGO_TARGET_DIR": str(ROOT / ".deps/libsignal-charon-2026-09-30-target")})
    if "rustflags" in package:
        env["RUSTFLAGS"] = package["rustflags"]
    target = package.get("target", "aarch64-apple-darwin")
    if "@" in package["package"]:
        subprocess.run([str(rust / "bin/cargo"), "clean", "--package", package["package"],
                        "--target", target], cwd=source, env=env, check=True,
                       stdout=subprocess.DEVNULL)
    command = [str(tool / "charon"), "cargo", "--preset=aeneas", "--sysroot=default",
               "--error-on-warnings", "--start-from=" + ",".join(package["starts"]),
               *package["extra"],
               *(["--resugar-drops", "--detect-drop-flags"] if args.resugar_drops else []),
               "--dest-file=" + str(llbc), "--",
               "--package", package["package"], "--lib", "--locked", "--offline",
               "--target", target]
    llbc.unlink(missing_ok=True)
    with (destination / "charon.log").open("w") as log:
        result = subprocess.run(command, cwd=source, env=env, stdout=log, stderr=subprocess.STDOUT)
    audit = {"candidate_only": True, "accepted_reference": False, "versions": actual,
             "tool_pins": "candidate-pins.json", "profile": args.profile,
             "charon_command": [x.replace(str(ROOT), "$WORKSPACE") for x in command],
             "charon_exit_code": result.returncode, "rustflags": env.get("RUSTFLAGS", ""),
             "target": target, "trait_method_filter_requested": args.filter_unused_trait_methods}
    audit["resugar_drops_requested"] = args.resugar_drops
    if llbc.exists():
        audit.update(inventory(llbc))
    (destination / "inventory.json").write_text(json.dumps(audit, indent=2) + "\n")
    if result.returncode or not llbc.exists() or audit["has_errors"]:
        raise RuntimeError(f"candidate Charon extraction incomplete: {destination}")
    command = [str(tool / "aeneas"), "-backend", "lean", str(llbc),
               "-dest", str(destination), "-subdir", "/Reference", "-split-files",
               "-namespace", "CandidateSignal", "-use-lean-modules", "false",
               "-warnings-as-errors", "-no-progress-bar",
               *(["-filter-trait-methods"] if args.filter_unused_trait_methods else [])]
    with (destination / "aeneas.log").open("w") as log:
        result = subprocess.run(command, cwd=source, env=env, stdout=log, stderr=subprocess.STDOUT)
    audit["aeneas_exit_code"] = result.returncode
    audit["aeneas_command"] = [x.replace(str(ROOT), "$WORKSPACE") for x in command]
    audit["generated_files"] = {str(p.relative_to(HERE)): digest(p)
                                for p in sorted((destination / "Reference").glob("*.lean"))}
    (destination / "inventory.json").write_text(json.dumps(audit, indent=2) + "\n")
    print(f"Candidate Aeneas exit={result.returncode}; inventory: {destination.relative_to(ROOT)}")
    print("No candidate extraction is accepted as a proof reference by this script.")


if __name__ == "__main__":
    main()
