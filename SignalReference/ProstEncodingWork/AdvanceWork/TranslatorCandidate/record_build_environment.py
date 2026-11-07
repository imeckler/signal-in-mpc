#!/usr/bin/env python3
"""Record the isolated exact-source build and external read-only tool inputs."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    prefix = HERE / "Opam/aeneas-never"
    tools = {
        "opam": Path(shutil.which("opam")),
        "ocamlc": Path("/Users/izzy/.opam/default/bin/ocamlc"),
        "ocamlopt": Path("/Users/izzy/.opam/default/bin/ocamlopt"),
        "dune": prefix / "bin/dune",
        "charon": ROOT / ".deps/charon-4ad295c1bf982b5533ce7d85f4ddc889ff3127f8/charon/target/release/charon",
        "rustc": ROOT / ".deps/rust-nightly-2026-08-18/bin/rustc",
        "accepted_aeneas": ROOT / ".deps/aeneas-2026-08-27/aeneas",
        "baseline": HERE / "Bin/baseline",
        "candidate": HERE / "Bin/candidate",
        "candidate_runtime_gmp": Path("/opt/homebrew/opt/gmp/lib/libgmp.10.dylib"),
    }
    versions = {
        name: subprocess.check_output([str(path), flag], text=True).strip()
        for name, path, flag in (("ocamlc", tools["ocamlc"], "-version"),
                                 ("dune", tools["dune"], "--version"),
                                 ("opam", tools["opam"], "--version"),
                                 ("rustc", tools["rustc"], "--version"),
                                 ("accepted_aeneas", tools["accepted_aeneas"], "-version"),
                                 ("baseline", tools["baseline"], "-version"),
                                 ("candidate", tools["candidate"], "-version"))}
    assert versions["ocamlc"] == "5.3.0" and versions["dune"] == "3.19.1"
    command = ["opam", "exec", "--root", str(HERE / "Opam"), "--switch", "aeneas-never", "--",
               "env", "PATH=" + str(prefix / "bin") + ":/Users/izzy/.opam/default/bin:/opt/homebrew/bin:/usr/bin:/bin",
               "dune", "build", "--profile", "release", "main.exe", "-j", "4"]
    report = {
        "candidate_only": True, "accepted_toolchain_changed": False,
        "source_commit": "5b9dcf33dccdb1560ea7203ac57ea202476b6ed3",
        "charon_source_commit": "4ad295c1bf982b5533ce7d85f4ddc889ff3127f8",
        "versions": versions,
        "tools": {name: {"path": str(path), "resolved_path": str(path.resolve()), "sha256": digest(path)}
                  for name, path in tools.items()},
        "build_command": command,
        "build_cwd": str(HERE / "aeneas-5b9dcf33dccdb1560ea7203ac57ea202476b6ed3/src"),
        "baseline_environment": {"AENEAS_VERSION": versions["baseline"]},
        "candidate_environment": {"AENEAS_VERSION": versions["candidate"]},
        "dependency_source_cache_checksums": ["download-plan.json", "visitors-download-plan.json"],
        "dependency_version_inventory_sha256": digest(HERE / "installed-packages.txt"),
        "build_logs_sha256": {name: digest(HERE / name) for name in
                              ("dependency-build.log", "visitors-upgrade-build.log", "baseline-build.log", "candidate-build.log")},
        "build_note": "Only workspace-local package/build directories were written. The original OCaml compiler and GMP library were read from existing installations.",
        "opam_note": "Local repository/cache copies and checksum-verified approved curl downloads supplied dependencies. The managed outer filesystem/network sandbox remained in force; nested opam sandbox-exec is unavailable on this host.",
    }
    (HERE / "build-environment.json").write_text(json.dumps(report, indent=2) + "\n")
    print("Recorded exact tools, candidate/baseline binaries, dependency versions and build commands.")


if __name__ == "__main__":
    main()
