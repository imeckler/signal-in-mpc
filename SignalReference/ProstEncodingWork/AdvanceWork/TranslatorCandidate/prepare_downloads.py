#!/usr/bin/env python3
"""Inventory checksum-pinned opam sources; download only via approved curl calls."""
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent


def main():
    plan = json.loads((HERE / "dependency-plan.json").read_text())
    repo = HERE / "Opam/repo/default/packages"
    cache = HERE / "Opam/download-cache"
    sources, package_metadata = {}, {}
    for action in plan["solution"]:
        package = action["install"]
        name, version = package["name"], package["version"]
        opam = repo / name / f"{name}.{version}" / "opam"
        package_metadata[f"{name}.{version}"] = hashlib.sha256(opam.read_bytes()).hexdigest()
        for block in re.finditer(r'(?:url|extra-source\s+"[^"]+")\s*\{([^}]+)\}', opam.read_text(), re.S):
            source = re.search(r'src:\s*"([^"]+)"', block[1])
            checksums = re.findall(r'"(sha256|sha512|md5)=([0-9a-f]+)"', block[1])
            assert source and checksums, (opam, block[0])
            preferred = next((c for c in checksums if c[0] == "sha256"), checksums[0])
            algorithm, expected = preferred
            path = cache / algorithm / expected[:2] / expected
            path.parent.mkdir(parents=True, exist_ok=True)
            cached = path.exists()
            if cached:
                assert hashlib.new(algorithm, path.read_bytes()).hexdigest() == expected
            sources[(algorithm, expected)] = {"url": source[1], "path": str(path),
                "algorithm": algorithm, "checksum": expected, "cached": cached}
    output = {"package_metadata_sha256": package_metadata, "sources": list(sources.values())}
    (HERE / "download-plan.json").write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps([s for s in sources.values() if not s["cached"]]))


if __name__ == "__main__":
    main()
