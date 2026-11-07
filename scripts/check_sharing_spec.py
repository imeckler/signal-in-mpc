#!/usr/bin/env python3
"""Build the Lean sharing contracts and reject unexpected proof axioms.

This checks functional Lean theorems only. It runs no MPC protocol and makes
no freshness, confidentiality, persistence, or throughput claim.
"""

from pathlib import Path
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
THEOREMS = [
    "LinearSharing.normalized_refresh_preserves_value",
    "LinearSharing.refreshBatch_preserves_values",
    "unpack_packKey",
    "packKey_injective",
    "keyLimbs_fit_curve25519",
    "advance_epoch",
    "advance_context",
    "accepted_requires_all_five",
    "replay_rejected",
    "skipped_epoch_rejected",
    "Exposure.period_is_accounted",
    "Exposure.refresh_charged_source",
    "Exposure.refresh_charged_target",
    "Exposure.three_distinct_exposures_reject",
    "Exposure.refresh_and_next_period_share_budget",
    "Exposure.accounted_monotone",
    "Exposure.violation_persists",
    "Exposure.rotating_admissible",
    "Exposure.rotating_exposes_every_party",
    "resume_requires_retirement",
    "resume_requires_fresh_correlations",
    "resume_requires_transport_rekey",
    "resume_requires_all_cleanup_receipts",
    "retained_material_blocks_resume",
    "MaskReuse.common_mask_difference",
    "MaskReuse.three_point_reconstruction",
    "MaskReuse.three_epoch_difference",
    "MaskReuse.known_reference_recovers_value",
    "MaskReuse.subset_basis_zero",
    "MaskReuse.subset_basis_excluded",
]
ALLOWED = {"propext", "Quot.sound", "Classical.choice"}


def checked(command):
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    return result.stdout + result.stderr


def main():
    checked(["lake", "build", "TlsMpc.Sharing.Refresh", "TlsMpc.Sharing.Epoch", "TlsMpc.Sharing.MaskReuse"])
    source = "import TlsMpc.Sharing.Refresh\nimport TlsMpc.Sharing.Epoch\nimport TlsMpc.Sharing.MaskReuse\n"
    source += "".join(f"#print axioms TlsMpc.Sharing.{name}\n" for name in THEOREMS)
    with tempfile.TemporaryDirectory(prefix="tls-mpc-sharing-check-") as temporary:
        check_file = Path(temporary) / "SharingAxioms.lean"
        check_file.write_text(source)
        output = checked(["lake", "env", "lean", str(check_file)])
    checked_names = set(re.findall(r"'TlsMpc\.Sharing\.([^']+)'", output))
    if checked_names != set(THEOREMS):
        raise RuntimeError("Incomplete theorem audit:\n" + output)
    used = set()
    for listing in re.findall(r"depends on axioms: \[([^]]*)\]", output):
        used.update(item.strip() for item in listing.split(",") if item.strip())
    unexpected = used - ALLOWED
    if unexpected:
        raise RuntimeError(f"Unexpected axioms: {sorted(unexpected)}\n{output}")
    json.loads((ROOT / "specs/sharing-refresh.json").read_text())
    print(json.dumps({
        "status": "passed",
        "theorems_audited": len(THEOREMS),
        "axioms_used": sorted(used),
        "security_or_runtime_test": False,
        "scope": "Lean functional contracts and design JSON syntax only",
    }, indent=2))


if __name__ == "__main__":
    main()
