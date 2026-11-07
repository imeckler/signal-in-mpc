#!/usr/bin/env python3
"""Apply one isolated, unaccepted translator change to the exact source pin."""
import difflib
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = HERE / "aeneas-5b9dcf33dccdb1560ea7203ac57ea202476b6ed3"
RELATIVE = "src/interp/InterpStatements.ml"
BEFORE = """  (* Continue - note that we do as if the function call has been successful,
   * by giving {!Unit} to the continuation, because we place us in the case
   * where we haven't panicked. Of course, the translation needs to take the
   * panic case into account... *)
  ([ (ctx, Unit) ], cc_singleton __FILE__ __LINE__ span cc)
"""
AFTER = """  (* The symbolic call in [cc] must remain: its Result may fail or diverge.
   * A successful return of type Never is impossible. End that unreachable
   * continuation instead of falling through with Unit. The existing Panic
   * continuation is used only AFTER the retained call; for Result Never,
   * binding any continuation equals elimination of the empty success value.
   * See the isolated NeverContinuation Lean proof and regression audit.
   * This is not an assertion that the called function itself panics. *)
  let result = if inst_sg.output = TNever then Panic else Unit in
  ([ (ctx, result) ], cc_singleton __FILE__ __LINE__ span cc)
"""


def main():
    manifest = json.loads((HERE / "original-source-manifest.json").read_text())
    path = SOURCE / RELATIVE
    before = path.read_text()
    assert hashlib.sha256(path.read_bytes()).hexdigest() == manifest["source_sha256"][RELATIVE]
    assert before.count(BEFORE) == 1
    after = before.replace(BEFORE, AFTER)
    patch = "".join(difflib.unified_diff(before.splitlines(keepends=True),
                                      after.splitlines(keepends=True),
                                      fromfile="a/" + RELATIVE, tofile="b/" + RELATIVE))
    (HERE / "never-continuation.patch").write_text(patch)
    path.write_text(after)
    report = {"accepted_translator": False, "candidate_only": True,
              "source_commit": manifest["aeneas_commit"], "changed_files": [RELATIVE],
              "before_sha256": hashlib.sha256(before.encode()).hexdigest(),
              "after_sha256": hashlib.sha256(after.encode()).hexdigest(),
              "patch_sha256": hashlib.sha256(patch.encode()).hexdigest(),
              "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "actual_rust_sources_changed": [], "standard_models_changed": [],
              "accepted_binary_changed": False}
    (HERE / "candidate-patch.json").write_text(json.dumps(report, indent=2) + "\n")
    print("Applied isolated Never continuation candidate; not accepted.")


if __name__ == "__main__":
    main()
