#!/usr/bin/env python3
"""Deterministic imports-only replay; actual assertion/XOR/AES loop unchanged."""
import hashlib,json,pathlib
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parents[1];ROOT=REF.parent
original=REF/'AesZipInvestigation/Generated/Baseline/Funs.lean';source=original.read_text();old='import AesZipInvestigation.Generated.Baseline.Types\n';new=old+'import AesCtrBlockWork.ZipModelV1.StdBorrowZip\n';assert source.count(old)==1
replayed=source.replace(old,new);assert replayed.replace(new,old)==source
(HERE/'ActualRoundKey.lean').write_text(replayed)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(HERE/'import-replay.json').write_text(json.dumps(dict(candidate_only=True,accepted_extracted_Zip_proof=False,imports_only=True,actual_computational_body_edits=False,original=str(original.relative_to(ROOT)),original_sha256=sha(original),replayed_sha256=sha(HERE/'ActualRoundKey.lean'),script_sha256=sha(pathlib.Path(__file__))),indent=2)+'\n')
