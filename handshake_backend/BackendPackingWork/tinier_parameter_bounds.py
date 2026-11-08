#!/usr/bin/env python3
"""Public parameter arithmetic only; does not enable a runtime/protocol."""
import json, math
from pathlib import Path

def bound(outputs, bucket):
    checks = bucket
    buckets = bucket * outputs
    raw = bucket * buckets + checks
    denominator = math.comb(raw, bucket)
    # Exact rational comparison: no floating rounding in the security decision.
    correctness_128 = buckets * (1 << 128) <= denominator
    # FKOS Lemma 10 is strict: B > (s-1)/log2(L)+1.
    leakage_128 = pow(outputs, bucket - 1) > (1 << 127)
    return dict(outputs=outputs, correctness_bucket=bucket, leakage_bucket=bucket,
                opened_checks=checks, sacrifice_outputs=buckets, exact_raw=raw,
                raw_per_output=raw / outputs,
                correctness_numerator=buckets, correctness_denominator=str(denominator),
                correctness_bits=math.log2(denominator)-math.log2(buckets),
                correctness_at_most_2_minus_128=correctness_128,
                leakage_lemma_128_strict=leakage_128,
                raw_authentication_ot_input_cost_measured=False)

def tests():
    # Independently enumerate all bad-triple counts for small divisible batches.
    count=0
    for n in range(1,33):
        for b in range(2,9):
            m=n*b+b
            upper_n,upper_d=n,math.comb(m,b)
            for t in range(1,n+1):
                assert math.comb(n,t)*upper_d <= upper_n*math.comb(m,t*b)
                count+=1
    assert bound(64,23)['leakage_lemma_128_strict']
    assert not bound(64,22)['leakage_lemma_128_strict']
    return count

rows=[]
for outputs in [64,256,1024,4096,16384,65536,262144,1048576]:
    bucket=next(b for b in range(2,130) if bound(outputs,b)['correctness_at_most_2_minus_128'] and bound(outputs,b)['leakage_lemma_128_strict'])
    rows.append(bound(outputs,bucket))
report=dict(candidate_only=True,runtime_changed=False,statistical_target=128,
    exact_small_distribution_checks=tests(),curves=rows,
    primary_sources=['https://eprint.iacr.org/2016/944.pdf','https://eprint.iacr.org/2015/901.pdf'],
    assumptions=['FLNW Theorem 5.3: uniform permutation, fixed bad set, C>=B, exact divisible batch; maximum bad count B.',
      'FKOS Lemma 10: final output count L, independent combine permutation and bucket size B; strict inequality checked exactly.',
      'Authenticated raw prefix must be trimmed to exact raw count BEFORE challenge/shuffle; authenticated discarded owners must be erased.',
      'These are separate correctness/leakage bounds, not a complete Tinier security proof or total failure bound.',
      'GF128 authentication constants, OT computational assumptions, input checks and per-phase union terms remain separate obligations.',
      'No whole-deployment lifetime bound is asserted; batch/phase bounds compose with explicit query counts.'])
path=Path(__file__).with_name('tinier-parameter-bounds.json')
path.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'distribution_checks':report['exact_small_distribution_checks'],'curves':[{k:r[k] for k in ['outputs','correctness_bucket','exact_raw','raw_per_output']} for r in rows]}))
