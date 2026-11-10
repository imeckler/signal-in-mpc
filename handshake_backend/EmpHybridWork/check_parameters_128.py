"""Exact public cut/bucket bounds for the statistical-128 bridge pool profiles.

Public combinatorics only (same counting bound as parameters.py); no backend or
composition claim. The buckets printed here must match dabit_generator.h.
"""
import json
from fractions import Fraction
from pathlib import Path
from parameters import Parameters,choose
rows=[]
for n in (256,512,1024):
    p=choose(n,128);assert all(p.bound(t)<Fraction(1,1<<128) for t in range(1,n+1))
    smaller=Parameters(n,p.bucket-1,2,128)
    try:smaller.validate()
    except ValueError:pass
    else:raise AssertionError('bucket not minimal')
    rows.append(p.receipt())
report={'passed':True,'profiles':rows,'scope':'Public combinatorial bound only; backend/security composition unvalidated.'}
Path(__file__).with_name('parameters-128-report.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({r['outputs']:(r['bucket'],round(r['approx_bound_bits'],1),r['candidates_per_party']) for r in rows}))
