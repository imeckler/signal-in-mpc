"""Exact public probability/model checks; NOT native bridge evidence."""
import itertools
import json
from fractions import Fraction
from math import comb
from pathlib import Path
from parameters import Parameters,choose

def model_check():
    # Exhaust all cuts and ordered buckets for ell2/B2/C2, all bad counts.
    # One corrupt party's mismatched bit inputs become a fixed bad set.
    outputs,bucket,cut_factor=2,2,2
    n=outputs*bucket;m=cut_factor*n;prime=17
    challenges=[]
    for kept in itertools.combinations(range(m),n):
        for ordered in itertools.permutations(kept):challenges.append(ordered)
    checks=0
    for count in range(m+1):
        bad=set(range(count));accept_wrong=0
        honest=[i%2 for i in range(m)]
        field=[(int(i in bad)+h-2*int(i in bad)*h)%prime for i,h in enumerate(honest)]
        binary=honest
        for ordered in challenges:
            kept=set(ordered)
            if bad-kept:continue # opened corrupt raw contribution rejects
            passed=True
            for start in range(0,n,bucket):
                a,b=ordered[start:start+bucket]
                opened=(field[a]+field[b]-2*field[a]*field[b])%prime
                passed &= opened in (0,1) and opened==(binary[a]^binary[b])
            if passed and any(i in bad for i in ordered[::bucket]):accept_wrong+=1
        actual=Fraction(accept_wrong,len(challenges))
        expected=Fraction(comb(outputs,count//bucket),comb(m,count)) if count and count<=n and count%bucket==0 else Fraction(0)
        assert actual==expected,(count,actual,expected)
        checks+=1
    # A non-bit field input paired with any honest bit stays non-bit under XOR.
    for p in (5,7,17,31):
        for x in range(2,p):
            for y in (0,1):assert (x+y-2*x*y)%p not in (0,1)
    return checks,len(challenges)

if __name__=='__main__':
    checks,challenges=model_check()
    rows=[choose(n).receipt() for n in (1,16,64,256)]
    for n in (1,16,64,256):
        p=choose(n)
        assert all(p.bound(t)<Fraction(1,1<<40) for t in range(1,n+1))
    for bad in [Parameters(1,2,2,40),Parameters(16,2,2,40),Parameters(64,6,2,128)]:
        try:bad.validate()
        except ValueError:pass
        else:raise AssertionError('bad profile accepted')
    report={'passed':True,'scope':'exact public combinatorics and small ideal checker model only; no native bridge/security composition claim',
            'bad_count_cases':checks,'challenges_per_case':challenges,'profiles':rows,
            'native_bridge_implemented':False}
    path=Path(__file__).with_name('parameter-report.json');path.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'passed':True,'profiles':len(rows),'bad_count_cases':checks}))
