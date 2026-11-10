"""Conservative finite parameters for the RW19 cut/bucket daBit construction.

No backend security claim follows from these public combinatorial calculations.
The exact bound includes every possible count of bad retained buckets.
"""
from dataclasses import dataclass
from fractions import Fraction
from math import comb, log2

@dataclass(frozen=True)
class Parameters:
    outputs: int
    bucket: int
    cut_factor: int
    statistical_target: int

    @property
    def candidates(self):return self.cut_factor*self.bucket*self.outputs

    @property
    def kept_before_bucketing(self):return self.bucket*self.outputs

    def bound(self,t):
        if not 1<=t<=self.outputs:raise ValueError('bad bucket count')
        return Fraction(comb(self.outputs,t),comb(self.candidates,self.bucket*t))

    def exact_worst_bound(self):
        return max((self.bound(t),t) for t in range(1,self.outputs+1))

    def conservative_bound(self):
        # Union over output buckets on top of the published single-bucket
        # sufficient expression. Also check every exact count independently.
        return Fraction(self.outputs,self.cut_factor**self.bucket*comb(self.kept_before_bucketing,self.bucket))

    def validate(self):
        if self.outputs<1 or self.outputs>4096 or self.bucket<2 or self.cut_factor<2:
            raise ValueError('unsupported bounded parameter profile')
        # 128 is the production profile (2026-11-09); 40 is retained for earlier receipts.
        if self.statistical_target not in (40,128):raise ValueError('unsupported statistical target')
        target=Fraction(1,1<<self.statistical_target)
        worst,_=self.exact_worst_bound()
        if worst>=target or self.conservative_bound()>=target:raise ValueError('insufficient checked bound')
        return self

    def receipt(self):
        bound,t=self.exact_worst_bound()
        return {'outputs':self.outputs,'bucket':self.bucket,'cut_factor':self.cut_factor,
                'candidates_per_party':self.candidates,'statistical_target':self.statistical_target,
                'worst_bad_bucket_count':t,'exact_bound_numerator':bound.numerator,
                'exact_bound_denominator':str(bound.denominator),'approx_bound_bits':log2(bound.denominator)-log2(bound.numerator),
                'backend_security_proved':False}

def choose(outputs,statistical_target=40):
    if outputs<1 or outputs>4096 or statistical_target not in (40,128):raise ValueError('unsupported profile')
    for bucket in range(2,statistical_target+2):
        p=Parameters(outputs,bucket,2,statistical_target)
        try:return p.validate()
        except ValueError:pass
    raise ValueError('no bounded parameters')
