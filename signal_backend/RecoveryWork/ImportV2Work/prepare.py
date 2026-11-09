#!/usr/bin/env python3
"""Deterministic container-only helper candidate; original V1 stays unchanged."""
import hashlib,json,pathlib
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[2]
def main():
 source=HERE.parent/'RawFieldReadmit.h';base=source.read_text();text=base
 changes=[('#include "NativeOwnShareArchive.h"','#include "../NativeOwnShareArchive.h"\n#include "WipingAllocator.h"'),('namespace signal_mpc::recovery {','namespace signal_mpc::recovery::import_v2 {'),('class RawFieldReadmit {','class RawFieldReadmitV2 {'),('explicit RawFieldReadmit(Player& player)','explicit RawFieldReadmitV2(Player& player)'),('std::vector<Share> private_inputs(const std::vector<Field>& mine)','PrivateVector<Share> private_inputs(const PrivateVector<Field>& mine)'),('input.exchange();std::vector<Share> out;','input.exchange();PrivateVector<Share> out;'),('std::vector<Field> mine(count)','PrivateVector<Field> mine(count)'),('std::vector<Share> values,checks;','PrivateVector<Share> values,checks;'),('std::vector<Field> local_random(checks.size())','PrivateVector<Field> local_random(checks.size())'),('std::vector<Share> coefficients(checks.size(),Share(Field(0)))','PrivateVector<Share> coefficients(checks.size(),Share(Field(0)))')]
 for old,new in changes:
  assert text.count(old)==1,old;text=text.replace(old,new)
 target=HERE/'RawFieldReadmitV2.h';candidate='// Container-erasure candidate only; protocol/prep/RNG teardown NOT covered.\n'+text
 if not target.exists() or target.read_text()!=candidate:target.write_text(candidate)
 sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
 report=dict(candidate_only=True,base_sha256=sha(source),candidate_sha256=sha(target),transformations=changes,computational_field_expressions_changed=False,private_container_allocation_erasure=True,protocol_prep_PRNG_teardown_covered=False,provider_admission=False)
 (HERE/'derivation.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
