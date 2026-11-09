#!/usr/bin/env python3
"""Pin and report inspected author experiment source; never launches parties."""
import hashlib,json,pathlib,math
root=pathlib.Path(__file__).resolve().parents[2]
rev='57d7bed3895975f78b215226d851156aea1826c8'
source=root/'.deps/boolean-backend-research'/('ccs-DEN22-'+rev)
hashfile=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
checks={
 'README.md':['implementation of core components','with 7'],
 'src/frn/check.h':['// Omitted for now','void SetupPRG();','void AgreeOnTranscript();','hash = Field(0);','// TODO protocol for obtaining it'],
 'src/frn/util.h':['FpElement<frn::lib::math::Mp61>'],
 'src/frn/lib/primitives/prg.h':['mSeed[sizeof(BlockType)] = {0}'],
 'src/frn/exp_mult.cc':['FakeInputs(xs, ys','(void)output;'],
 'src/frn/exp_check.cc':['check_protocol.ReconstructMsgs();'],
 'src/frn/lib/math/fp.h':['return sizeof(ValueType);'],
 'src/frn/mult.cc':['mId < 2 * mThreshold + 1','party_id < mSize - mThreshold'],
}
for path,needles in checks.items():
 text=(source/path).read_text()
 for needle in needles: assert needle in text,(path,needle)
assert 'Check check_protocol' not in (source/'src/frn/exp_mult.cc').read_text()
report={'repository':'https://github.com/anderspkd/ccs-DEN22','revision':rev,
 'archive_sha256':hashfile(pathlib.Path('/tmp/den22.tar.gz')),
 'tree_hashes':{str(p.relative_to(source)):hashfile(p) for p in sorted(source.rglob('*')) if p.is_file()},
 'checks':checks,'supported_malicious_backend_established':False,'MPC_executed':False,
 'configured_value_domain':'61-bit prime;8-byte element; no bit-packed Boolean implementation established',
 'n7_t2_local_replicated_share_elements':math.comb(6,2),
 'n7_t2_local_replicated_share_bytes':math.comb(6,2)*8,
 'n7_t2_multiplication_only_source_loop_payload':{
  'all_Send_calls_bytes_per_gate':80,'external_peer_Send_calls_bytes_per_gate_aggregate':64,
  'scope':'Two sends of5 field elements total across the group, excluding2self sends for external total. Excludes correlation/input/check/output/network framing; incomplete check means NOT secure full-protocol cost.'},
 'blockers':['unimplemented joint check randomness setup','unimplemented transcript agreement','dummy zero hashes','received check values discarded without verification','no application output reconstruction/check path established','default deterministic benchmark PRG seed','no checked Fp25519 mixed bridge','no runtime erasure/epoch/failure integration'],
 'decision':'Do not build or promote as malicious7PC/t2 candidate; retain as core experiment reference only.'}
out=pathlib.Path(__file__).with_name('den22-report.json');out.write_text(json.dumps(report,indent=2)+'\n')
print('PASS source identity/assertions; incomplete author experiment rejected as backend')
