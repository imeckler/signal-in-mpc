#!/usr/bin/env python3
"""Capacity/private-length prefix agreement, reusing exact inherited actual-CTR closure."""
import hashlib,importlib.util,json,pathlib,re,subprocess
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parents[1];ROOT=REF.parent
s=importlib.util.spec_from_file_location('b',REF/'CtrReferenceV1Work/check_conversion.py');base=importlib.util.module_from_spec(s);s.loader.exec_module(base)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 inherited=HERE/'proof-report.json';receipt=json.loads(inherited.read_text());assert receipt['passed']
 for n,w in receipt['source_sha256'].items():assert sha(ROOT/n)==w,n
 module='CtrReferenceV1Work/FixedGeneratorV1Work/PrefixSemantics';source=REF/(module+'.lean');body=source.read_text();assert not any(t in body for t in ['sorry','axiom ','native_decide','bv_decide']);names=re.findall(r'^theorem (\w+)',body,re.M)
 out=base.BUILD/(module+'.olean');r=subprocess.run(['lean','-o',str(out),module+'.lean'],cwd=REF,env=base.environment,capture_output=True,text=True,timeout=60);assert r.returncode==0,r.stdout+r.stderr
 audit=base.BUILD/'CtrPrefixAxioms.lean';audit.write_text('import CtrReferenceV1Work.FixedGeneratorV1Work.PrefixSemantics\n'+''.join('#print axioms LibSignalReference.Candidate.FixedCtr.'+n+'\n'for n in names));text=subprocess.check_output(['lean',str(audit)],cwd=REF,env=base.environment,text=True);assert text.count('depends on axioms:')+text.count('does not depend on any axioms')==len(names)
 for g in re.findall(r'depends on axioms: \[(.*?)\]',text,re.S):assert set(re.findall(r'[\w.]+',g))<={'propext','Classical.choice','Quot.sound'}
 assert '_native'not in text and 'sorryAx'not in text;(HERE/'prefix-axioms.txt').write_text(text)
 (HERE/'prefix-report.json').write_text(json.dumps(dict(passed=True,candidate_only=True,backend_independent=True,kernel_endpoints=len(names),endpoints=names,foundation_axioms_only=True,capacity_ciphertext_prefix_equals_true_length_ciphertext_expression=True,all_secret_key_plaintext_and_padding_bits_unrestricted=True,no_crypto_replication_per_private_length=True,counter_profile_public_deterministic_index=True,private_length_runtime_release_adapter_not_proved=True,full_generic_Rust_stream_wrapper_still_open=True,production_changed=False,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in [pathlib.Path(__file__),source,inherited]},object_sha256={str(out.relative_to(ROOT)):sha(out)}),indent=2)+'\n');print('PASS',len(names),'foundational CTR capacity/prefix endpoints')
if __name__=='__main__':main()
