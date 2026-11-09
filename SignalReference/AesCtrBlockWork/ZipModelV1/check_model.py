#!/usr/bin/env python3
"""PUBLIC fixture comparisons: actual indexed StdZip and unchanged AES loop."""
import tarfile,hashlib,importlib.util,json,pathlib,random,subprocess
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parents[1];ROOT=REF.parent
spec=importlib.util.spec_from_file_location('base',REF/'CtrReferenceV1Work/check_conversion.py');base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 binary=ROOT/'.deps/aes-std-borrow-oracle-target/debug/aes-std-borrow-oracle';built=json.loads((HERE/'oracle-build-report.json').read_text());assert sha(binary)==built['binary_sha256']
 subprocess.run(['python3',str(HERE/'prepare.py')],check=True)
 for module in ['AesZipInvestigation/Generated/Baseline/Types','AesCtrBlockWork/ZipModelV1/StdBorrowZip','AesCtrBlockWork/ZipModelV1/ActualRoundKey']:
  out=base.BUILD/(module+'.olean');out.parent.mkdir(parents=True,exist_ok=True);r=subprocess.run(['lean','-o',str(out),str(REF/(module+'.lean'))],cwd=REF,env=base.environment,capture_output=True,text=True,timeout=60);assert r.returncode==0,r.stdout+r.stderr
 provenance=json.loads((REF/'PaddingWork/Unpad/sysroot-provenance.json').read_text());archive=ROOT/'.deps/rust-src-nightly-2026-08-18.tar.xz';assert sha(archive)==provenance['rust_source_archive_sha256']
 with tarfile.open(archive)as bundle:
  for name in ['core/src/iter/adapters/zip.rs','core/src/slice/iter.rs','core/src/slice/iter/macros.rs']:
   entry='rust-src-nightly/rust-src/lib/rustlib/src/rust/library/'+name
   assert bundle.extractfile(entry).read()==(ROOT/'.deps/rust-nightly-2026-08-18/lib/rustlib/src/rust/library'/name).read_bytes()
 rng=random.Random(20261109);cases=[]
 for na in range(6):
  for nb in range(6):
   for a in range(na+1):
    for b in range(nb+1):
     for steps in sorted(set([0,1,2,min(na-a,nb-b),min(na-a,nb-b)+1,12])):
      cases.append(dict(mode='zip',state=[rng.getrandbits(64)for _ in range(na)],keys=[rng.getrandbits(64)for _ in range(nb)],left_start=a,right_start=b,steps=steps))
 for _ in range(256):
  na=rng.randrange(17);nb=rng.randrange(17);cases.append(dict(mode='zip',state=[rng.getrandbits(64)for _ in range(na)],keys=[rng.getrandbits(64)for _ in range(nb)],left_start=rng.randrange(na+1),right_start=rng.randrange(nb+1),steps=rng.randrange(25)))
 for side in range(2):
  for bit in range(512):
   state=[0]*8;keys=[0]*8;(state if side==0 else keys)[bit//64]=1<<(bit%64);cases.append(dict(mode='add',state=state,keys=keys))
 for _ in range(64):cases.append(dict(mode='add',state=[rng.getrandbits(64)for _ in range(8)],keys=[rng.getrandbits(64)for _ in range(8)]))
 for n in range(17):
  if n!=8:cases.append(dict(mode='add',state=[rng.getrandbits(64)for _ in range(8)],keys=[rng.getrandbits(64)for _ in range(n)]))
 wire=''.join(json.dumps(c,separators=(',',':'))+'\n'for c in cases)
 rust=subprocess.run([str(binary)],input=wire,text=True,capture_output=True,timeout=60);assert rust.returncode==0,rust.stderr
 lean=subprocess.run(['lean','--run',str(HERE/'Evaluate.lean')],cwd=REF,env=base.environment,input=wire,text=True,capture_output=True,timeout=60);assert lean.returncode==0,lean.stdout+lean.stderr
 expected=[json.loads(s)for s in rust.stdout.splitlines()];actual=[json.loads(s)for s in lean.stdout.splitlines()];assert len(actual)==len(cases)==len(expected)
 for i,(a,b)in enumerate(zip(actual,expected,strict=True)):assert a==b,(i,cases[i],a,b)
 std=ROOT/'.deps/rust-nightly-2026-08-18/lib/rustlib/src/rust/library/core/src';zip_source=std/'iter/adapters/zip.rs';slice_source=std/'slice/iter.rs';text=zip_source.read_text();assert 'A: TrustedRandomAccess + Iterator' in text and 'B: TrustedRandomAccess + Iterator'in text and 'let i = self.index;'in text and 'self.index += 1;'in text
 assert "TrustedRandomAccess for Iter<'a, T>"in slice_source.read_text()and "TrustedRandomAccess for IterMut<'a, T>"in slice_source.read_text()
 files=[pathlib.Path(__file__),HERE/'Evaluate.lean',HERE/'StdBorrowZip.lean',HERE/'ActualRoundKey.lean',HERE/'prepare.py',HERE/'import-replay.json',HERE/'oracle-build-report.json',zip_source,slice_source,std/'slice/iter/macros.rs',ROOT/'.deps/libsignal-vendor/aes-0.9.1/src/soft/fixslice64.rs']
 report=dict(passed=True,candidate_only=True,trusted_Std_model=True,extracted_Zip_proof=False,actual_AES_assert_XOR_loop_bodies_retained=True,actual_slice_TrustedRandomAccess_specialization=True,pinned_Std_source_archive_verified=True,nonzero_starting_positions=True,unequal_remaining_lengths=True,early_drop_and_suffix_preservation=True,repeated_None_and_owner_writeback=True,actual_assertion_rejection_preserves_state=True,cases=len(cases),zip_cases=sum(c['mode']=='zip'for c in cases),actual_add_round_key_cases=sum(c['mode']=='add'for c in cases),all1024_operand_basis_bits=True,input_sha256=hashlib.sha256(wire.encode()).hexdigest(),result_sha256=hashlib.sha256(rust.stdout.encode()).hexdigest(),source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files},actual_AES_round_or_CTR_proof=False,native_MPC=False)
 (HERE/'model-report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS',len(cases),'actual indexed StdZip/AES-loop public differential cases; trusted Std boundary explicit')
if __name__=='__main__':main()
