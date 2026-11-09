#!/usr/bin/env python3
"""Focused key-composition/compiler proof and independent HKDF layout checks.
This does not claim actual Rust initialization or native bootstrap execution.
"""
import hashlib,hmac,json,pathlib,subprocess
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def seq(n,k):return bytes((i+k)%256 for i in range(n))
def hkdf(ikm,info,salt=bytes(32),n=96):
 prk=hmac.digest(salt,ikm,'sha256');out=b'';prior=b''
 for i in range(1,(n+31)//32+1):prior=hmac.digest(prk,prior+info+bytes([i]),'sha256');out+=prior
 return out[:n]
def main():
 subprocess.run(['lake','build','TlsMpc.Signal.PrivateBootstrapKeysV1'],cwd=ROOT,check=True,stdout=subprocess.DEVNULL)
 run=subprocess.run(['lake','env','lean','--run',str(HERE/'KeyChecks.lean')],cwd=ROOT,capture_output=True,text=True,check=True,timeout=120)
 rows=run.stdout.splitlines();got=bytes(json.loads(rows[0]));assert 'passed7 rejection'in rows[-1]
 identity=seq(32,101);dh=seq(96,1)+identity+seq(160,51);kem=b'\xff\x08'+seq(1568,7)+seq(32,17)
 keys=hkdf(bytes([255])*32+dh[128:256]+kem[1570:],b'WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024')
 ratchet=hkdf(dh[256:],b'WhisperRatchet',keys[:32],64)
 sender=ratchet[:32]+dh[32:96]+ratchet[32:]+bytes(8)
 receivers=bytes(276)+b'\xff'+seq(32,33)+keys[32:64]+bytes(4)
 assert got==b'\xff'+dh[:32]+sender+receivers+keys[64:]and len(got)==546
 audit=subprocess.run(['lake','env','lean',str(HERE/'KeyAudit.lean')],cwd=ROOT,capture_output=True,text=True,check=True)
 (HERE/'key-axioms.txt').write_text(audit.stdout)
 assert not any(x in audit.stdout for x in ['sorryAx','native_decide','Lean.ofReduceBool'])
 files=[pathlib.Path(__file__),HERE/'KeyChecks.lean',HERE/'KeyAudit.lean',ROOT/'TlsMpc/Signal/PrivateBootstrapKeysV1.lean']
 report=dict(key_composition_build_passed=True,independent_HKDF_layout_matches=True,accepted_bytes=546,rejection_profiles=7,foundation_endpoints=4,actual_Rust_init_refinement=False,native_MPC=False,whole_bootstrap=False,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files})
 (HERE/'key-report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
