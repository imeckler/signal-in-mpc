#!/usr/bin/env python3
"""Public fixture differential of Lean numeric text builder, no secret openings."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from backend_adapter.boolean import load
from scripts.check_lean_crypto import evaluate_lanes
HERE=Path(__file__).resolve().parent
ART=ROOT/'.deps/private-hash-artifacts/private-text-48-80.json'
def varint(n):
 b=bytearray()
 while n>=128:b.append((n&127)|128);n>>=7
 return bytes(b)+bytes([n])
def expected(raw):
 n=int.from_bytes(raw[1:3],'big')
 try:raw[3:3+n].decode('utf8')
 except UnicodeDecodeError:return bytes(90)
 if raw[0]!=255 or n>48:return bytes(90)
 body=raw[3:3+n];time=raw[-8:];dm=b'\x0a'+varint(n)+body+b'\x38'+varint(int.from_bytes(time,'big'))
 content=b'\x0a'+varint(len(dm))+dm
 return b'\xff\x00'+content+b'\x80'+bytes(79-len(content))+time

def main():
 audit=subprocess.check_output(['lake','env','lean',str(HERE/'Checks.lean')],cwd=ROOT,text=True)
 groups=re.findall(r'depends on axioms: \[(.*?)\]',audit,re.S);assert len(groups)==4
 for group in groups:assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'}
 rows=[]
 def add(body,n=None,status=255,time=1900000000000,tail=0):
  assert len(body)<=48
  rows.append(bytes([status])+((len(body) if n is None else n).to_bytes(2,'big'))+body+bytes([tail])*(48-len(body))+time.to_bytes(8,'big'))
 for n in range(49):
  for time in [0,127,128,16383,16384,2**32,2**64-1]:add(b'x'*n,time=time,tail=255)
 for body in ['Hello, Signal!','Coffee ☕ ready','😀 café \x00 test','你好，世界','€'*16]:add(body.encode())
 for body in [b'\x80',b'\xc0\x80',b'\xc1\xbf',b'\xc2',b'\xe0\x9f\xbf',b'\xed\xa0\x80',b'\xf0\x8f\xbf\xbf',b'\xf4\x90\x80\x80',b'\xf5\x80\x80\x80',b'\xff',b'ok\xe2\x82']:
  add(body)
 for body in [b'\xc2\x80',b'\xdf\xbf',b'\xe0\xa0\x80',b'\xed\x9f\xbf',b'\xef\xbf\xbf',b'\xf0\x90\x80\x80',b'\xf4\x8f\xbf\xbf']:add(body)
 for n in [49,255,256,65535]:add(b'',n=n)
 for status in [0,1,127,254]:add(b'hello',status=status)
 image=load(ART);observed=evaluate_lanes(image,rows)
 for raw,out in zip(rows,observed):assert out==expected(raw),(raw.hex(),out.hex(),expected(raw).hex())
 # Independent actual prost encoder with exact relay DataMessage derive and
 # pinned libsignal service.proto outer Content, public fixture inputs only.
 oracle=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-text-recipient-oracle'
 valid=[(raw,out)for raw,out in zip(rows,observed)if out[0]==255]
 requests=[dict(mode='text',body=raw[3:3+int.from_bytes(raw[1:3],'big')].hex(),timestamp=int.from_bytes(raw[-8:],'big'))for raw,_ in valid]
 result=subprocess.run([str(oracle)],input=''.join(json.dumps(row)+'\n'for row in requests),text=True,capture_output=True,check=True)
 for answer,(_,out)in zip(map(json.loads,result.stdout.splitlines()),valid):assert answer==dict(accepted=True,padded=out[2:82].hex())
 assert len(result.stdout.splitlines())==len(valid)
 files=[Path(__file__),HERE/'Export.lean',HERE/'Checks.lean',ROOT/'TlsMpc/Signal/PrivateTextNotification.lean']
 report={'cases':len(rows),'numeric_nodes':len(image['nodes']),'kernel_endpoints':4,'foundational_axioms_only':True,
  'private_text_capacity':48,'public_iso7816_bucket':80,'timestamp_body_and_return_identical':True,
  'utf8_domain':'strict valid UTF8; relay lossy replacement outside this domain is rejected',
  'native_MPC_executed':False,'actual_session_recipient_tested':False,'actual_prost_valid_fixture_matches':len(valid),'full_app_schema_refinement_proved':False,'utf8_unicode_semantic_refinement_proved':False,
  'artifact_sha256':hashlib.sha256(ART.read_bytes()).hexdigest(),
  'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in files}}
 (HERE/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(f'{len(rows)} numeric text/padding/UTF8 fixtures and4 kernel endpoints passed',flush=True)
if __name__=='__main__':main()
