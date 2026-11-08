#!/usr/bin/env python3
"""Public frame fixtures for unchanged pinned tungstenite client."""
import hashlib,json,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];ORACLE=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-established-send-oracle'
def main():
 wires=['8203616263880203e8','020161890178800162880203e8','82816100000000','880303e8ff']
 r=subprocess.run([str(ORACLE)],input=''.join(json.dumps(dict(mode='check_ws_frames',wire=x))+'\n' for x in wires),text=True,capture_output=True,check=True)
 answers=[json.loads(x) for x in r.stdout.splitlines()]
 assert [x['closed'] for x in answers]==[True,True,False,False]
 assert answers[0]['messages'][0]==dict(type='binary',data='616263')
 assert answers[1]['messages'][:2]==[dict(type='ping',data='78'),dict(type='binary',data='6162')]
 assert 'masked frame' in answers[2]['error'] and 'UTF-8' in answers[3]['error']
 files=[Path(__file__),ROOT/'signal_backend/Oracle/src/main.rs',ROOT/'signal_backend/Oracle/src/relay.rs']
 report={'cases':answers,'actual_tungstenite_client':True,'network_side_effects':False,
  'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
  'oracle_sha256':hashlib.sha256(ORACLE.read_bytes()).hexdigest()}
 Path(__file__).with_name('ws-frame-report.json').write_text(json.dumps(report,indent=2)+'\n');print('4 actual tungstenite frame fixtures passed')
if __name__=='__main__':main()
