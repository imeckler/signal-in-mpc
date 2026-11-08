"""Host ownership/lifecycle regression only; no native-MPC claim."""
from pathlib import Path
import hashlib,json,os,subprocess,tempfile
ROOT=Path(__file__).resolve().parents[1]
def check():
 sources=['handshake_backend/WebSocketWork/PrivateMuxRegistry.h','handshake_backend/WebSocketWork/mux_registry_checks.cpp']
 with tempfile.TemporaryDirectory(prefix='tls-mux-registry-') as directory:
  binary=Path(directory)/'checks'
  subprocess.run([os.environ.get('CXX','c++'),'-std=c++20','-fsanitize=address,undefined','-g','-I'+str(ROOT/'handshake_backend/WebSocketWork'),str(ROOT/sources[1]),'-o',str(binary)],check=True,timeout=120)
  subprocess.run([str(binary)],check=True,timeout=60)
 return {'status':'pass','scope':'ASAN/UBSAN host mock ownership and lifecycle; not native MPC','profiles':9,'source_sha256':{name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in sources},'checks':['two conversations and reordered replies with slot reuse','cross-owner input rejection before ID allocation','one pending per conversation','consumed input rejection','failed computed-validity admission burns ID without retention/checkpoint','four-conversation capacity','send before authenticated activation','unsolicited completion','four outstanding slots and replay rejection']}
if __name__=='__main__':
 result=check();target=ROOT/'benchmarks/results/tls-private-mux-registry.json';target.write_text(json.dumps(result,indent=2)+'\n');print(target)
