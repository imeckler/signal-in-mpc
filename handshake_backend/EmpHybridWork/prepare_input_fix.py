"""Diagnostic stock tree + input-only repair; unsafe openings fail CLOSED.
No claim that remaining KRRW validation/composition is repaired.
"""
import difflib,hashlib,json,pathlib
ROOT=pathlib.Path(__file__).resolve().parents[2];BASE=ROOT/'.deps/two-party-comparison';HERE=pathlib.Path(__file__).resolve().parent
base=json.loads((BASE/'linear-mask-overlay.json').read_text());src=pathlib.Path(base['target']);sha=lambda b:hashlib.sha256(b).hexdigest()
observer='''
#ifdef EMP_HYBRID_INPUT_OBSERVER
inline void hybrid_observe_input(const std::vector<uint8_t>&bytes) {
  const char* target=std::getenv("EMP_HYBRID_OBSERVE_INPUT_HASH");
  if(!target||bytes.size()!=256)return;
  char digest[Hash::DIGEST_SIZE];Hash::hash_once(digest,bytes.data(),bytes.size());
  const char* h="0123456789abcdef";std::string encoded;
  for(unsigned char b:std::string(digest,Hash::DIGEST_SIZE)){encoded+=h[b>>4];encoded+=h[b&15];}
  std::cout<<"input_observer recovered_peer_input="<<(encoded==target?1:0)<<"\\n";
}
#endif
'''
reports={}
for name,repair in [('emp-ag2pc-input-diagnostic-v1',False),('emp-ag2pc-private-input-v2',True)]:
 target=BASE/name;files={};diffs=[]
 for rel,expected in base['files'].items():
  raw=(src/rel).read_bytes()
  if sha(raw)!=expected:raise ValueError('base source drift '+rel)
  data=raw.decode()
  if rel=='emp-ag2pc/backend/protocol.h':
   start=data.index('std::vector<SecureWires> AG2PCProtocol::process_inputs(')
   end=data.index('std::vector<uint8_t> AG2PCProtocol::decode(',start)
   if repair:
    data=data[:start]+observer+(HERE/'input_phase_v2.inc').read_text()+'\n'+data[end:]
    needle='''  if (recipient == PUBLIC) {'''
    if data.count(needle)!=1:raise ValueError('opening patch')
    data=data.replace(needle,'''  if(recipient==PUBLIC||recipient==ALICE)error("decode: two-sided opening gated pending validation review");
'''+needle)
   else:
    data=data[:start]+observer+data[start:]
    needle='''  // Verify peer's MAC hash before using their share.'''
    data=data.replace(needle,'''#ifdef EMP_HYBRID_INPUT_OBSERVER
  if(party==BOB)hybrid_observe_input(peer_x_packed);
#endif
'''+needle)
    needle='''      io->send_data(buf.data(), n);'''
    if data.count(needle)!=1:raise ValueError('public lie hook')
    data=data.replace(needle,'''#ifdef EMP_HYBRID_TEST_ATTACKS
      if(party==BOB&&std::getenv("EMP_TEST_PUBLIC_LIE")&&n)buf[0]^=1;
#endif
'''+needle)
   data='#include <climits>\n'+data
  if rel=='emp-ag2pc/backend/engine.h' and not repair:
   needle='''      mpc->io->send_bool((const bool*)st.Lambda_AND.data(), st.num_ands);'''
   if data.count(needle)!=1:raise ValueError('Gamma hook')
   data=data.replace(needle,'''      auto reported=st.Lambda_AND;
#ifdef EMP_HYBRID_TEST_ATTACKS
      if(mpc->party==BOB&&std::getenv("EMP_TEST_FALSE_GAMMA")&&!reported.empty())reported[0]^=1;
#endif
      mpc->io->send_bool(reported.data(), st.num_ands);''')
  out=data.encode();dest=target/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(out);files[rel]=sha(out)
  if raw!=out:diffs.extend(difflib.unified_diff(raw.decode().splitlines(True),data.splitlines(True),fromfile='a/'+rel,tofile='b/'+rel))
 (HERE/(name+'.patch')).write_text(''.join(diffs))
 reports[name]=dict(target=str(target),repair_input_only=repair,files=files)
report=dict(base_revision=base['source_revision'],base_overlay=base,variants=reports,scope='Input privacy/correctness diagnostics and source-backed owner-only input phase. PUBLIC/ALICE outputs explicitly gated in repair; active validation remains unreviewed.')
(BASE/'input-fix-build-source.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v['target'] for k,v in reports.items()}))
