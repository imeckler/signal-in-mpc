"""Fresh additive diagnostics overlay; never edits the tested runtime."""
from pathlib import Path
import difflib,hashlib,json,re,shutil,subprocess
ROOT=Path(__file__).resolve().parents[2];WORK=Path(__file__).resolve().parent
BASE=ROOT/'.deps/tls-session-runtime/MP-SPDZ';DEST=ROOT/'.deps/tls-backend-diagnostic-runtime/MP-SPDZ'
def sha(data):return hashlib.sha256(data).hexdigest()
def prepare():
 if DEST.exists():raise SystemExit('preserve existing diagnostic candidate; destination exists')
 identities={}
 for source in BASE.rglob('*'):
  rel=source.relative_to(BASE)
  if any(part in ['deps','local','Player-Data','Memory','Programs'] for part in rel.parts):continue
  if not source.is_file() or source.suffix not in ['.h','.hpp','.cpp','.c','.S'] and source.name not in ['Makefile','CONFIG','CONFIG.mine']:continue
  data=source.read_bytes();identities[str(rel)]=sha(data);target=DEST/rel;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
 for folder in ['deps','local']:(DEST/folder).symlink_to((BASE/folder).resolve(),target_is_directory=True)
 changes={}
 def edit(name,old,new):
  before,after=changes.get(name,((DEST/name).read_text(),(DEST/name).read_text()))
  assert after.count(old)==1,(name,old[:80],after.count(old));changes[name]=(before,after.replace(old,new))
 for name in ['Networking/Player.cpp','Networking/CryptoPlayer.cpp','Protocols/Beaver.hpp','Processor/Data_Files.h','Processor/Machine.hpp']:
  text=(DEST/name).read_text();first=text.index('#include ');line=text[first:text.index('\n',first)];edit(name,line,'#include "Tools/PublicProtocolMetrics.h"\n'+line)
 for name in ['Networking/Player.cpp','Networking/CryptoPlayer.cpp']:
  before,after=changes[name]
  def hook(match):
   prefix,expression=match.group(1),match.group(2)
   if expression=='other.sent':return match.group(0) # aggregation is not a send
   return f'{prefix}tls_public_diagnostics::sent_bytes({expression});\n{match.group(0)}'
  after,count=re.subn(r'(?m)^(\s*)(?:comm_stats\.)?sent \+= ([^;\n]+);',hook,after);assert count>0
  changes[name]=(before,after)
 tag='tls_public_diagnostics::Scope public_scope(T::clear::field_type()==DATA_GF2?tls_public_diagnostics::Domain::binary:tls_public_diagnostics::Domain::field, tls_public_diagnostics::Phase::'
 edit('Protocols/Beaver.hpp','void Beaver<T>::exchange()\n{','void Beaver<T>::exchange()\n{\n    '+tag+'online);')
 edit('Processor/Data_Files.h','array<T, 3> Preprocessing<T>::get_triple(int n_bits)\n{','array<T, 3> Preprocessing<T>::get_triple(int n_bits)\n{\n  '+tag+'preprocessing);')
 edit('Processor/Machine.hpp','void Machine<sint, sgf2n>::prepare(const string& progname_str)\n{','void Machine<sint, sgf2n>::prepare(const string& progname_str)\n{\n  tls_public_diagnostics::LoadTimer public_prepare(false);')
 edit('Processor/Machine.hpp','  load_schedule(progname_str);','  { tls_public_diagnostics::LoadTimer public_load(true); load_schedule(progname_str); }')
 edit('Processor/Machine.h','  void retire_worker_epoch(bool renew_transport = true);','  void retire_worker_epoch(bool renew_transport = true);\n  DataPositions public_function_usage();')
 marker='template<class sint, class sgf2n>\ntemplate<class ArithmeticVisitor, class BinaryVisitor>\nvoid Machine<sint, sgf2n>::visit_secret_scratch'
 getter='''template<class sint, class sgf2n>
DataPositions Machine<sint, sgf2n>::public_function_usage()
{
  if (ThreadQueue::thread_queue or threads.empty() or threads.size()!=tinfo.size() or
      queues.size()!=threads.size() or not active_threads.empty())
    throw runtime_error("diagnostic usage requires quiescent host");
  DataPositions result;
  for(size_t i=0;i<tinfo.size();++i) {
    if(not queues[i] or not queues[i]->available() or not tinfo[i].processor)
      throw runtime_error("diagnostic usage requires joined jobs");
    result.increase(tinfo[i].processor->DataF.get_usage());
  }
  return result;
}

'''
 edit('Processor/Machine.hpp',marker,getter+marker)
 patch=''
 for name,(before,after) in changes.items():
  (DEST/name).write_text(after);patch+=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/'+name,tofile='b/'+name))
 (WORK/'diagnostics.patch').write_text(patch);shutil.copy2(WORK/'PublicProtocolMetrics.h',DEST/'Tools/PublicProtocolMetrics.h')
 identity=sha(''.join(n+'\0'+h+'\n' for n,h in sorted(identities.items())).encode())
 report={'scope':'isolated additive diagnostic candidate; no protocol/config switch','base_source_identity':identity,'base_source_sha256':identities,'overlay_sha256':sha(patch.encode()),'header_sha256':sha((WORK/'PublicProtocolMetrics.h').read_bytes()),'destination':str(DEST.relative_to(ROOT)),'coverage':'Player sent-counter increments; Beaver online exchange and triple-fetch preprocessing scopes; other paths explicitly unattributed; nested times overlap; bytes do not','runtime_build_passed':False}
 (WORK/'diagnostic-prepare.json').write_text(json.dumps(report,indent=2)+'\n');print(DEST)
if __name__=='__main__':prepare()
