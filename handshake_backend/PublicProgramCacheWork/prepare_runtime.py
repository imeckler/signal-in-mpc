#!/usr/bin/env python3
"""Isolated public-program cache overlay. Never edits frozen/runtime defaults."""
from pathlib import Path
import shutil,hashlib,json,subprocess,difflib
ROOT=Path(__file__).resolve().parents[2];WORK=Path(__file__).parent
BASE=ROOT/'.deps/tls-backend-diagnostic-runtime-v4/MP-SPDZ';DEST=ROOT/'.deps/tls-public-program-cache-runtime/MP-SPDZ'
if DEST.exists():raise SystemExit('preserve existing public-cache candidate')
DEST.mkdir(parents=True)
# Public source/build products only. No Player-Data, memory snapshots or prep.
for name in ['Processor','Tools','Math','Networking','Protocols','GC','Machines','BMR','ExternalIO','Auth','FHE','FHEOffline','OT','deps','local']:
 p=BASE/name
 if p.exists():
  if p.is_symlink():(DEST/name).symlink_to(p.resolve(),target_is_directory=True)
  else:shutil.copytree(p,DEST/name,symlinks=True)
for name in ['Makefile','CONFIG','CONFIG.mine','libSPDZ.so']:
 if(BASE/name).exists():shutil.copy2(BASE/name,DEST/name)
for name in ['PublicCodeCache.h','PinnedPublicCode.h']:shutil.copy2(WORK/name,DEST/'Tools'/name)
original={}
def edit(path,old,new):
 p=DEST/path;s=p.read_text();original.setdefault(path,(BASE/path).read_text());assert old in s,(path,old[:80]);p.write_text(s.replace(old,new,1))
edit('Processor/BaseMachine.h','    void print_compiler();','    void load_schedule_stream(const string&, istream&, bool load_bytecode = true);\n    void print_compiler();')
p=DEST/'Processor/BaseMachine.cpp';s=p.read_text();original['Processor/BaseMachine.cpp']=(BASE/'Processor/BaseMachine.cpp').read_text()
start=s.index('  int nprogs;',s.index('void BaseMachine::load_schedule('));end=s.index('\nvoid BaseMachine::print_compiler()',start)
body=s[start:end].replace('  inpf.close();\n','')
s=s[:start]+'''  load_schedule_stream(progname, inpf, load_bytecode);
}

void BaseMachine::load_schedule_stream(const string& progname, istream& inpf, bool load_bytecode)
{
  this->progname = progname;
  string fname = "Programs/Schedules/" + progname + ".sch";
'''+body+s[end:];p.write_text(s)
edit('Processor/Program.h','  void parse(istream& s);','  void parse(istream& s);\n  void parse_pinned(const string&, const map<string,string>&);\n  size_t public_storage_bytes() const;')
edit('Processor/Program.cpp','#include "Processor/Program.h"','#include "Processor/Program.h"\n#include "Tools/PinnedPublicCode.h"')
p=DEST/'Processor/Program.cpp';s=p.read_text();s+='''
// Exact admitted bytes are hashed once and then parsed from that same owned
// snapshot. Only public instructions/usage metadata may enter the cache.
void Program::parse_pinned(const string& filename, const map<string,string>& pins)
{
  name = boost::filesystem::path(filename).stem().string();
  auto bytes = tls_public_code::read(filename, pins);
  tls_public_code::Stream stream(bytes);
  parse(stream);
  Hash hasher; hasher.update(bytes.data(), bytes.size());
  hash = hasher.final().str();
}
size_t Program::public_storage_bytes() const
{
  size_t bytes = sizeof(*this) + p.capacity() * sizeof(Instruction) + name.capacity() + hash.capacity();
  for (const auto& instruction : p)
    bytes += instruction.start.capacity() * sizeof(unsigned) + instruction.str.capacity();
  bytes += offline_data_used.inputs.capacity() * sizeof(offline_data_used.inputs[0]);
  for (const auto& values : offline_data_used.extended)
    bytes += values.size() * (sizeof(decltype(values)::value_type) + 4 * sizeof(void*));
  bytes += offline_data_used.edabits.size() * (sizeof(decltype(offline_data_used.edabits)::value_type) + 4 * sizeof(void*));
  bytes += offline_data_used.matmuls.size() * (sizeof(decltype(offline_data_used.matmuls)::value_type) + 4 * sizeof(void*));
  return bytes;
}
''';s=s.replace('sizeof(decltype(values)::value_type)','sizeof(map<DataTag,long long>::value_type)');p.write_text(s)
edit('Processor/Machine.h','#include <memory>','#include <memory>\n#include "Tools/PublicCodeCache.h"\n#include "Tools/PinnedPublicCode.h"')
edit('Processor/Machine.h','  void prepare(const string& progname_str);','''  struct PublicPreparedImage {
    vector<Program> programs; vector<string> filenames;
    string program, compiler, domain, relevant, security, gf2n, communication;
    int threads; size_t accounted_bytes;
  };
  tls_public_code::Cache<PublicPreparedImage> public_cache{size_t(1024)*1024*1024, 16};
  const map<string,string>* admitted_public_files = nullptr;
  string admitted_public_key, current_public_key, current_public_config;
  bool public_cache_failed = false;
  uint64_t public_cache_direct_hits = 0, public_cache_loads = 0;
  void prepare(const string& progname_str);''')
edit('Processor/Machine.h','  // Exclusive host-owner API, between completed exported function calls.','''  // Internal pinned embedding API; no RPC/import entry point. Full closure
  // must be independently pinned/agreed by the caller before admission.
  void run_function_pinned(const string&, FunctionArgument&, vector<FunctionArgument>&,
      const string& closure_identity, const map<string,string>& files);
  array<uint64_t,5> public_program_cache_metrics() const {
    return {public_cache_direct_hits + public_cache.hits, public_cache_loads,
      public_cache.evictions, public_cache.retained_bytes(), public_cache.size()};
  }

  // Exclusive host-owner API, between completed exported function calls.''')
edit('Processor/Machine.hpp','  progs[i].parse(filename);','''  if (admitted_public_files) progs[i].parse_pinned(filename, *admitted_public_files);
  else progs[i].parse(filename);''')
old='''  progs.clear();
  { tls_public_diagnostics::LoadTimer public_load(true); load_schedule(progname_str); }'''
new='''  // Quiescent host only. Cache holds no Processor, protocol, prep, RNG,
  // secret registers, memory, sockets or function arguments.
  bool reused = false;
  if (not admitted_public_key.empty())
    {
      if (admitted_public_key == current_public_key and not progs.empty())
        { reused = true; ++public_cache_direct_hits; }
      else
        {
          auto requested = public_cache.take(admitted_public_key);
          if (not current_public_key.empty() and not progs.empty())
            {
              auto image = make_unique<PublicPreparedImage>();
              image->accounted_bytes = sizeof(PublicPreparedImage);
              for (const auto& p : progs) image->accounted_bytes += p.public_storage_bytes();
              image->programs = std::move(progs); image->filenames = bc_filenames;
              image->program = progname; image->threads = nthreads;
              image->compiler = compiler; image->domain = domain;
              image->relevant = relevant_opts; image->security = security;
              image->gf2n = gf2n; image->communication = expected_communication;
              auto bytes = image->accounted_bytes;
              public_cache.put(current_public_key, std::move(image), bytes);
            }
          if (requested)
            {
              progs = std::move(requested->programs); bc_filenames = std::move(requested->filenames);
              progname = requested->program; nthreads = requested->threads;
              compiler = requested->compiler; domain = requested->domain;
              relevant_opts = requested->relevant; security = requested->security;
              gf2n = requested->gf2n; expected_communication = requested->communication;
              reused = true;
            }
        }
    }
  current_public_key.clear();
  if (not reused)
    {
      progs.clear();
      tls_public_diagnostics::LoadTimer public_load(true);
      if (admitted_public_files)
        {
          auto bytes = tls_public_code::read("Programs/Schedules/" + progname_str + ".sch", *admitted_public_files);
          tls_public_code::Stream stream(bytes); load_schedule_stream(progname_str, stream);
          ++public_cache_loads;
        }
      else load_schedule(progname_str);
    }
  else
    for (auto& program : progs)
      {
        auto name = program.get_name();
        M2.minimum_size(SGF2N, CGF2N, program, name);
        Mp.minimum_size(SINT, CINT, program, name);
        Mi.minimum_size(NONE, INT, program, name);
        bit_memories.reset(program);
      }
  current_public_key = admitted_public_key;'''
edit('Processor/Machine.hpp',old,new)
# Descriptor reads also use the same verified byte snapshot.
edit('Processor/Machine.hpp','''  ifstream file;
  FunctionArgument::open(file, name, arguments);''','''  ifstream ordinary;
  string descriptor_bytes;
  unique_ptr<tls_public_code::Stream> admitted;
  if (admitted_public_files)
    {
      string path = "Programs/Functions/" + name;
      for (auto& argument : arguments) path += "-" + argument.get_type_string();
      descriptor_bytes = tls_public_code::read(path, *admitted_public_files);
      admitted.reset(new tls_public_code::Stream(descriptor_bytes));
    }
  else FunctionArgument::open(ordinary, name, arguments);
  istream& file = admitted ? static_cast<istream&>(*admitted) : static_cast<istream&>(ordinary);''')
p=DEST/'Processor/Machine.hpp';s=p.read_text();s+='''
#ifndef TLS_PUBLIC_CODE_PINNED_METHOD_DEFINED
#define TLS_PUBLIC_CODE_PINNED_METHOD_DEFINED
template<class sint, class sgf2n>
void Machine<sint, sgf2n>::run_function_pinned(const string& name,
    FunctionArgument& result, vector<FunctionArgument>& arguments,
    const string& identity, const map<string,string>& files)
{
  if (public_cache_failed or admitted_public_files or ThreadQueue::thread_queue or
      not active_threads.empty() or identity.size() != 64 or files.empty())
    throw runtime_error("invalid public cache admission");
  // Configuration changes invalidate retained public parse metadata. Epoch
  // renewal deliberately does not: code contains no cryptographic state.
  ostringstream config;
  config << typeid(sint).name() << ":" << typeid(sgf2n).name() << ":" << N.num_players()
    << ":" << opts.prime << ":" << opts.lgp << ":" << opts.lg2
    << ":" << opts.security_parameter << ":" << opts.semi_honest
    << ":" << opts.live_prep << ":" << opts.disk_memory
    << ":" << sint::clear::pr() << ":" << gf2n_long::degree()
    << ":" << opts.direct << ":" << opts.bits_from_squares << ":" << opts.batch_size
    << ":" << opts.bucket_size << ":" << opts.trunc_error;
  for (auto value : opts.args) config << ":" << value;
  for (const auto& option : OnlineOptions::singleton.options) config << ":" << option;
  for (auto& option : opts.options) config << ":" << option;
  if (current_public_config != config.str())
    { public_cache.clear(); current_public_key.clear(); current_public_config = config.str(); }
  try
    {
      string admitted = name + "\\n";
      for (auto& argument : arguments) admitted += argument.get_type_string() + "\\n";
      for (const auto& entry : files) admitted += entry.second + " " + entry.first + "\\n";
      if (identity != tls_public_code::sha256(admitted))
        throw runtime_error("public cache closure identity mismatch");
      // Even cache hits reject any mutation of the admitted closure. Filenames
      // are lookup locations, never cache identities.
      for (const auto& entry : files) tls_public_code::read(entry.first, files);
      admitted_public_files = &files;
      admitted_public_key = identity + ":" + current_public_config;
      run_function(name, result, arguments);
      admitted_public_files = nullptr; admitted_public_key.clear();
    }
  catch (...)
    {
      admitted_public_files = nullptr; admitted_public_key.clear();
      current_public_key.clear(); public_cache.clear(); public_cache_failed = true;
      throw;
    }
}
#endif
''';p.write_text(s)
patch=''
for path,old in original.items():patch+=''.join(difflib.unified_diff(old.splitlines(True),(DEST/path).read_text().splitlines(True),fromfile='a/'+path,tofile='b/'+path))
(WORK/'public-cache.patch').write_text(patch)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipt={'candidate_only':True,'production_runtime_changed':False,'base_runtime':str(BASE.relative_to(ROOT)),'source_hashes':{p:sha(BASE/p)for p in original},'candidate_hashes':{p:sha(DEST/p)for p in original},'helper_hashes':{n:sha(WORK/n)for n in ['PublicCodeCache.h','PinnedPublicCode.h']},'native_executed':False,'accounted_retained_instruction_budget_bytes':1024**3,'max_retained_entries':16,'memory_budget_scope':'accounted parsed instruction vectors/arguments plus usage metadata estimate; excludes current active image and allocator overhead/RSS'}
(WORK/'prepare-report.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('Prepared isolated cache source candidate; not yet built or validated')
