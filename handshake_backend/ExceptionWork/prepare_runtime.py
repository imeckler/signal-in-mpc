#!/usr/bin/env python3
"""Fresh isolated caught-failure candidate; no canonical source writes."""
from pathlib import Path
import shutil,json,hashlib,difflib,sys,tempfile
ROOT=Path(__file__).resolve().parents[2];WORK=Path(__file__).parent
BASE=ROOT/'.deps/tls-backend-diagnostic-runtime-v4/MP-SPDZ'
DEST=ROOT/'.deps/tls-caught-failure-runtime/MP-SPDZ'
VERIFY='--verify' in sys.argv
ACTUAL=DEST
temporary=tempfile.TemporaryDirectory(prefix='tls-failure-overlay-') if VERIFY else None
if VERIFY: DEST=Path(temporary.name)/'MP-SPDZ'
assert not DEST.exists(),'preserve existing candidate'
identity={}
for p in BASE.rglob('*'):
 r=p.relative_to(BASE)
 if any(x in ['deps','local','Programs','Player-Data','Memory'] for x in r.parts):continue
 if not p.is_file() or (p.suffix not in ['.h','.hpp','.cpp','.c','.S','.o','.a','.d'] and p.name not in ['Makefile','CONFIG','CONFIG.mine']):continue
 if VERIFY and p.suffix in ['.o','.a','.d']:continue
 q=DEST/r;q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
 if p.suffix not in ['.o','.a','.d']:identity[str(r)]=hashlib.sha256(p.read_bytes()).hexdigest()
for x in ['deps','local']:(DEST/x).symlink_to((BASE/x).resolve(),target_is_directory=True)
changes={}
def edit(n,a,b):
 old,new=changes.get(n,((DEST/n).read_text(),(DEST/n).read_text()))
 assert new.count(a)==1,(n,a[:70],new.count(a));changes[n]=(old,new.replace(a,b))
def include(n,header):
 s=(DEST/n).read_text();i=s.index('#include ');line=s[i:s.index('\n',i)];edit(n,line,f'#include "Tools/{header}"\n'+line)
for name in ['SocketCancellation.h','FailureScope.h']:shutil.copy2(WORK/name,DEST/'Tools'/name)
# Exact tested queue prerequisite.
n='Tools/WaitQueue.h';before=(DEST/n).read_text();after=(ROOT/'.deps/tls-caught-failure-queue/Tools/WaitQueue.h').read_text();changes[n]=(before,after)
include('Processor/ThreadQueue.h','SocketCancellation.h')
edit('Processor/ThreadQueue.h','    void schedule(const ThreadJob& job);','    void cancel_failure() noexcept { in.stop(); out.stop(); }\n    void schedule(const ThreadJob& job);')
edit('Processor/ThreadQueue.cpp','    auto res = in.pop();','    ThreadJob res;\n    if (not in.pop(res)) throw runtime_error("MPC worker cancelled");')
edit('Processor/ThreadQueue.cpp','    auto res = out.pop();','    ThreadJob res;\n    if (not out.pop(res)) throw runtime_error("MPC worker cancelled");')
# Socket token dies before the boost base closes/reuses its fd.
include('Networking/ssl_sockets.h','SocketCancellation.h')
edit('Networking/ssl_sockets.h','    typedef boost::asio::ssl::stream<boost::asio::ip::tcp::socket> parent;','    typedef boost::asio::ssl::stream<boost::asio::ip::tcp::socket> parent;\n    tls_caught_failure::SocketToken cancellation_token;')
edit('Networking/ssl_sockets.h','        lowest_layer().assign(boost::asio::ip::tcp::v4(), plaintext_socket);','        try { lowest_layer().assign(boost::asio::ip::tcp::v4(), plaintext_socket); }\n        catch (...) { ::close(plaintext_socket); throw; }\n        cancellation_token.arm(plaintext_socket);')
edit('Networking/ssl_sockets.h','        cancellation_token.arm(plaintext_socket);','        cancellation_token.arm(plaintext_socket);\n#ifdef SO_NOSIGPIPE\n        int no_sigpipe=1;\n        if(::setsockopt(plaintext_socket,SOL_SOCKET,SO_NOSIGPIPE,&no_sigpipe,sizeof(no_sigpipe)))\n            throw runtime_error("MPC no-SIGPIPE socket setup failed");\n#else\n        throw runtime_error("caught-failure candidate requires per-socket no-SIGPIPE support");\n#endif')
# Fixed handshake diagnostics; throw through C++ owners, never exit.
n='Networking/CryptoPlayer.cpp';s=(DEST/n).read_text();a=s.index('    cerr << side');b=s.index('\n}\n\nCryptoPlayer::CryptoPlayer',a)
edit(n,s[a:b],'    (void)side; (void)other; (void)me; (void)e;\n    throw runtime_error("MPC TLS handshake failed");')
include(n,'FailureScope.h')
edit('Networking/CryptoPlayer.h','    void connect(int other, vector<int>* plaintext_sockets);','    void clear_owned_connections() noexcept;\n    void connect(int other, vector<int>* plaintext_sockets);')
edit(n,'    vector<int> plaintext_sockets[2];','''    vector<int> plaintext_sockets[2];
    tls_caught_failure::OnUnwind construction_failure([&]() noexcept {
        tls_caught_failure::runtime_sockets.cancel();
        clear_owned_connections();
        for(auto& group:plaintext_sockets) for(int fd:group)
            if(fd>=0) ::close(fd);
    });''')
edit(n,'        close_client_socket(player.socket(my_num()));','        close_client_socket(player.socket(my_num()));\n        plaintext_sockets[i][my_num()]=-1;')
edit(n,'    sockets[i] = new ssl_socket(io_service, ctx, plaintext_sockets[0][i],','    int first=plaintext_sockets[0][i]; plaintext_sockets[0][i]=-1;\n    sockets[i] = new ssl_socket(io_service, ctx, first,')
edit(n,'    other_sockets[i] = new ssl_socket(io_service, ctx, plaintext_sockets[1][i],','    int second=plaintext_sockets[1][i]; plaintext_sockets[1][i]=-1;\n    other_sockets[i] = new ssl_socket(io_service, ctx, second,')
edit(n,'''        delete sockets[i];
        delete other_sockets[i];
        delete senders[i];
        delete receivers[i];''','''        delete senders[i]; senders[i]=nullptr;
        delete receivers[i]; receivers[i]=nullptr;
        delete sockets[i]; sockets[i]=nullptr;
        delete other_sockets[i]; other_sockets[i]=nullptr;''')
edit(n,'CryptoPlayer::~CryptoPlayer()\n{','CryptoPlayer::~CryptoPlayer() { clear_owned_connections(); }\n\nvoid CryptoPlayer::clear_owned_connections() noexcept\n{')
# Never rethrow across communication pthread entry. Cancels all active TLS I/O.
n='Networking/Receiver.cpp';s=(DEST/n).read_text();a=s.index('    if (OnlineOptions::singleton.has_option("throw_exceptions"))');b=s.index('\n}\n\ntemplate<class T>\nvoid Receiver<T>::run_with_error',a)
edit(n,s[a:b],'''    (void)other;
    try { run_with_error(); }
    catch (...) {
        tls_caught_failure::runtime_sockets.cancel();
        fprintf(stderr, "MPC failure category=communication\\n");
        fail();
    }''')
# Instruction wrappers must propagate; upstream otherwise exits before worker catch.
for n in ['Processor/Instruction.hpp','GC/Program.hpp']:
 text=(DEST/n).read_text();a=text.index('          auto inst =') if n.startswith('Processor') else text.index('            auto inst =')
 b=text.index('exit(1);',a)+len('exit(1);')
 edit(n,text[a:b],'          fprintf(stderr,"MPC failure category=instruction\\n");\n          throw;')
# Machine terminal state; profile currently permits one VM worker, many IO workers.
include('Processor/Machine.h','SocketCancellation.h')
edit('Processor/Machine.h','  vector<pthread_t> threads;','  vector<pthread_t> threads;\n  atomic<bool> caught_failure{false};\n  bool caught_cleanup_complete=false;')
edit('Processor/Machine.h','  DataPositions public_function_usage();','''  DataPositions public_function_usage();
  void report_caught_failure() noexcept;
  void cleanup_caught_failure() noexcept;
  bool has_caught_failure() const noexcept { return caught_failure.load(); }
  bool failed_cleanup_complete() const noexcept { return caught_cleanup_complete; }''')
include('Processor/Machine.hpp','FailureScope.h')
edit('Processor/Machine.hpp','  tls_public_diagnostics::LoadTimer public_prepare(false);','  if(has_caught_failure()) throw runtime_error("MPC runtime terminal failure");\n  tls_public_diagnostics::LoadTimer public_prepare(false);')
edit('Processor/Machine.hpp','  // keep preprocessing\n','  if(nthreads!=1) throw runtime_error("caught-failure candidate requires one VM worker");\n\n  // keep preprocessing\n')
edit('Processor/Machine.hpp','  ifstream file;\n  FunctionArgument::open(file, name, arguments);','''  if(has_caught_failure()) throw runtime_error("MPC runtime terminal failure");
  tls_caught_failure::OnUnwind host_failure([this]() noexcept {
    report_caught_failure(); cleanup_caught_failure();
  });
  ifstream file;
  FunctionArgument::open(file, name, arguments);''')
edit('Processor/Machine.hpp','  // only stop actually running threads','''  if(has_caught_failure()) {
    cleanup_caught_failure();
    return {DataPositions(N.num_players()), NamedCommStats{}};
  }
  // only stop actually running threads''')
edit('Processor/Machine.hpp','  // Host-owned FunctionArgument/output shares deliberately survive.','  // Host-owned FunctionArgument/output shares deliberately survive.') if False else None
edit('Processor/Machine.hpp','  /* Set up the threads */','  threads.reserve(nthreads); worker_stacks.reserve(nthreads);\n  /* Set up the threads */')
edit('Processor/Machine.hpp','Machine<sint, sgf2n>::~Machine()\n{\n  stop_threads();','Machine<sint, sgf2n>::~Machine()\n{\n  try { stop_threads(); } catch (...) { report_caught_failure(); cleanup_caught_failure(); }')
edit('Processor/Machine.hpp','  stop_threads();\n  ++worker_epoch;','  stop_threads();\n  if(has_caught_failure()) throw runtime_error("MPC failed epoch cannot retire");\n  // Collective completion is after local protocol checks, joins and stack wipe.\n  vector<octetStream> completion(N.num_players());\n  octetStream expected; expected.store(worker_epoch);\n  completion[my_number]=expected;\n  P->Broadcast_Receive(completion); P->Check_Broadcast();\n  for(const auto& item:completion)\n    if(not item.equals(expected)) throw runtime_error("MPC epoch completion mismatch");\n  ++worker_epoch;')
# The failure API never reports normal retirement success.
s=(DEST/'Processor/Machine.hpp').read_text();start=s.index('void Machine<sint, sgf2n>::retire_worker_epoch(');brace=s.index('{',start)
edit('Processor/Machine.hpp',s[start:brace+1],s[start:brace+1]+'\n  if(has_caught_failure()) throw runtime_error("MPC failed epoch cannot retire");\n  tls_caught_failure::OnUnwind retire_failure([this]() noexcept { report_caught_failure(); cleanup_caught_failure(); });')
marker='template<class sint, class sgf2n>\npair<DataPositions, NamedCommStats> Machine<sint, sgf2n>::stop_threads()'
methods='''template<class sint, class sgf2n>
void Machine<sint, sgf2n>::report_caught_failure() noexcept {
  caught_failure.store(true);
  tls_caught_failure::runtime_sockets.cancel();
  for(auto* queue:queues) if(queue) queue->cancel_failure();
}
template<class sint, class sgf2n>
void Machine<sint, sgf2n>::cleanup_caught_failure() noexcept {
  if(caught_cleanup_complete) return;
  report_caught_failure();
  bool joined=true;
  for(auto thread:threads) if(pthread_join(thread,nullptr)!=0) joined=false;
  if(not joined) {
    // Quarantine mappings rather than wiping a potentially live stack.
    for(auto& stack:worker_stacks) stack.release();
    fprintf(stderr,"MPC failure category=join\\n");
    return;
  }
  for(auto* queue:queues) delete queue;
  queues.clear(); threads.clear(); worker_stacks.clear(); tinfo.clear();
  active_threads.clear(); nthreads=0;
  M2.resize_s(0); M2.resize_c(0); Mp.resize_s(0); Mp.resize_c(0);
  Mi.resize_s(0); Mi.resize_c(0); bit_memories.MS.clear(); bit_memories.MC.clear();
  auto* previous=P;P=nullptr;delete previous;
  caught_cleanup_complete=true;
}

'''
edit('Processor/Machine.hpp',marker,methods+marker)
# Per-thread RAII owners. Unwind guard fires before any owners are destroyed.
n='Processor/Online-Thread.hpp';include(n,'FailureScope.h')
edit(n,'  Player* player;','''  std::unique_ptr<Player> player_owner;
  std::unique_ptr<typename sgf2n::MAC_Check> mc2_owner;
  std::unique_ptr<typename sint::MAC_Check> mcp_owner;
  std::unique_ptr<Processor<sint,sgf2n>> processor_owner;
  tls_caught_failure::OnUnwind worker_failure([&]() noexcept { machine.report_caught_failure(); });
  Player* player;''')
edit(n,'  Player& P = *player;','  player_owner.reset(player);\n  Player& P = *player;')
edit(n,'      MC2 = new typename sgf2n::Direct_MC(*(tinfo->alpha2i));','      MC2 = new typename sgf2n::Direct_MC(*(tinfo->alpha2i)); mc2_owner.reset(MC2);')
edit(n,'      MCp = new typename sint::Direct_MC(*(tinfo->alphapi));','      MCp = new typename sint::Direct_MC(*(tinfo->alphapi)); mcp_owner.reset(MCp);')
edit(n,'      MC2 = new typename sgf2n::MAC_Check(*(tinfo->alpha2i), opts.opening_sum, opts.max_broadcast);','      MC2 = new typename sgf2n::MAC_Check(*(tinfo->alpha2i), opts.opening_sum, opts.max_broadcast); mc2_owner.reset(MC2);')
edit(n,'      MCp = new typename sint::MAC_Check(*(tinfo->alphapi), opts.opening_sum, opts.max_broadcast);','      MCp = new typename sint::MAC_Check(*(tinfo->alphapi), opts.opening_sum, opts.max_broadcast); mcp_owner.reset(MCp);')
edit(n,'  auto& Proc = *processor;','  processor_owner.reset(processor);\n  auto& Proc = *processor;')
edit(n,'  delete processor;','  processor_owner.reset(); processor=nullptr;\n  if(machine.has_caught_failure()) throw runtime_error("MPC teardown failed");')
edit(n,'  delete MC2;\n  delete MCp;\n  delete player;','  mc2_owner.reset(); mcp_owner.reset(); player_owner.reset();')
s=(DEST/n).read_text();a=s.index('  if (OnlineOptions::singleton.has_option("throw_exceptions"))');b=s.index('  return 0;',a)
edit(n,s[a:b],'''  try { ti.Main_Func_With_Purge(); }
  catch (...) {
    ti.machine->report_caught_failure();
    fprintf(stderr,"MPC failure category=worker\\n");
  }
''')
# Compile-time-only public fault injection for the isolated fixture executable.
edit(n,'      program = job.prognum;','''      program = job.prognum;
#ifdef TLS_CAUGHT_FAILURE_TEST_HOOKS
      if(program>=0 && tls_caught_failure::fixture_fault_stage==1)
        throw runtime_error("fixture protocol failure");
#endif''')
edit(n,'  auto exe_stats = Proc.stats;','''#ifdef TLS_CAUGHT_FAILURE_TEST_HOOKS
  if(tls_caught_failure::fixture_fault_stage==2)
    throw runtime_error("fixture teardown failure");
#endif
  auto exe_stats = Proc.stats;''')
# Destructor cannot initiate checks while unwinding or throw across noexcept.
edit('Processor/Processor.hpp','  share_thread.post_run();','''  if(not machine.has_caught_failure()) {
    try { share_thread.post_run(); }
    catch (...) { machine.report_caught_failure(); }
  }''')
edit('Protocols/MAC_Check_Base.hpp','            cout << check << " != " << value << endl;','            cerr << "MPC failure category=check\\n";')
patch=''
for n,(a,b) in changes.items():
 (DEST/n).write_text(b);patch+=''.join(difflib.unified_diff(a.splitlines(True),b.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
if VERIFY:
 for n in list(changes)+['Tools/SocketCancellation.h','Tools/FailureScope.h']:
  assert (DEST/n).read_bytes()==(ACTUAL/n).read_bytes(),('overlay mismatch',n)
 DEST=ACTUAL
 print('exact generated source matches isolated candidate')
(WORK/'caught-failure.patch').write_text(patch)
(WORK/'runtime-prepare.json').write_text(json.dumps(dict(candidate_only=True,validated=False,base_source_sha256=identity,overlay_sha256=hashlib.sha256(patch.encode()).hexdigest(),destination=str(DEST.relative_to(ROOT))),indent=2)+'\n')
print(DEST)
