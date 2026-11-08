#pragma once
#include <array>
#include <atomic>
#include <chrono>
#include <cstdint>
#include <stdexcept>
// Optional isolated diagnostic overlay: public protocol work only. Domains and
// phases follow static call sites, never shares or secret-dependent decisions.
namespace tls_public_diagnostics {
enum class Domain:unsigned {unattributed,field,binary};
enum class Phase:unsigned {unattributed,online,preprocessing};
struct Context {Domain domain=Domain::unattributed;Phase phase=Phase::unattributed;};
inline thread_local Context context;
inline std::array<std::atomic<uint64_t>,9> bytes{},nanoseconds{},calls{};
inline std::atomic<uint64_t> prepare_ns{},load_ns{},prepare_calls{},load_calls{};
struct Snapshot {std::array<uint64_t,9> bytes{},nanoseconds{},calls{};uint64_t prepare_ns=0,load_ns=0,prepare_calls=0,load_calls=0;};
inline unsigned index(Context value){return unsigned(value.domain)*3+unsigned(value.phase);}
inline Snapshot snapshot(){Snapshot result;for(unsigned i=0;i<9;++i){result.bytes[i]=bytes[i].load();result.nanoseconds[i]=nanoseconds[i].load();result.calls[i]=calls[i].load();}
 result.prepare_ns=prepare_ns.load();result.load_ns=load_ns.load();result.prepare_calls=prepare_calls.load();result.load_calls=load_calls.load();return result;}
inline void sent_bytes(uint64_t count){bytes[index(context)].fetch_add(count,std::memory_order_relaxed);}
class Scope {
 Context previous;unsigned category;std::chrono::steady_clock::time_point started;
public:
 Scope(Domain domain,Phase phase):previous(context),started(std::chrono::steady_clock::now()){
  // Nested online arithmetic used by preprocessing remains preprocessing.
  if(previous.phase==Phase::preprocessing)phase=Phase::preprocessing;
  context={domain,phase};category=index(context);calls[category].fetch_add(1,std::memory_order_relaxed);
 }
 ~Scope(){context=previous;nanoseconds[category].fetch_add(std::chrono::duration_cast<std::chrono::nanoseconds>(std::chrono::steady_clock::now()-started).count(),std::memory_order_relaxed);}
};
class LoadTimer {
 std::atomic<uint64_t>& target;std::chrono::steady_clock::time_point started;
public:
 LoadTimer(bool load):target(load?load_ns:prepare_ns),started(std::chrono::steady_clock::now()){
  (load?load_calls:prepare_calls).fetch_add(1,std::memory_order_relaxed);
 }
 ~LoadTimer(){target.fetch_add(std::chrono::duration_cast<std::chrono::nanoseconds>(std::chrono::steady_clock::now()-started).count(),std::memory_order_relaxed);}
};
}
