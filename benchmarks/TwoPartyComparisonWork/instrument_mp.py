"""Public-only diagnostic overlay for unencrypted comparison sockets.

Counts successful socket payload bytes, including framing/startup; excludes
TCP/IP headers/retransmissions. No protocol parameters or data are changed.
"""
import hashlib
import json
import pathlib
import tarfile

ROOT=pathlib.Path(__file__).resolve().parents[2]
MP=ROOT/'.deps/two-party-comparison/data61-MP-SPDZ-113c4e4'
paths=['Networking/sockets.h','Networking/sockets.cpp']
with tarfile.open(ROOT/'.deps/mp-spdz-v0.4.4.tar.gz') as archive:
    prefix=archive.getnames()[0]
    original={p:archive.extractfile(prefix+'/'+p).read() for p in paths}
before={p:hashlib.sha256(original[p]).hexdigest() for p in paths}
h=MP/paths[0]
s=original[paths[0]].decode()
at='inline size_t send_non_blocking(int socket, octet* msg, size_t len)'
instrument='''#include <atomic>
#include <cstdio>
struct TwoPartyTraffic {
  std::atomic<unsigned long long> sent{0}, received{0};
  ~TwoPartyTraffic() {
    std::fprintf(stderr, "EXACT_SOCKET_BYTES sent=%llu received=%llu\\n",
        sent.load(), received.load());
  }
};
inline TwoPartyTraffic two_party_traffic;

'''
assert s.count(at)==1
s=s.replace(at,instrument+at)
at='  int j = send(socket,msg,len,MSG_DONTWAIT);'
assert s.count(at)==1
s=s.replace(at,at+'\n  if (j > 0) two_party_traffic.sent += j;')
at='  ssize_t res = recv(socket, msg, len, MSG_DONTWAIT);'
assert s.count(at)==1
s=s.replace(at,at+'\n  if (res > 0) two_party_traffic.received += res;')
at='      if (recv(socket, msg, len, 0) != len)'
assert s.count(at)==1
s=s.replace(at,'      auto received = recv(socket, msg, len, 0);\n'
    '      if (received > 0) two_party_traffic.received += received;\n'
    '      if (received != len)')
if h.read_text()!=s:h.write_text(s)
p=MP/paths[1];s=original[paths[1]].decode()
at='      int j = recv(socket, msg + i, len - i, 0);'
assert s.count(at)==1
s=s.replace(at,at+'\n      if (j > 0) two_party_traffic.received += j;')
if p.read_text()!=s:p.write_text(s)
receipt={'before':before,'after':{p:hashlib.sha256((MP/p).read_bytes()).hexdigest() for p in paths},
         'scope':'successful unencrypted socket payload bytes; no TCP headers/retransmissions; no encrypted-channel coverage claim'}
(ROOT/'benchmarks/TwoPartyComparisonWork/mp-instrumentation.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
