// PUBLIC synthetic own-evaluation bytes; never aggregate keys/private values.
#include "OwnShareBox.h"
#include <iostream>
using namespace signal_mpc::recovery;
size_t checks=0;void check(bool b){require(b,"own archive check failed");++checks;}
template<class F>void rejects(F&& f){try{f();}catch(const std::exception&){++checks;return;}throw std::runtime_error("own archive rejection missing");}
int main(int argc,char**){try{
 std::array<unsigned char,64> key;for(size_t i=0;i<key.size();++i)key[i]=i+1;OwnShareBox box(key);
 for(size_t count:{size_t(1),size_t(8),size_t(513)}){
  ShareDomain d{};d.party=3;d.epoch=4;d.slot=7;d.bit_count=count;d.context.fill(1);d.membership.fill(2);d.manifest.fill(3);d.schema.fill(4);d.sharing_epoch.fill(5);
  SecretBytes bytes(count*16);for(size_t i=0;i<bytes.size();++i)bytes.data()[i]=(i*17+count)%256;
  QuarantinedEvaluations local(std::move(bytes));auto sealed=box.seal(d,local);auto opened=box.open_quarantined(d,sealed);
  check(opened.bit_count()==count);check(CRYPTO_memcmp(opened.local_bytes().data(),local.local_bytes().data(),count*16)==0);
  check(box.seal(d,local)==sealed); // Deterministic SIV, no crash-sensitive nonce counter.
  for(auto offset:{size_t(0),d.header().size(),sealed.size()-1}){auto bad=sealed;bad[offset]^=1;rejects([&]{box.open_quarantined(d,bad);});}
  auto short_box=sealed;short_box.pop_back();rejects([&]{box.open_quarantined(d,short_box);});
  auto long_box=sealed;long_box.push_back(0);rejects([&]{box.open_quarantined(d,long_box);});
  for(unsigned change=0;change<9;++change){auto wrong=d;switch(change){case 0:wrong.party=2;break;case 1:++wrong.epoch;break;case 2:++wrong.slot;break;case 3:++wrong.bit_count;break;case 4:wrong.context[0]^=1;break;case 5:wrong.membership[0]^=1;break;case 6:wrong.manifest[0]^=1;break;case 7:wrong.schema[0]^=1;break;case 8:wrong.sharing_epoch[0]^=1;break;}rejects([&]{box.open_quarantined(wrong,sealed);});}
  auto wrong_key=key;wrong_key[7]^=1;OwnShareBox other(wrong_key);rejects([&]{other.open_quarantined(d,sealed);});
  if(argc>1){auto print=[](const Bytes& b){const char* hex="0123456789abcdef";for(auto x:b)std::cout<<hex[x>>4]<<hex[x&15];};std::cout<<"VECTOR "<<count<<' ';print(d.header());std::cout<<' ';print(sealed);std::cout<<'\n';}
  auto moved=std::move(opened);check(moved.bit_count()==count);
 }
 ShareDomain bad{};rejects([&]{bad.header();});std::cout<<checks<<" own-share archive/quarantine checks passed\n";return 0;
 }catch(const std::exception& e){std::cerr<<e.what()<<'\n';return 1;}}
