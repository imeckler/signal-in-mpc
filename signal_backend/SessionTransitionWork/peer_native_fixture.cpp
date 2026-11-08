// PUBLIC disposable receiving-chain fixture. No key/state shares are opened;
// only secure equality against independently computed PUBLIC oracle constants.
#include "NativeNewDhReceive.h"
#include "../VariableServiceWork/NativeVariableService.h"
#include <iomanip>
#include "NativeCollective.h"
#include "Protocols/Opener.h"
#include <fstream>
#include <iostream>
using namespace tls_mpc_worker;
static PublicBytes decode(const std::string& s){PublicBytes b;for(size_t i=0;i<s.size();i+=2)b.push_back(std::stoul(s.substr(i,2),nullptr,16));return b;}
int main(int argc,char**argv){if(argc!=6)return 2;try{
 unsigned party=std::stoul(argv[1]),port=std::stoul(argv[3]);public_require(party<5&&port>1024&&port<65530,"fixture party/port");
 PinnedPrograms pinned(argv[4]);ShamirOptions::singleton={5,2};OnlineOptions options;
 options.playerno=party;options.live_prep=true;options.security_parameter=128;options.lg2=128;options.lgp=255;
 options.prime=1;options.prime<<=255;options.prime-=19;Names names(party,port,std::string(argv[2]));
 public_require(names.num_players()==5,"five parties required");Machine<tls_mpc_worker::Share> machine(names,true,options);
 Collective collective(machine.get_player(),pinned.digest(),PublicBytes(32,85));Worker worker(machine,pinned);
 signal_mpc::NativeNewDhReceive receiver(machine,worker,pinned);
 auto public_bits=[&](const PublicBytes& raw){auto out=worker.allocate(raw.size()*8);for(size_t i=0;i<out.size();++i){
  out[i][0]=tls_mpc_worker::Bit::constant((raw[i/8]>>(7-i%8))&1,party,machine.get_bit_mac_key());}return out;};
 auto slice=[](const tls_mpc_worker::Bits& b,size_t off,size_t n){public_require(off<=b.size()/8&&n<=b.size()/8-off,"fixture slice");return tls_mpc_worker::Bits(b.begin()+8*off,b.begin()+8*(off+n));};
 auto append=[](tls_mpc_worker::Bits& out,const tls_mpc_worker::Bits& more){out.insert(out.end(),more.begin(),more.end());};
 auto compare=[&](tls_mpc_worker::Bits actual,tls_mpc_worker::Bits expected){append(actual,expected);auto result=worker.allocate(8);
  std::vector<FunctionArgument> args={{1,actual.function_argument()},{1,result.function_argument()}};
  const std::string name="signal_new_dh_fixture_equal_4864";pinned.verify_function(name,args);FunctionArgument ignored;machine.run_function(name,ignored,args);
  Opener<tls_mpc_worker::Bit> opener(machine.get_player(),machine.get_bit_mac_key());opener.init_open();opener.prepare_open(result[0][0]);opener.exchange();
  auto ok=opener.finalize_open().get();opener.Check();public_require(ok==1,"native receive equality rejected");
 };
 auto open_fixture=[&](const tls_mpc_worker::Bits& bits){Opener<tls_mpc_worker::Bit> opener(machine.get_player(),machine.get_bit_mac_key());opener.init_open();
  for(auto& b:bits)opener.prepare_open(b[0]);opener.exchange();PublicBytes out(bits.size()/8);
  for(size_t i=0;i<bits.size();++i)out[i/8]|=(opener.finalize_open().get()&1)<<(7-i%8);opener.Check();return out;
 };
 std::ifstream file(argv[5]);std::string initial;file>>initial;auto init=decode(initial);public_require(init.size()==982,"native peer init dimensions");
 auto all=public_bits(init);auto state=slice(all,0,525),ids=slice(all,525,64),prefix=slice(all,589,292),sendpq=slice(all,881,44),metadata=slice(all,925,57);
 signal_mpc::NativeVariableService service(machine,worker,pinned);signal_mpc::VariableShape shape(260,80,false,false);
 auto receive=[&](const tls_mpc_worker::Bits& old,const PublicBytes& wire){public_require(wire.size()<=256,"native peer wire capacity");
  PublicBytes encoded{255,static_cast<unsigned char>(wire.size()>>8),static_cast<unsigned char>(wire.size())};encoded.insert(encoded.end(),wire.begin(),wire.end());encoded.resize(259);
  auto input=old;append(input,ids);append(input,public_bits(encoded));return receiver.evaluate(std::move(input));
 };
 std::string wire_hex,plain_hex,reply_hex;size_t round=0;
 while(std::cin>>wire_hex>>plain_hex>>reply_hex){public_require(round<2,"native peer round bound");auto wire=decode(wire_hex),plain=decode(plain_hex),reply=decode(reply_hex);
  public_require(plain.size()==80&&reply.size()==80,"native peer text size");
  if(round==0){
   for(size_t rejection=0;rejection<3;++rejection){auto bad=wire;auto old=state;
    if(rejection==0)bad.back()^=1;
    if(rejection==1){public_require(bad.size()>=36,"point fixture bounds");std::fill(bad.begin()+4,bad.begin()+36,0);}
    if(rejection==2){auto max=public_bits(PublicBytes(4,255));std::copy(max.begin(),max.end(),old.begin()+8*521);}
    auto rejected=receive(old,bad);auto expected=public_bits(PublicBytes{0});append(expected,old);append(expected,public_bits(PublicBytes(82,0)));compare(std::move(rejected),std::move(expected));
   }
   std::cout<<"REJECTIONS passed\n"<<std::flush;
  }
  auto output=receive(state,wire);state=slice(output,1,525); // selected state committed before reply.
  // Only status and plaintext are compared; every state/key stays unopened.
  auto observed=slice(output,0,1);append(observed,public_bits(PublicBytes(525,0)));append(observed,slice(output,526,82));
  PublicBytes expected{255};expected.resize(526);expected.push_back(0);expected.push_back(80);expected.insert(expected.end(),plain.begin(),plain.end());compare(std::move(observed),public_bits(expected));
  auto call=prefix;append(call,public_bits(PublicBytes{68}));append(call,slice(state,128,8));append(call,slice(state,64,32));append(call,slice(state,96,32));
  append(call,slice(sendpq,8,36));append(call,slice(sendpq,0,8));append(call,public_bits(PublicBytes{0}));append(call,slice(ids,32,32));append(call,slice(ids,0,32));append(call,public_bits(reply));
  auto meta=metadata;PublicBytes ts(8);uint64_t time=1900000000100ULL+round;for(int i=7;i>=0;--i){ts[i]=time&255;time>>=8;}auto tb=public_bits(ts);std::copy(tb.begin(),tb.end(),meta.begin()+32*8);append(call,meta);
  public_require(call.size()==shape.input_bytes()*8,"native reply service dimensions");auto sent=service.evaluate(shape,std::move(call));
  auto next=state;auto ck=slice(sent,1,32),ctr=slice(sent,33,4);std::copy(ck.begin(),ck.end(),next.begin()+96*8);std::copy(ctr.begin(),ctr.end(),next.begin()+128*8);
  auto nextpq=slice(sendpq,0,8);append(nextpq,slice(sent,37,36));state=std::move(next);sendpq=std::move(nextpq);
  auto id=slice(sent,73,8);std::copy(id.begin(),id.end(),metadata.begin()+40*8);
  auto payload=slice(sent,0,1);append(payload,slice(sent,81,2+shape.frame_capacity()));auto final=open_fixture(payload);
  public_require(final[0]==255,"native reply rejected");size_t n=size_t(final[1])*256+final[2];public_require(n<=shape.frame_capacity(),"native reply length");
  std::cout<<"FRAME "<<round<<' ';for(size_t i=3;i<n+3;++i)std::cout<<std::hex<<std::setw(2)<<std::setfill('0')<<unsigned(final[i]);std::cout<<std::dec<<'\n'<<std::flush;++round;
 }
 public_require(round==2,"two native peer ratchets required");std::cout<<"native receive peer fixture passed\n";
 return 0;
 }catch(const std::exception&){std::cerr<<"native receiving peer fixture failed\n";return 1;}}
