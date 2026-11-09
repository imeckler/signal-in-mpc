// PUBLIC disposable component fixture; no normal provider or account admission.
// Actual service+computed binding+store transaction. Only final disposable wire
// and aggregate state-equality flag are opened. Not full-account recovery.
#include "NativeCanonicalSendOwner.h"
#include "NativeOwnShareArchive.h"
#include "CiphertextStore.h"
#include "NativeCollective.h"
#include "Protocols/Opener.h"
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <iostream>
using namespace tls_mpc_worker;
using namespace signal_mpc;
using namespace signal_mpc::recovery;
static PublicBytes decode(const std::string& s){PublicBytes b;for(size_t i=0;i<s.size();i+=2)b.push_back(std::stoul(s.substr(i,2),nullptr,16));return b;}
static tls_mpc_worker::Bits clone(const tls_mpc_worker::Bits& b){return {b.begin(),b.end()};}
static void append(tls_mpc_worker::Bits& a,const tls_mpc_worker::Bits& b){a.insert(a.end(),b.begin(),b.end());}
struct Tx {
 Machine<tls_mpc_worker::Share>& machine;const PinnedPrograms& pin;OwnShareBox& box;CiphertextStore& files;unsigned party;size_t reserve_count=0,commit_count=0;
 void persist(unsigned phase,const tls_mpc_worker::Bits& values){ShareDomain d{};d.party=party;d.epoch=1;d.slot=commit_count+1;d.bit_count=values.size();d.context.fill(71);d.membership.fill(72);d.schema.fill(phase);d.sharing_epoch.fill(73);std::copy_n(pin.digest().begin(),32,d.manifest.begin());
  // This is this party's local evaluation archive, never opened/reconstructed.
  auto cipher=NativeOwnShareArchive::seal(d,values,machine.get_player(),box);files.put(cipher);
 }
 void reserve(const std::vector<VariableShape>& shapes,const std::vector<NativeCanonicalSendOwner::Prestate>& states){
  public_require(shapes.size()==1&&states.size()==1&&reserve_count==commit_count,"fixture reserve ordering");
  auto values=clone(states[0].record);append(values,states[0].selected);append(values,states[0].call);persist(1,values);++reserve_count;
 }
 void commit(const std::vector<VariableShape>& shapes,const std::vector<NativeCanonicalSendOwner::Poststate>& states){
  public_require(shapes.size()==1&&states.size()==1&&reserve_count==commit_count+1,"fixture commit ordering");
  auto values=clone(states[0].record);append(values,states[0].selected);append(values,states[0].service);append(values,states[0].outbox);append(values,states[0].request_id);persist(2,values);++commit_count;
 }
};
int main(int argc,char**argv){if(argc!=6)return 2;try{
 unsigned party=std::stoul(argv[1]),port=std::stoul(argv[3]);public_require(party<5&&port>1024&&port<65530,"fixture member/port");
 PinnedPrograms pin(argv[4]);ShamirOptions::singleton={5,2};OnlineOptions opts;opts.playerno=party;opts.live_prep=true;opts.security_parameter=128;opts.lg2=128;opts.lgp=255;opts.prime=1;opts.prime<<=255;opts.prime-=19;
 Names names(party,port,std::string(argv[2]));Machine<tls_mpc_worker::Share> machine(names,true,opts);Collective collective(machine.get_player(),pin.digest(),PublicBytes(32,71));Worker worker(machine,pin);
 auto public_bits=[&](const PublicBytes& bytes){auto out=worker.allocate(bytes.size()*8);for(size_t i=0;i<out.size();++i)out[i][0]=tls_mpc_worker::Bit::constant((bytes[i/8]>>(7-i%8))&1,party,machine.get_bit_mac_key(),1);return out;};
 auto open_fixture=[&](const tls_mpc_worker::Bits& bits){Opener<tls_mpc_worker::Bit> open(machine.get_player(),machine.get_bit_mac_key());open.init_open();for(const auto& b:bits)open.prepare_open(b[0]);open.exchange();PublicBytes bytes(bits.size()/8);for(size_t i=0;i<bits.size();++i)bytes[i/8]|=(open.finalize_open().get()&1)<<(7-i%8);open.Check();return bytes;};
 std::ifstream in(argv[5]);std::string encoded;auto read=[&](){public_require(bool(in>>encoded),"fixture truncated");return decode(encoded);};
 auto record=read(),selected=read(),input=read();VariableShape shape(260,80,false,false);public_require(input.size()==611&&record.size()==5550&&selected.size()==525,"fixture profile");
 auto directory=std::string(argv[5])+"-party"+std::to_string(party);std::filesystem::create_directory(directory);
 std::array<unsigned char,64> key;for(size_t i=0;i<key.size();++i)key[i]=i+party*7;OwnShareBox box(key);CiphertextStore files(directory);Tx tx{machine,pin,box,files,party};NativeVariableService service(machine,worker,pin);NativeRecordBinding binding(machine,worker,pin);
 NativeCanonicalSendOwner owner(shape,public_bits(record),public_bits(selected),public_bits(input),directory+"/fence",service,binding);
 for(size_t step=0;step<2;++step){auto payload=read(),timestamp=read(),id=read(),expected=read();public_require(expected.size()==6686,"fixture expected view dimensions");
  auto output=owner.produce(public_bits(payload),public_bits(timestamp),public_bits(id),tx);
  auto actual=clone(owner.record_snapshot());append(actual,owner.selected_snapshot());append(actual,owner.service_snapshot());append(actual,public_bits(expected));auto flag=worker.allocate(8);std::vector<FunctionArgument> args={{1,actual.function_argument()},{1,flag.function_argument()}};pin.verify_function("signal_canonical_fixture_equal_53488",args);FunctionArgument ignored;machine.run_function("signal_canonical_fixture_equal_53488",ignored,args);public_require(open_fixture(flag)==PublicBytes(1,255),"private canonical/store state mismatch");
  auto wire=open_fixture(output.payload);public_require(wire[0]==255,"private owner rejected supported state");size_t length=256*wire[1]+wire[2];public_require(length<=shape.frame_capacity(),"fixture private length bounds");std::cout<<"FRAME "<<step<<' ';for(size_t i=3;i<3+length;++i)std::cout<<std::hex<<std::setw(2)<<std::setfill('0')<<unsigned(wire[i]);std::cout<<std::dec<<'\n';
  owner.response_complete(output.ticket); // explicit synthetic component ACK
 }
 public_require(tx.reserve_count==2&&tx.commit_count==2,"fixture transaction count");owner.close();std::cout<<"canonical owner fixture passed\n";return 0;
 }catch(const std::exception&e){std::cerr<<"canonical owner fixture failed: "<<e.what()<<'\n';return 1;}}
