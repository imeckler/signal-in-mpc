#include "../NativeWorker.h"
#include "../../signal_backend/RecoveryWork/AccountLayoutV2.h"
#include <cassert>
#include <iostream>
using namespace tls_mpc_worker;using namespace signal_mpc::recovery;
int main(){gf2n_long::init_field(128);typename tls_mpc_worker::Bit::mac_key_type mac{};size_t checks=0;
 auto constants=[&](unsigned byte){tls_mpc_worker::Bits result(8,std::vector<tls_mpc_worker::Bit>(1,single_cell_constant<tls_mpc_worker::Bit>(0,0,mac)));for(unsigned i=0;i<8;++i)result[i][0]=single_cell_constant<tls_mpc_worker::Bit>((byte>>(7-i))&1,0,mac);return result;};
 auto layout=AccountLayoutV2(1);std::vector<tls_mpc_worker::Bits> sections;
 auto zero=single_cell_constant<tls_mpc_worker::Bit>(0,0,mac);
 for(unsigned tag=1;tag<=4;++tag)sections.emplace_back(8*layout.global_width(tag),std::vector<tls_mpc_worker::Bit>{zero});
 for(unsigned tag=10;tag<=16;++tag)sections.emplace_back(8*layout.conversation_width(tag),std::vector<tls_mpc_worker::Bit>{zero});
 OwnedAccountV2 account(layout,std::move(sections));
 for(auto entry:std::vector<std::pair<unsigned,unsigned>>{{16,3},{14,255},{15,1}}){
  auto value=tls_mpc_worker::Bits(account.conversation(0,entry.first));auto prefix=constants(entry.second);std::copy(prefix.begin(),prefix.end(),value.begin());account.replace_conversation(0,entry.first,std::move(value));NativeOwnShareArchive::require_cells(account.conversation(0,entry.first));++checks;
 }
 for(unsigned party=0;party<5;++party)for(unsigned value:{0u,1u}){
  auto bit=single_cell_constant<tls_mpc_worker::Bit>(value,party,mac);assert(bit.get_regs().size()==1);++checks;
  tls_mpc_worker::Bits one(1,std::vector<tls_mpc_worker::Bit>{bit});NativeOwnShareArchive::require_cells(one);++checks;
 }
 for(unsigned byte:{0u,1u,3u,255u}){auto data=constants(byte);NativeOwnShareArchive::require_cells(data);auto copy=data;NativeOwnShareArchive::require_cells(copy);std::vector<FunctionArgument> args={{1,data.function_argument()}};assert(args[0].get_type_string()=="sbv:[8x1]");checks+=3;}
 auto packed=tls_mpc_worker::Bit::constant(1,0,mac);assert(packed.get_regs().size()==64);bool rejected=false;try{NativeOwnShareArchive::require_cells(tls_mpc_worker::Bits(1,std::vector<tls_mpc_worker::Bit>{packed}));}catch(...){rejected=true;}assert(rejected);++checks;
 rejected=false;try{single_cell_constant<tls_mpc_worker::Bit>(2,0,mac);}catch(...){rejected=true;}assert(rejected);++checks;
 std::cout<<checks<<" public exact-cell construction/interface checks passed\n";
}
