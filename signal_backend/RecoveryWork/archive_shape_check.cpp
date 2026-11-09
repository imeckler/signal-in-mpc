// Representation admission only, local PUBLIC constants. No keys/MPC opens.
#include "NativeOwnShareArchive.h"
#include <iostream>
using namespace signal_mpc::recovery;
using Secret=tls_mpc_worker::Bit;
static tls_mpc_worker::Bits cells(Secret value){return {1,std::vector<Secret>{value}};}
int main(){try{gf2n_long::init_field(128);typename Secret::mac_key_type mac{};size_t checks=0;
 auto rejects=[&](const tls_mpc_worker::Bits& value){try{NativeOwnShareArchive::require_cells(value);}catch(const std::runtime_error&){++checks;return;}throw std::runtime_error("malformed archive cells admitted");};
 for(int value: {0,1}){
  auto one=Secret::constant(value,0,mac,1);auto packed=Secret::constant(value,0,mac);
  require(one.get_regs().size()==1&&packed.get_regs().size()==64,"fixture constant widths");++checks;
  NativeOwnShareArchive::require_cells(cells(one));++checks;rejects(cells(packed));
  auto two=one;two.resize_regs(2);rejects(cells(two));
  tls_mpc_worker::Bits outer(1,std::vector<Secret>{one,one});rejects(outer);
  tls_mpc_worker::Bits empty(1,std::vector<Secret>{});rejects(empty);
 }
 std::cout<<checks<<" archive exact-cell admission checks passed\n";return 0;
 }catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 1;}}
