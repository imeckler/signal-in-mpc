#pragma once
#include "OwnShareBox.h"
#include "NativeWorker.h"
#include <type_traits>
namespace signal_mpc::recovery {
namespace detail {
inline void encode_own_evaluation(unsigned char* out,const gf2n_long& value){
 std::memset(out,0,16);for(size_t bit=0;bit<128;++bit)out[bit/8]|=value.get_bit(bit)<<(bit%8);
}
}
// Captures this party's LOCAL polynomial evaluations only. Never interpolates,
// opens a bit/key, or manufactures restored Bits. The only returned artifact
// is encrypted. Decryption stays quarantined until fresh private-MPC import.
class NativeOwnShareArchive {
public:
 static void require_cells(const tls_mpc_worker::Bits& state){
  for(size_t i=0;i<state.size();++i)
   require(state[i].size()==1&&state[i][0].get_regs().size()==1,"archive runtime cell shape");
 }
 static Bytes seal(const ShareDomain& domain,const tls_mpc_worker::Bits& state,
     const Player& player,const OwnShareBox& box){
  using Part=typename tls_mpc_worker::Bit::part_type;
  static_assert(std::is_same_v<tls_mpc_worker::Bit,GC::MaliciousCcdSecret<gf2n_long>>, "CCD secret type only");
  static_assert(std::is_same_v<Part,GC::MaliciousCcdShare<gf2n_long>>, "CCD part type only");
  static_assert(std::is_same_v<typename Part::open_type,gf2n_long>,"CCD128 archive representation only");
  domain.header();require(player.num_players()==5&&unsigned(player.my_num())==domain.party,
    "archive runtime member mismatch");
  require(ShamirOptions::s().threshold==2&&gf2n_long::degree()==128,"archive runtime sharing mismatch");
  require(state.size()==domain.bit_count,"archive runtime bit count mismatch");require_cells(state);SecretBytes local(state.size()*16);
  for(size_t i=0;i<state.size();++i){
   const auto& own=static_cast<const gf2n_long&>(state[i][0].get_regs()[0]);
   detail::encode_own_evaluation(local.data()+16*i,own);
  }
  QuarantinedEvaluations captured(std::move(local));return box.seal(domain,captured);
 }
};
}
