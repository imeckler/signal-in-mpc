#pragma once
// Candidate VALUE re-sharing only. Certificate/fresh-head/provider admission is
// separate. Arbitrary archived GF128 evaluations NEVER enter a bit-only mask.
#include "NativeOwnShareArchive.h"
#include "Processor/Processor.hpp"
#include "Protocols/MaliciousRepPrep.hpp"
#include "Protocols/Beaver.hpp"
#include "Protocols/ShamirInput.hpp"
#include "Protocols/MaliciousShamirMC.hpp"
#include "Protocols/ShamirMC.hpp"
#include "Protocols/Shamir.hpp"
#include "Protocols/SemiInput.hpp"
namespace signal_mpc::recovery {
class RawFieldReadmit {
public:
 using Field=gf2n_long;
 using Share=tls_mpc_worker::StrongShamirShare<Field>;
 static_assert(std::is_same_v<typename Share::clear,Field>&&std::is_same_v<typename Share::open_type,Field>&&std::is_same_v<typename Share::random_type,Field>,"fullfield input/masking only");
private:
 Player& player_;bool failed_=false;
 DataPositions usage_;
 typename Share::MAC_Check mc_;
 typename Share::TriplePrep prep_;
 SubProcessor<Share> proc_;
 static Share add(const Share& a,const Share& b){return Share(static_cast<const Field&>(a)+static_cast<const Field&>(b));}
 static Share scale(const Share& a,unsigned c){return Share(static_cast<const Field&>(a)*Field(int(c)));}
 std::vector<Share> private_inputs(const std::vector<Field>& mine){
  // ShamirInput ignores n_bits and samples fullGF128 Scalar randomness. This
  // shares arbitrary field values, not just low bits of the stored evaluations.
  typename Share::Input input(nullptr,player_,2);
  for(unsigned party=0;party<5;++party)for(auto& value:mine){if(party==unsigned(player_.my_num()))input.add_mine(value);else input.add_other(party);}
  input.exchange();std::vector<Share> out;out.reserve(5*mine.size());
  for(unsigned party=0;party<5;++party)for(size_t i=0;i<mine.size();++i)out.push_back(input.finalize(party));
  return out;
 }
public:
 explicit RawFieldReadmit(Player& player):player_(player),usage_(player.num_players()),prep_(nullptr,usage_),proc_(mc_,prep_,player){
  require(player.num_players()==5&&ShamirOptions::s().threshold==2&&Field::degree()==128,"raw import runtime domain mismatch");
  require(!OnlineOptions::singleton.has_option("zero_seed"),"raw import insecure randomness forbidden");
 }
 // Returns fresh degree2 CCD shares ONLY after raw fullfield multiplication and
 // masked consistency/bitness checks. No constant term/key is opened to host.
 // Statistical falseaccept ≤2^-128 per batch under fresh uniform secret masks
 // and correct pinned malicious-MPC/input/opening primitives. Not a full restore.
 tls_mpc_worker::Bits values_candidate(QuarantinedEvaluations archived,const ShareDomain& domain,
     tls_mpc_worker::Worker& allocation){
  require(!failed_,"raw import candidate poisoned");
  try{
  domain.header();require(domain.party==unsigned(player_.my_num())&&domain.bit_count==archived.bit_count(),"raw import archive owner/count mismatch");
  const size_t count=archived.bit_count();require(count<=4096,"raw import candidate batch bound");std::vector<Field> mine(count);
  for(size_t i=0;i<count;++i){mine[i]=Field(0);for(size_t bit=0;bit<128;++bit)if((archived.local_bytes().data()[i*16+bit/8]>>(bit%8))&1)mine[i]+=Field(1)<<bit;}
  auto inputs=private_inputs(mine);std::vector<Share> values,checks;values.reserve(count);checks.reserve(3*count);
  for(size_t i=0;i<count;++i){auto& a=inputs[i];auto& b=inputs[count+i];auto& c=inputs[2*count+i];auto& d=inputs[3*count+i];auto& e=inputs[4*count+i];
   values.push_back(add(add(a,b),c));
   checks.push_back(add(d,add(add(scale(a,7),scale(b,9)),scale(c,15))));
   checks.push_back(add(e,add(add(scale(a,7),scale(b,8)),scale(c,14))));
  }
  // RAW GF128 operations. A Boolean compiler must not optimize x(x+1) away.
  proc_.protocol.init_mul();auto one=Share::constant(Field(1),player_.my_num());
  for(auto& value:values)proc_.protocol.prepare_mul(value,add(value,one));proc_.protocol.exchange();
  for(size_t i=0;i<count;++i)checks.push_back(proc_.protocol.finalize_mul());
  // Coefficients are secret sums of all5 fresh fullfield contributions, sampled
  // AFTER input exchange. Open just a uniformly masked aggregate, never f(0),
  // raw evaluations, syndromes, bitness products or keys.
  SeededPRNG random;std::vector<Field> local_random(checks.size());for(auto& r:local_random)r.randomize(random);
  auto randomness=private_inputs(local_random);std::vector<Share> coefficients(checks.size(),Share(Field(0)));
  for(unsigned party=0;party<5;++party)for(size_t i=0;i<checks.size();++i)coefficients[i]=add(coefficients[i],randomness[party*checks.size()+i]);
  proc_.protocol.init_mul();for(size_t i=0;i<checks.size();++i)proc_.protocol.prepare_mul(coefficients[i],checks[i]);proc_.protocol.exchange();
  Share masked(Field(0));for(size_t i=0;i<checks.size();++i)masked=add(masked,proc_.protocol.finalize_mul());
  std::vector<Field> opened;mc_.POpen(opened,std::vector<Share>{masked},player_);mc_.Check(player_);
  require(opened.size()==1&&opened[0].is_zero(),"private share consistency/bitness import failed");
  // Both are degree2 Shamir evaluations in identical GF128/n5/x1..5 domain;
  // only a successful FULLFIELD check permits the bit representation boundary.
  auto out=allocation.allocate(count);using Part=typename tls_mpc_worker::Bit::part_type;
  for(size_t i=0;i<count;++i)out[i][0]=tls_mpc_worker::Bit(Part(static_cast<const Field&>(values[i])));
  return out;
  }catch(...){failed_=true;throw;}
 }
};
}
