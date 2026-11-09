#pragma once
#include "CertifiedArchiveGate.h"
namespace signal_mpc::recovery {
// Canonical public certificate persistence/wire codec. Verifies real member
// signatures on decode; no secret archive or private validity interpretation.
inline Bytes encode_phase(const Epoch& epoch,CertifiedPhase phase){
 require(certificate(epoch,phase.proposal,phase.votes),"invalid phase certificate");
 std::sort(phase.votes.begin(),phase.votes.end(),[](auto& a,auto& b){return a.party<b.party;});
 auto out=label("SIGNAL-RECOVERY-CERT-1");auto message=phase.proposal.encode(epoch);u64(out,message.size());out.insert(out.end(),message.begin(),message.end());out.push_back(phase.votes.size());
 for(auto& vote:phase.votes){out.push_back(vote.party);out.insert(out.end(),vote.signature.begin(),vote.signature.end());}return out;
}
inline CertifiedPhase decode_phase(const Epoch& epoch,const Bytes& bytes){
 auto header=label("SIGNAL-RECOVERY-CERT-1");require(bytes.size()>=header.size()+8,"truncated phase certificate");
 require(std::equal(header.begin(),header.end(),bytes.begin()),"phase certificate format");size_t at=header.size();auto size=read64(bytes.data()+at);at+=8;
 auto prefix=label("tls-mpc-signal-recovery-vote-v1");append(prefix,epoch.digest());
 const auto expected=prefix.size()+1+8+32*9;
 require(size==expected&&bytes.size()>=at+size+1,"phase certificate length");
 require(std::equal(prefix.begin(),prefix.end(),bytes.begin()+at),"phase certificate epoch");at+=prefix.size();
 Proposal p{};p.phase=Phase(bytes[at++]);p.slot=read64(bytes.data()+at);at+=8;
 auto digest=[&](){Digest d;std::copy_n(bytes.begin()+at,32,d.begin());at+=32;return d;};
 p.context=digest();p.parent=digest();p.attempt=digest();p.manifest=digest();for(auto& d:p.bundles)d=digest();
 auto count=bytes[at++];require(count>=4&&count<=5&&bytes.size()==at+65*count,"phase certificate vote count");
 std::vector<Vote> votes;for(unsigned i=0;i<count;++i){Vote v{};v.party=bytes[at++];require(i==0||votes.back().party<v.party,"phase certificate signer order");std::copy_n(bytes.begin()+at,64,v.signature.begin());at+=64;votes.push_back(v);}
 CertifiedPhase result{p,votes};require(certificate(epoch,p,votes),"phase certificate signature");require(encode_phase(epoch,result)==bytes,"phase certificate noncanonical");return result;
}
}
