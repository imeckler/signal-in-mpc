#pragma once
// Protocol wiring derived from pinned MP-SPDZ Protocols/MaliciousShamirShare.h.
// Keeps its malicious Shamir protocols and changes the mixed binary companion
// to MaliciousCcdSecret<gf2n_long>. No upstream or refresh-backend source patch.
// This is an unverified backend configuration, not a new MPC security proof.
#include "Protocols/MaliciousShamirShare.h"
#include "GC/MaliciousCcdSecret.h"
#include "Math/gf2n.h"

namespace tls_mpc_worker {
template<class T> class StrongShamirShare : public ShamirShare<T> {
    using super=ShamirShare<T>;
    using This=StrongShamirShare<T>;
public:
    using BasicProtocol=Beaver<This>;
    using MAC_Check=MaliciousShamirMC<This>;
    using Direct_MC=MAC_Check;
    using Input=ShamirInput<This>;
    using PO=MaliciousShamirPO<This>;
    using PrivateOutput=SpecificPrivateOutput<This>;
    using Honest=ShamirShare<T>;
    using LivePrep=MaliciousRepPrepWithBits<This>;
    using TriplePrep=MaliciousRepPrep<This>;
    using random_type=T;
    using Protocol=MaybeHemi<This>;
    using MatrixPrep=DummyMatrixPrep<This>;
    using mac_key_type=T;
    using bit_type=GC::MaliciousCcdSecret<gf2n_long>;
    static const bool malicious=true;
    static std::string type_short(){return "M128"+super::type_short();}
    static std::string alt(){return "";}
    StrongShamirShare()=default;
    template<class U> StrongShamirShare(const U& value):super(value){}
};
}
