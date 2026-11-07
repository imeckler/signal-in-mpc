// Local native test driver: unchanged pinned malicious CCD runtime instantiated
// over GF(2^128). This selects existing protocols, not a new security proof.
#include "GC/MaliciousCcdSecret.h"
#include "GC/TinyMC.h"
#include "GC/CcdPrep.h"
#include "GC/VectorInput.h"
#include "GC/ShareParty.hpp"
#include "GC/ShareSecret.hpp"
#include "GC/ThreadMaster.hpp"
#include "GC/Secret.hpp"
#include "GC/CcdPrep.hpp"
#include "Machines/Shamir.hpp"
#include "Machines/MalRep.hpp"
#include "LongFieldBit.h"
#include <stdexcept>
int main(int argc,const char** argv) {
    ez::ezOptionParser opt;
    ShamirOptions::singleton={opt,argc,argv};
    OnlineOptions opts(opt,argc,argv);
    if(opts.security_parameter!=128)throw std::runtime_error("Signal test profile requires -S128");
    gf2n_long::init_minimum(128);
    if(gf2n_long::length()!=128)throw std::runtime_error("binary field degree");
    GC::ShareParty<GC::MaliciousCcdSecret<gf2n_long>>(argc,argv,opt);
}
