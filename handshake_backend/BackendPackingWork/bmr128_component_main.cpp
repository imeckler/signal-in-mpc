/*
 * mal-shamir-bmr-party.cpp
 *
 */

#include "BMR/RealProgramParty.hpp"
#include "emit_backend_totals.h"
#include "Machines/Shamir.hpp"
#include "Math/Z2k.hpp"
#include "Machines/MalRep.hpp"

int main(int argc, const char** argv)
{
	require_component_security(argc,argv);
	ez::ezOptionParser opt;
	ShamirOptions::singleton = {opt, argc, argv};
    if(ShamirOptions::singleton.nparties!=5||ShamirOptions::singleton.threshold!=2)throw std::runtime_error("component requires five parties/threshold two");
	// Upstream RealProgramParty creates a second option parser without -T.
    // Preserve the already checked global threshold and omit only its duplicate
    // CLI spelling from that parser; do not change the MPC threshold.
    std::vector<const char*> forwarded;
    for(int i=0;i<argc;++i){if(std::string(argv[i])=="-T"){++i;continue;}forwarded.push_back(argv[i]);}
    forwarded.push_back(nullptr);
    RealProgramParty<MaliciousShamirShare<gf2n_long>>(int(forwarded.size()-1),forwarded.data());
    if(ShamirOptions::singleton.nparties!=5||ShamirOptions::singleton.threshold!=2)throw std::runtime_error("component threshold changed");
    if(OnlineOptions::singleton.security_parameter!=128)throw std::runtime_error("BMR component requires security128");
    emit_backend_totals("bmr-malicious-shamir128");
}
