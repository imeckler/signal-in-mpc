/*
 * ccd-party.cpp
 *
 */

#include "GC/MaliciousCcdSecret.h"
#include "LongFieldBit.h"
#include "emit_backend_totals.h"
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

int main(int argc, const char** argv)
{
    require_component_security(argc,argv);
    ez::ezOptionParser opt;
    ShamirOptions::singleton = {opt, argc, argv};
    if(ShamirOptions::singleton.nparties!=5||ShamirOptions::singleton.threshold!=2)throw std::runtime_error("component requires five parties/threshold two");
    OnlineOptions opts(opt, argc, argv);
    gf2n_long::init_minimum(opts.security_parameter);
    if(opts.security_parameter!=128)throw std::runtime_error("CCD component requires security128");
    GC::ShareParty<GC::MaliciousCcdSecret<gf2n_long>>(argc, argv, opt);
    emit_backend_totals("ccd128");
}
