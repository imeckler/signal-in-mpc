#include "SessionWork/ErasedHostCall.h"
#include "LifecycleWork/SecureGmp.h"
#include <iostream>
#include <gmpxx.h>
#include <stdexcept>
using namespace tls_mpc_worker;
int main() {
    SecureGmp::install_before_threads();
    size_t stacks=ErasingThreadStack::wiped_stacks.load();
    bool ran=false,nested=false;uint64_t generation=0;
    if(!ErasedHostCall::run([&] {
        if(!ErasedHostCall::active())throw std::runtime_error("missing host marker");
        mpz_t x;mpz_init2(x,8192);mpz_setbit(x,4095);mpz_clear(x);
        generation=ErasedHostCall::generation();
        if(ErasedHostCall::completed(generation))throw std::runtime_error("premature host barrier");
        ran=true;
        try {ErasedHostCall::run([]{});}catch(const std::runtime_error&){nested=true;}
    }) || !ran || !nested) return 1;
    if(!ErasedHostCall::completed(generation))return 1;
    auto limbs=SecureGmp::wiped_allocations.load();
    if(ErasedHostCall::run([] {mpz_class value=42;value<<=4096;throw std::runtime_error("public injected failure");}))return 1;
    if(SecureGmp::wiped_allocations<=limbs)return 1;
    if(ErasedHostCall::active() || ErasingThreadStack::wiped_stacks!=stacks+2)return 1;
    std::cout<<"erased host calls passed: successful/throwing jobs joined and wiped; nested invocation rejected\n";
}
