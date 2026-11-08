#pragma once
// Persistent mixed VM adapter. Only native shares cross the function boundary.
// This header intentionally has no share reconstruction or network RPC parser.
#include "Protocols/MaliciousShamirShare.h"
#include "Protocols/ShamirOptions.h"
#include "Machines/MalRep.hpp"
#include "Machines/Shamir.hpp"
#include "Processor/FunctionArgument.h"
#include <functional>
#include <stdexcept>
#include "PinnedPrograms.h"
#include "StrongShamirShare.h"
#include "DaBitOnly.h"
#include "LongFieldBit.h"
#include "OwnedSecrets.h"

namespace tls_mpc_worker {
using Field = gfp_<0, 4>;
using Share = StrongShamirShare<Field>;
using Bit = Share::bit_type;
using Bits = OwnedBits<Bit>;

class Worker {
    Machine<Share>& machine;
    const PinnedPrograms& pinned;
    // Optional partial scratch cleanup for a separately patched runtime. This
    // is not a retirement capability: preprocessing/PRNG/history remain live.
    // The callback runs only after checked execution and output copy-out.
    std::function<void()> cleanup_function_scratch;
    std::vector<Share> scalar;
    bool begun = false;
    bool derived = false;
    void run(const std::string& name,std::vector<FunctionArgument>& args) {
        FunctionArgument result;
        pinned.verify_function(name,args);
        machine.run_function(name,result,args);
        if(cleanup_function_scratch)cleanup_function_scratch();
    }
public:
    explicit Worker(Machine<Share>& machine, const PinnedPrograms& pinned,
                    std::function<void()> cleanup_function_scratch={})
        : machine(machine), pinned(pinned),cleanup_function_scratch(std::move(cleanup_function_scratch)),
          scalar(256, Share::constant(0, machine.get_N().my_num(), machine.get_sint_mac_key())) {}
    Worker(const Worker&)=delete;
    Worker& operator=(const Worker&)=delete;
    ~Worker(){erase_owned_scalar();}
    void erase_owned_scalar() noexcept {
        for(auto& value:scalar)sodium_memzero(static_cast<Field&>(value).get_ptr(),Field::N_BYTES);
        begun=true;derived=true; // Erased scalar storage can never be reused.
    }
    Bits allocate(size_t count) {
        return Bits(count, std::vector<Bit>(1, Bit::constant(0,
            machine.get_N().my_num(), machine.get_bit_mac_key())));
    }
    Bits begin() {
        if (begun) throw std::runtime_error("scalar already allocated");
        // Reserve before execution: a failed operation cannot be retried with
        // partially initialized state. The caller must destroy this session.
        begun = true;
        auto output = allocate(256);
        std::vector<FunctionArgument> args = {{scalar, true}, {1, output.function_argument()}};
        run("tls_begin",args);
        return output; // PUBLIC KEY, still shared until explicitly released.
    }
    Bits agreement(const Field& public_peer) {
        if (!begun || derived) throw std::runtime_error("invalid agreement phase");
        derived = true;
        std::vector<Share> peer = {Share::constant(public_peer,
            machine.get_N().my_num(), machine.get_sint_mac_key())};
        auto output = allocate(256);
        std::vector<FunctionArgument> args = {{scalar, true}, {peer}, {1, output.function_argument()}};
        run("tls_agreement",args);
        return output; // SECRET ECDH bytes. Never eligible for public release.
    }
    Bits binary(const std::string& stem, Bits inputs, size_t output_bits) {
        if (stem.rfind("tls-", 0) != 0 || output_bits == 0 || output_bits > 140000)
            throw std::runtime_error("invalid TLS kernel dimensions/name");
        std::string name = "tls_binary_";
        for (auto c : stem) {
            if (!(c >= 'a' && c <= 'z') && !(c >= '0' && c <= '9') && c != '-')
                throw std::runtime_error("invalid TLS kernel character");
            name += c == '-' ? '_' : c;
        }
        auto output = allocate(output_bits);
        std::vector<FunctionArgument> args = {{1, inputs.function_argument()}, {1, output.function_argument()}};
        run(name,args);
        return output;
    }
};
}
