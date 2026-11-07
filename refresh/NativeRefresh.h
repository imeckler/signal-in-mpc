#pragma once

// Unverified backend prototype, not a deployment or an erasure proof.
// Public descriptor agreement + fresh secret coefficients + private deltas.
#include "Machines/Shamir.hpp"
#include "Networking/CryptoPlayer.h"

#include <array>
#include <bit>
#include <cstdint>
#include <limits>
#include <stdexcept>
#include <type_traits>

#ifndef TLS_MPC_REFRESH_TRANSPORT_POLICY
#error "Build against the isolated refresh backend; stock CryptoPlayer policy is insufficient"
#endif
#if TLS_MPC_REFRESH_TRANSPORT_POLICY < 2
#error "Refresh requires exact peer-certificate pinning as well as mutual TLS"
#endif

namespace tls_mpc_refresh {

using Prime = gfp_<0, 4>;
template<class F> using NativeShare = MaliciousShamirShare<F>;
constexpr size_t parties = 5;
constexpr size_t threshold = 2;
constexpr size_t max_components = 4096;

inline void require(bool condition, const char* message)
{
    if (!condition) throw std::runtime_error(message);
}

inline void wipe(octetStream& buffer)
{
    if (buffer.get_length())
        sodium_memzero(buffer.get_data(), buffer.get_length());
    buffer.reset_write_head();
}

template<class T> class SecretVector : public std::vector<T>
{
public:
    using std::vector<T>::vector;
    ~SecretVector()
    {
        static_assert(std::is_trivially_destructible_v<T>);
        if (!this->empty()) sodium_memzero(this->data(), this->size() * sizeof(T));
    }
};

class PrivateBuffers : public std::vector<octetStream>
{
public:
    using std::vector<octetStream>::vector;
    ~PrivateBuffers() { for (auto& buffer : *this) wipe(buffer); }
};

template<class F> std::string domain()
{
    if constexpr (std::is_same_v<F, Prime>) return "shamir-fp25519-montgomery-le64x4";
    else return "ccd-gf2n-" + std::to_string(F::length()) + "-polynomial-le64";
}

inline void configure(const std::string& name)
{
    require(std::endian::native == std::endian::little, "prototype needs little endian native encoding");
    require(sodium_init() >= 0, "libsodium initialization failed");
    ShamirOptions::singleton = {parties, threshold};
    if (name == "fp25519")
    {
        bigint p = 1;
        p <<= 255;
        p -= 19;
        Prime::init_field(p);
    }
    else if (name == "ccd40") gf2n_short::init_field(40);
    else if (name == "ccd64") gf2n_short::init_field(64);
    else throw std::runtime_error("domain must be fp25519, ccd40 or ccd64");
}

template<class F> bool canonical_native(const unsigned char* bytes)
{
    if constexpr (std::is_same_v<F, Prime>)
    {
        // A Montgomery residue is still an integer in [0,p). No reduction on import.
        bigint raw;
        mpz_import(raw.get_mpz_t(), F::size(), -1, 1, 0, 0, bytes);
        return raw < F::pr();
    }
    else
    {
        uint64_t value;
        std::memcpy(&value, bytes, sizeof(value));
        return F::length() == 64 || (value >> F::length()) == 0;
    }
}

template<class F> F decode_native(octetStream& input)
{
    require(input.left() >= size_t(F::size()), "truncated native field payload");
    require(canonical_native<F>(input.get_data_ptr()), "noncanonical native field payload");
    F value;
    value.unpack(input);
    return value;
}

template<class F> void validate_payload(const octetStream& input, size_t count)
{
    require(input.get_length() == count * F::size(), "unexpected native payload length");
    for (size_t i = 0; i < count; ++i)
        require(canonical_native<F>(input.get_data() + i * F::size()),
                "noncanonical native field payload");
}

// Uniform native residues also give uniform field values under Montgomery encoding.
// No deterministic seed, shared PRNG, buffered randomfulls pool, or triple is used.
template<class F> F fresh_field()
{
    std::array<unsigned char, sizeof(F)> bytes{};
    require(size_t(F::size()) <= bytes.size(), "unsupported native field size");
    for (;;)
    {
        randombytes_buf(bytes.data(), F::size());
        if constexpr (std::is_same_v<F, Prime>) bytes[31] &= 127;
        else
            for (size_t bit = F::length(); bit < 64; ++bit)
                bytes[bit / 8] &= ~(1u << (bit % 8));
        if (!canonical_native<F>(bytes.data())) continue;
        octetStream buffer(F::size(), bytes.data());
        F result = decode_native<F>(buffer);
        wipe(buffer);
        sodium_memzero(bytes.data(), bytes.size());
        return result;
    }
}

// x_i is the backend's encoded field point, not repeated addition in characteristic 2.
template<class F> F point(size_t party) { return F(int(party + 1)); }

template<class F> F quadratic(F a0, F a1, F a2, F x)
{
    return a0 + x * (a1 + x * a2);
}

struct Binding
{
    uint64_t source_epoch;
    uint64_t target_epoch;
    std::string descriptor_sha256;

    template<class F> std::string encode(size_t count) const
    {
        require(source_epoch != std::numeric_limits<uint64_t>::max() &&
                target_epoch == source_epoch + 1, "refresh must advance exactly one epoch");
        require(count > 0 && count <= max_components, "component count must be 1..4096");
        require(descriptor_sha256.size() == 64 &&
                descriptor_sha256.find_first_not_of("0123456789abcdef") == std::string::npos,
                "descriptor must be a canonical SHA-256 hex digest");
        return "tls-mpc-native-refresh-prototype-v1\n5\n2\n" + domain<F>() + "\n" +
            std::to_string(source_epoch) + "\n" + std::to_string(target_epoch) + "\n" +
            std::to_string(count) + "\n" + descriptor_sha256 + "\n";
    }
};

inline void agree(Player& player, const std::string& expected)
{
    std::vector<octetStream> messages(parties);
    messages.at(player.my_num()) = octetStream(expected);
    player.Broadcast_Receive(messages);
    player.Check_Broadcast(); // Immediate, before any dependent private operation.
    const octetStream reference(expected);
    for (const auto& message : messages)
        require(message.equals(reference), "refresh descriptor/status disagreement");
}

// Unlike the CCD bit-valued clear API, this uses a full-field Shamir PO instance.
template<class F> class PrivateDeltaOutput : public MaliciousShamirPO<NativeShare<F>>
{
    using Base = MaliciousShamirPO<NativeShare<F>>;
public:
    explicit PrivateDeltaOutput(Player& player) : Base(player) {}
    void validate(size_t count, int me)
    {
        for (size_t i = 0; i < this->to_receive.size(); ++i)
            if (int(i) != me) validate_payload<F>(this->to_receive[i], count);
    }
    ~PrivateDeltaOutput()
    {
        wipe(this->to_send);
        for (auto& input : this->to_receive) wipe(input);
        if (!this->shares.empty())
            sodium_memzero(this->shares.data(), this->shares.size() * sizeof(F));
        // MP-SPDZ's checker/compiler temporaries are outside this wipe's scope.
        // Retiring the entire transition process and its storage remains mandatory.
    }
};

// PRECONDITIONS: source snapshot is agreed/valid; no concurrent mutation; player
// is a fresh authenticated private-channel context. This returns a CANDIDATE,
// never a committed epoch. The caller owns persistence and lifecycle enforcement.
template<class F> SecretVector<NativeShare<F>> prepare(
        Player& player, const Binding& binding, const std::vector<NativeShare<F>>& current)
{
    require(player.num_players() == int(parties) && player.is_encrypted(),
            "refresh requires five authenticated private-channel participants");
    require(ShamirOptions::s().threshold == int(threshold), "wrong Shamir threshold");
    const size_t count = current.size();
    const auto context = binding.encode<F>(count);
    agree(player, context);

    // Two independent coefficients per component. Each party contributes a
    // fresh degree-two sharing of each coefficient, using six full field draws.
    PrivateBuffers outgoing(parties), incoming;
    for (size_t component = 0; component < count; ++component)
        for (size_t coefficient = 0; coefficient < 2; ++coefficient)
        {
            std::array<F, 3> polynomial{fresh_field<F>(), fresh_field<F>(), fresh_field<F>()};
            for (size_t recipient = 0; recipient < parties; ++recipient)
                quadratic(polynomial[0], polynomial[1], polynomial[2], point<F>(recipient))
                    .pack(outgoing[recipient]);
            sodium_memzero(polynomial.data(), sizeof(polynomial));
        }
    player.send_receive_all(outgoing, incoming);
    incoming.at(player.my_num()) = outgoing.at(player.my_num()); // no network self-send
    bool accepted = true;
    SecretVector<NativeShare<F>> coefficients(count * 2);
    try
    {
        for (auto& received : incoming)
        {
            validate_payload<F>(received, count * 2);
            for (auto& coefficient : coefficients) coefficient += decode_native<F>(received);
        }
    }
    catch (const std::exception&) { accepted = false; }
    // Malformed input stops everybody before private outputs. No field values
    // or coefficients are included in this broadcast.
    agree(player, context + (accepted ? "inputs-shaped\n" : "abort-inputs\n"));
    require(accepted, "invalid coefficient contribution payload");

    SecretVector<NativeShare<F>> candidate(count);
    for (size_t recipient = 0; recipient < parties; ++recipient)
    {
        F x = point<F>(recipient);
        SecretVector<NativeShare<F>> projected(count);
        PrivateDeltaOutput<F> output(player);
        for (size_t component = 0; component < count; ++component)
        {
            projected[component] = coefficients[2 * component] * x +
                coefficients[2 * component + 1] * (x * x);
            output.prepare_sending(projected[component], recipient);
        }
        if (int(recipient) == player.my_num())
        {
            output.receive();
            try
            {
                output.validate(count, player.my_num());
                for (size_t component = 0; component < count; ++component)
                {
                    // finalize checks all 2t+1 shares before returning this delta.
                    F delta = output.finalize(projected[component]);
                    candidate[component] = current[component] + delta;
                    sodium_memzero(&delta, sizeof(delta));
                }
            }
            catch (const std::exception&) { accepted = false; }
        }
        else output.send(recipient);
    }
    // No candidate escapes to the caller until every participant reported
    // success and the broadcast transcript was checked for equivocation.
    agree(player, context + (accepted ? "private-deltas-checked\n" : "abort-deltas\n"));
    require(accepted, "private delta consistency check failed");
    return candidate;
}

} // namespace tls_mpc_refresh
