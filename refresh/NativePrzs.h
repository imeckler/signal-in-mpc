#pragma once

// Experimental computational alternative to per-component interactive refresh.
// See PRZS.txt: fresh transition-only seeds and complete erasure are essential.
#include "NativeRefresh.h"
#include <set>

namespace tls_mpc_refresh {

using PrzsSeed = std::array<unsigned char, crypto_auth_hmacsha256_KEYBYTES>;

struct ComponentId
{
    std::string opaque_handle;
    uint64_t object_version;
    uint64_t component_index;

    std::string encode() const
    {
        require(opaque_handle.size() == 64 &&
                opaque_handle.find_first_not_of("0123456789abcdef") == std::string::npos,
                "component needs a canonical 32-byte opaque handle");
        return opaque_handle + "\n" + std::to_string(object_version) + "\n" +
                std::to_string(component_index) + "\n";
    }
};

inline std::string component_manifest(const std::vector<ComponentId>& ids)
{
    require(!ids.empty() && ids.size() <= max_components, "invalid component inventory size");
    std::set<std::string> unique;
    std::string encoded = "tls-mpc-przs-component-inventory-v1\n";
    for (const auto& id : ids)
    {
        auto entry = id.encode();
        require(unique.insert(entry).second, "duplicate component label reuses a mask");
        encoded += entry;
    }
    std::array<unsigned char, crypto_hash_sha256_BYTES> digest;
    crypto_hash_sha256(digest.data(), reinterpret_cast<const unsigned char*>(encoded.data()),
            encoded.size());
    std::array<char, crypto_hash_sha256_BYTES * 2 + 1> hex;
    sodium_bin2hex(hex.data(), hex.size(), digest.data(), digest.size());
    return hex.data();
}

// Keys are replicated to everyone except the corresponding excluded party.
// This object does NOT prove setup correctness; setup_przs checks agreement.
// A later exposure must not recover this object or any copies of these keys.
class PrzsKeys
{
    size_t owner_;
    std::array<PrzsSeed, parties> values_{};
public:
    explicit PrzsKeys(size_t owner) : owner_(owner)
        { require(owner < parties, "invalid PRZS key owner"); }
    PrzsKeys(const PrzsKeys&) = delete;
    PrzsKeys& operator=(const PrzsKeys&) = delete;
    PrzsKeys(PrzsKeys&& other) : owner_(other.owner_), values_(other.values_)
        { sodium_memzero(other.values_.data(), sizeof(other.values_)); }
    ~PrzsKeys() { sodium_memzero(values_.data(), sizeof(values_)); }
    size_t owner() const { return owner_; }
    const PrzsSeed& seed(size_t excluded) const
    {
        require(excluded < parties && excluded != owner_, "excluded party cannot read this seed");
        return values_[excluded];
    }
    void install(size_t excluded, const unsigned char* value)
    {
        require(excluded < parties && excluded != owner_, "excluded party cannot hold this seed");
        std::memcpy(values_[excluded].data(), value, values_[excluded].size());
    }
    void append_echo(size_t recipient, octetStream& out) const
    {
        require(recipient < parties && recipient != owner_, "invalid seed echo recipient");
        for (size_t excluded = 0; excluded < parties; ++excluded)
            if (excluded != owner_ && excluded != recipient)
                out.append(values_[excluded].data(), values_[excluded].size());
    }
    void check_echo(size_t sender, const octetStream& received) const
    {
        require(sender < parties && sender != owner_, "invalid seed echo sender");
        require(received.get_length() == (parties - 2) * PrzsSeed{}.size(),
                "invalid seed echo length");
        size_t offset = 0;
        for (size_t excluded = 0; excluded < parties; ++excluded)
            if (excluded != owner_ && excluded != sender)
            {
                require(sodium_memcmp(values_[excluded].data(), received.get_data() + offset,
                        values_[excluded].size()) == 0, "inconsistent subset seed");
                offset += values_[excluded].size();
            }
    }
};

// One dealer per subset is sufficient for the stated model: the subset hidden
// from a sole transition corruption consists entirely of honest parties. See
// the case analysis in PRZS.txt; this is not a general t-private PRSS oracle.
inline PrzsKeys setup_przs(Player& player, const std::string& agreed_context)
{
    require(player.num_players() == int(parties) && player.is_encrypted(),
            "PRZS setup requires five authenticated private-channel participants");
    require(ShamirOptions::s().threshold == int(threshold), "wrong PRZS Shamir threshold");
    const size_t me = player.my_num();
    agree(player, agreed_context);
    PrzsKeys keys(me);
    PrivateBuffers outgoing(parties), incoming;
    PrzsSeed dealer_seed;
    crypto_auth_hmacsha256_keygen(dealer_seed.data());
    // Dealer d supplies the key for the subset excluding d-1 (mod 5).
    const size_t excluded = (me + parties - 1) % parties;
    for (size_t recipient = 0; recipient < parties; ++recipient)
        if (recipient != excluded)
            outgoing[recipient].append(dealer_seed.data(), dealer_seed.size());
    sodium_memzero(dealer_seed.data(), dealer_seed.size());
    player.send_receive_all(outgoing, incoming);
    incoming.at(me) = outgoing.at(me);
    bool accepted = true;
    try
    {
        for (size_t sender = 0; sender < parties; ++sender)
        {
            const size_t group = (sender + parties - 1) % parties;
            const size_t expected = group == me ? 0 : PrzsSeed{}.size();
            require(incoming[sender].get_length() == expected, "invalid subset seed payload");
            if (expected) keys.install(group, incoming[sender].get_data());
        }
    }
    catch (const std::exception&) { accepted = false; }
    agree(player, agreed_context + (accepted ? "seed-payloads-shaped\n" : "abort-seed-payloads\n"));
    require(accepted, "malformed subset seed input");

    // Echo only to the other holders of each seed. Never publish seed hashes.
    PrivateBuffers echoes(parties), received;
    for (size_t recipient = 0; recipient < parties; ++recipient)
        if (recipient != me) keys.append_echo(recipient, echoes[recipient]);
    player.send_receive_all(echoes, received);
    try
    {
        for (size_t sender = 0; sender < parties; ++sender)
            if (sender != me) keys.check_echo(sender, received[sender]);
    }
    catch (const std::exception&) { accepted = false; }
    agree(player, agreed_context + (accepted ? "subset-seeds-agreed\n" : "abort-seed-agreement\n"));
    require(accepted, "subset seed consistency failed");
    return keys;
}

template<class F> F przs_field(const PrzsSeed& seed, const std::string& context,
        size_t excluded, const ComponentId& id)
{
    static_assert(std::is_same_v<F, Prime> || std::is_same_v<F, gf2n_short>);
    require(excluded < parties, "invalid PRZS subset");
    const std::string label = "tls-mpc-przs-hmacsha256-v1\n" + domain<F>() + "\n" + context +
            "excluded\n" + std::to_string(excluded) + "\ncomponent\n" + id.encode();
    std::array<unsigned char, crypto_auth_hmacsha256_BYTES> bytes;
    static_assert(crypto_auth_hmacsha256_BYTES == 32);
    for (size_t retry = 0; retry < 64; ++retry)
    {
        const auto input = label + "retry\n" + std::to_string(retry) + "\n";
        crypto_auth_hmacsha256(bytes.data(),
                reinterpret_cast<const unsigned char*>(input.data()), input.size(), seed.data());
        if constexpr (std::is_same_v<F, Prime>) bytes[31] &= 127;
        else
            for (size_t bit = F::length(); bit < 64; ++bit)
                bytes[bit / 8] &= ~(1u << (bit % 8));
        if (!canonical_native<F>(bytes.data())) continue;
        octetStream encoded(F::size(), bytes.data());
        F result = decode_native<F>(encoded);
        wipe(encoded);
        sodium_memzero(bytes.data(), bytes.size());
        return result;
    }
    sodium_memzero(bytes.data(), bytes.size());
    throw std::runtime_error("PRZS field expansion rejection limit");
}

template<class F> F przs_basis(size_t excluded, F x)
{
    require(excluded < parties, "invalid PRZS basis index");
    return x * (x - point<F>(excluded));
}

template<class F> F przs_delta(const PrzsKeys& keys, const std::string& context,
        const ComponentId& id)
{
    const F x = point<F>(keys.owner());
    F result = 0;
    for (size_t excluded = 0; excluded < parties; ++excluded)
        if (excluded != keys.owner())
        {
            F coefficient = przs_field<F>(keys.seed(excluded), context, excluded, id);
            result += coefficient * przs_basis<F>(excluded, x);
            sodium_memzero(&coefficient, sizeof(coefficient));
        }
    return result;
}

// Bounded candidate API only. The current envelope supports <=4096 components;
// streaming one setup across a larger full inventory is future integration.
template<class F> SecretVector<NativeShare<F>> prepare_przs(Player& player,
        const Binding& binding, const std::vector<NativeShare<F>>& current,
        const std::vector<ComponentId>& ids)
{
    require(current.size() == ids.size(), "component inventory/source size mismatch");
    const std::string context = "tls-mpc-przs-refresh-prototype-v1\n" +
            binding.encode<F>(ids.size()) + component_manifest(ids) + "\n";
    auto keys = setup_przs(player, context);
    SecretVector<NativeShare<F>> candidate(current.size());
    bool accepted = true;
    try
    {
        for (size_t component = 0; component < current.size(); ++component)
        {
            F delta = przs_delta<F>(keys, context, ids[component]);
            candidate[component] = current[component] + delta;
            sodium_memzero(&delta, sizeof(delta));
        }
    }
    catch (const std::exception&) { accepted = false; }
    agree(player, context + (accepted ? "przs-candidate-ready\n" : "abort-przs-expansion\n"));
    require(accepted, "PRZS candidate expansion failed");
    return candidate;
}

} // namespace tls_mpc_refresh
