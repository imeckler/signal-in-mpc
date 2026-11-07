#include "NativePrzs.h"
#include <iostream>

using namespace tls_mpc_refresh;

template<class Action> void must_reject(Action action)
{
    bool rejected = false;
    try { action(); } catch (const std::exception&) { rejected = true; }
    require(rejected, "negative PRZS case was accepted");
}

template<class F> F reconstruct_three(const std::array<F, 3>& shares)
{
    F result = 0;
    for (size_t i = 0; i < shares.size(); ++i)
        result += shares[i] * Shamir<NativeShare<F>>::get_rec_factor(i, 3);
    return result;
}

std::array<PrzsSeed, parties> public_fixture_seeds()
{
    std::array<PrzsSeed, parties> seeds;
    for (size_t b = 0; b < parties; ++b)
    {
        const std::string label = "PUBLIC LOCAL PRZS FIXTURE " + std::to_string(b);
        crypto_hash_sha256(seeds[b].data(),
                reinterpret_cast<const unsigned char*>(label.data()), label.size());
    }
    return seeds;
}

PrzsKeys fixture_keys(size_t owner, const std::array<PrzsSeed, parties>& seeds)
{
    PrzsKeys keys(owner);
    for (size_t b = 0; b < parties; ++b)
        if (b != owner) keys.install(b, seeds[b].data());
    return keys;
}

template<class F> void common_mask_attack()
{
    const F secret = std::is_same_v<F, Prime> ? F(37) : F(1);
    std::array<F, parties> target, reference;
    for (size_t i = 0; i < parties; ++i)
    {
        target[i] = quadratic(secret, F(11), F(19), point<F>(i));
        reference[i] = quadratic(F(0), F(23), F(29), point<F>(i));
    }
    std::array<F, 3> retained_differences;
    for (size_t epoch = 0; epoch < 3; ++epoch)
    {
        // Only party `epoch` is exposed in this period; no transition exposure.
        retained_differences[epoch] = target[epoch] - reference[epoch];
        if (epoch == 2) break;
        const F a1 = fresh_field<F>(), a2 = fresh_field<F>();
        for (size_t i = 0; i < parties; ++i)
        {
            const F x = point<F>(i);
            const F same_mask = a1 * x + a2 * x * x;
            target[i] += same_mask;
            reference[i] += same_mask;
        }
    }
    require(reconstruct_three(retained_differences) == secret,
            "shared-mask multi-epoch attack did not recover the difference");
}

template<class F> std::array<F, 3> exposure_difference(unsigned exposed)
{
    require(std::popcount(exposed) <= 2, "inadmissible exposure set");
    std::array<F, 3> result{F(1), F(0), F(0)};
    std::vector<F> points;
    for (size_t i = 0; i < parties; ++i)
        if (exposed & (1u << i)) points.push_back(point<F>(i));
    if (points.size() == 1) result[1] = -F(1) / points[0];
    if (points.size() == 2)
    {
        F product = points[0] * points[1];
        result[1] = -(points[0] + points[1]) / product;
        result[2] = F(1) / product;
    }
    for (auto x : points)
        require(quadratic(result[0], result[1], result[2], x) == F(0),
                "exposure difference failed to vanish");
    return result;
}

template<class F> size_t check_all_adjacent_budgets()
{
    size_t checked = 0;
    for (unsigned left = 0; left < 32; ++left)
    for (unsigned right = 0; right < 32; ++right)
    for (unsigned transition = 0; transition < 32; ++transition)
    {
        if (std::popcount(left) > 2 || std::popcount(right) > 2 ||
            (transition & left) != transition || (transition & right) != transition) continue;
        const auto old = exposure_difference<F>(left);
        const auto next = exposure_difference<F>(right);
        const F q1 = next[1] - old[1], q2 = next[2] - old[2];
        const int corrupt = std::popcount(transition);
        if (corrupt == 2)
            require(q1 == F(0) && q2 == F(0), "known-all-seed transition needs hidden entropy");
        else if (corrupt == 1)
        {
            const size_t b = std::countr_zero(transition);
            require(q1 == -point<F>(b) * q2, "one hidden subset cannot realize mask difference");
        }
        else
        {
            const F x0 = point<F>(0), x1 = point<F>(1);
            const F u0 = (q1 + x1 * q2) / (x1 - x0), u1 = q2 - u0;
            require(F(0) - x0 * u0 - x1 * u1 == q1 && u0 + u1 == q2,
                    "two hidden subsets fail to span zero polynomials");
        }
        ++checked;
    }
    // A two-corruption transition cannot directly hand off to a new pair:
    // the intermediate epoch would account for the union of both transitions.
    require(std::popcount(unsigned(0b00011 | 0b00110)) == 3,
            "adjacent transition budget fixture is wrong");
    return checked;
}

template<class F> void retained_master_seed_attack(const std::array<PrzsSeed, parties>& seeds)
{
    // Rejected variant: the same master keys persist, even though epoch labels
    // differ. Exposing A then B gives the union of all five seeds; C completes
    // three shares translated into epoch 2. Fresh setup/erasure disallows this.
    const F secret = std::is_same_v<F, Prime> ? F(53) : F(1);
    const ComponentId id{std::string(64, 'a'), 0, 0};
    std::array<F, parties> state;
    std::array<std::array<F, parties>, 2> masks;
    std::array<F, 3> observations;
    for (size_t i = 0; i < parties; ++i)
        state[i] = quadratic(secret, F(13), F(31), point<F>(i));
    for (size_t epoch = 0; epoch < 3; ++epoch)
    {
        observations[epoch] = state[epoch];
        if (epoch == 2) break;
        for (size_t i = 0; i < parties; ++i)
        {
            auto keys = fixture_keys(i, seeds);
            masks[epoch][i] = przs_delta<F>(keys, "distinct epoch " + std::to_string(epoch) + "\n", id);
            state[i] += masks[epoch][i];
        }
    }
    auto a_view = fixture_keys(0, seeds), b_view = fixture_keys(1, seeds);
    std::array<PrzsSeed, parties> recovered;
    for (size_t excluded = 0; excluded < parties; ++excluded)
        recovered[excluded] = excluded != 0 ? a_view.seed(excluded) : b_view.seed(excluded);
    auto a_keys = fixture_keys(0, recovered), b_keys = fixture_keys(1, recovered);
    observations[0] += przs_delta<F>(a_keys, "distinct epoch 0\n", id) +
            przs_delta<F>(a_keys, "distinct epoch 1\n", id);
    observations[1] += przs_delta<F>(b_keys, "distinct epoch 1\n", id);
    require(reconstruct_three(observations) == secret, "retained master-seed attack failed");
}

template<class F> void checks()
{
    common_mask_attack<F>();
    const auto seeds = public_fixture_seeds();
    const ComponentId id{std::string(64, 'a'), 7, 3};
    const std::string context = "public native PRZS fixture\n";
    std::array<F, parties> coefficients, deltas;
    F a1 = 0, a2 = 0;
    for (size_t b = 0; b < parties; ++b)
    {
        coefficients[b] = przs_field<F>(seeds[b], context, b, id);
        a1 -= point<F>(b) * coefficients[b];
        a2 += coefficients[b];
        require(przs_basis<F>(b, F(0)) == F(0) &&
                przs_basis<F>(b, point<F>(b)) == F(0), "PRZS basis root mismatch");
    }
    for (size_t i = 0; i < parties; ++i)
    {
        auto keys = fixture_keys(i, seeds);
        deltas[i] = przs_delta<F>(keys, context, id);
        require(deltas[i] == quadratic(F(0), a1, a2, point<F>(i)),
                "local PRZS delta disagrees with the zero polynomial");
        must_reject([&] { keys.seed(i); });
        for (size_t recipient = 0; recipient < parties; ++recipient)
            if (recipient != i)
            {
                auto other = fixture_keys(recipient, seeds);
                octetStream echo;
                keys.append_echo(recipient, echo);
                other.check_echo(i, echo);
                echo.get_data()[0] ^= 1;
                must_reject([&] { other.check_echo(i, echo); });
            }
    }
    require(reconstruct_three<F>({deltas[0], deltas[1], deltas[2]}) == F(0),
            "PRZS mask has a nonzero secret");
    size_t equivocations = 0;
    for (unsigned corrupt = 0; corrupt < 32; ++corrupt)
        if (std::popcount(corrupt) <= 2)
            for (size_t excluded = 0; excluded < parties; ++excluded)
            {
                std::vector<size_t> honest;
                for (size_t i = 0; i < parties; ++i)
                    if (i != excluded && !(corrupt & (1u << i))) honest.push_back(i);
                require(honest.size() >= 2, "subset lacks honest comparison partners");
                auto first = fixture_keys(honest[0], seeds), second = fixture_keys(honest[1], seeds);
                auto changed = seeds[excluded];
                changed[0] ^= 1;
                first.install(excluded, changed.data());
                octetStream echo;
                first.append_echo(honest[1], echo);
                must_reject([&] { second.check_echo(honest[0], echo); });
                ++equivocations;
            }

    auto changed = id;
    changed.component_index++;
    require(przs_field<F>(seeds[0], context, 0, changed) != coefficients[0],
            "fixture component separation failed");
    require(przs_field<F>(seeds[0], context + "next epoch\n", 0, id) != coefficients[0],
            "fixture epoch separation failed");
    require(component_manifest({id, changed}).size() == 64, "inventory hash missing");
    must_reject([&] { component_manifest({id, id}); });
    changed.opaque_handle = "invalid";
    must_reject([&] { changed.encode(); });
    retained_master_seed_attack<F>(seeds);
    const size_t budget_cases = check_all_adjacent_budgets<F>();
    std::cout << "{\"domain\":\"" << domain<F>() << "\",\"status\":\"passed\","
        << "\"same_mask_three_epoch_attack_reproduced\":true,"
        << "\"retained_seed_attack_reproduced\":true,"
        << "\"adjacent_budget_cases\":" << budget_cases << ","
        << "\"malicious_seed_equivocation_cases\":" << equivocations << ","
        << "\"network_mpc_executed\":false,\"proactive_security_proved\":false}\n";
}

int main(int argc, char** argv)
{
    try
    {
        require(argc == 2, "usage: refresh-przs-checks fp25519|ccd40|ccd64");
        configure(argv[1]);
        if (std::string(argv[1]) == "fp25519") checks<Prime>();
        else checks<gf2n_short>();
        return 0;
    }
    catch (const std::exception& error)
    {
        std::cerr << "PRZS local check failed: " << error.what() << '\n';
        return 1;
    }
}
