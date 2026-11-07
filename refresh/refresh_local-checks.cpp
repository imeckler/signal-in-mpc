#include "NativeSnapshot.h"
#include <iostream>
#include <sys/stat.h>

using namespace tls_mpc_refresh;

// Metadata only: every attempted communication throws. These tests execute
// actual MP-SPDZ field/decoder/checker code, not an MPC network simulation.
class NoNetworkPlayer final : public Player
{
public:
    explicit NoNetworkPlayer(const Names& names) : Player(names) {}
    void send_to_no_stats(int, const octetStream&) const override { throw std::logic_error("network forbidden in local checks"); }
    void receive_player_no_stats(int, octetStream&) const override { throw std::logic_error("network forbidden in local checks"); }
    void send_receive_all_no_stats(const std::vector<std::vector<bool>>&,
        const std::vector<octetStream>&, std::vector<octetStream>&) const override
        { throw std::logic_error("network forbidden in local checks"); }
};

template<class F> class InjectedPrivateOutput : public PrivateDeltaOutput<F>
{
public:
    explicit InjectedPrivateOutput(Player& player) : PrivateDeltaOutput<F>(player) {}
    void fixture(const std::array<F, parties>& shares)
    {
        this->to_receive.resize(parties);
        for (size_t i = 0; i < parties; ++i) shares[i].pack(this->to_receive[i]);
    }
};

template<class Action> void must_reject(Action action)
{
    bool rejected = false;
    try { action(); } catch (const std::exception&) { rejected = true; }
    require(rejected, "negative case was accepted");
}

template<class F> F interpolate_three(const std::array<F, 3>& values)
{
    F value = 0;
    for (size_t i = 0; i < 3; ++i)
        value += values[i] * Shamir<NativeShare<F>>::get_rec_factor(i, 3);
    return value;
}

class TemporaryDirectory
{
    std::filesystem::path path_;
public:
    TemporaryDirectory()
    {
        std::string pattern = (std::filesystem::temp_directory_path() /
                "tls-mpc-refresh-local-XXXXXX").string();
        require(mkdtemp(pattern.data()) != nullptr, "cannot create local fixture directory");
        path_ = pattern;
    }
    ~TemporaryDirectory()
    {
        std::error_code ignored;
        std::filesystem::remove_all(path_, ignored);
    }
    std::string file(const std::string& name) { return (path_ / name).string(); }
};

template<class F> void snapshot_checks()
{
    // Public arithmetic fixtures only; never a production share/key import.
    TemporaryDirectory directory;
    const auto active = directory.file("active");
    const auto candidate = directory.file("candidate");
    const std::string manifest(64, 'a');
    std::array<std::string, 7> lines{"TLSMPC-LOCAL-SHARES-v1", "active", domain<F>(),
        "0", "6", manifest, "2"};
    octetStream payload;
    F(37).pack(payload);
    F(19).pack(payload);
    auto write_fixture = [&](const std::array<std::string, 7>& header, size_t length,
            bool trailing = false)
    {
        std::ofstream output(active, std::ios::binary | std::ios::trunc);
        for (const auto& line : header) output << line << '\n';
        output.write(reinterpret_cast<const char*>(payload.get_data()), length);
        if (trailing) output.put('\0');
        require(bool(output), "fixture write failed");
    };
    write_fixture(lines, payload.get_length());
    auto shares = load_local<F>(active, 0, 6, manifest);
    require(shares.size() == 2 && shares[0] == F(37) && shares[1] == F(19),
            "native snapshot round trip failed");
    must_reject([&] { load_local<F>(active, 1, 6, manifest); });
    must_reject([&] { load_local<F>(active, 0, 7, manifest); });
    must_reject([&] { load_local<F>(active, 0, 6, std::string(64, 'b')); });
    for (size_t i : {size_t(0), size_t(1), size_t(2), size_t(3), size_t(4), size_t(6)})
    {
        auto changed = lines;
        changed[i] = "invalid";
        write_fixture(changed, payload.get_length());
        must_reject([&] { load_local<F>(active, 0, 6, manifest); });
    }
    write_fixture(lines, payload.get_length() - 1);
    must_reject([&] { load_local<F>(active, 0, 6, manifest); });
    write_fixture(lines, payload.get_length(), true);
    must_reject([&] { load_local<F>(active, 0, 6, manifest); });

    Binding binding{6, 7, std::string(64, 'b')};
    stage_local<F>(candidate, 0, binding, shares);
    struct stat info;
    require(stat(candidate.c_str(), &info) == 0 && (info.st_mode & 0777) == 0600,
            "candidate permissions mismatch");
    must_reject([&] { stage_local<F>(candidate, 0, binding, shares); });
    must_reject([&] { load_local<F>(candidate, 0, 7, binding.descriptor_sha256); });
    for (const auto& text : {"", "01", "-1", "1 ", "18446744073709551616"})
        must_reject([&] { number(text); });
}

template<class F> void checks()
{
    Binding valid{6, 7, std::string(64, 'a')};
    require(!valid.encode<F>(1).empty(), "valid binding rejected");
    must_reject([&] { Binding{6, 8, std::string(64, 'a')}.encode<F>(1); });
    must_reject([&] { Binding{6, 7, "bad"}.encode<F>(1); });
    must_reject([&] { valid.encode<F>(max_components + 1); });

    // Kernel checks all five shares, under every recipient's rotation.
    std::array<F, parties> sharing;
    for (size_t i = 0; i < parties; ++i)
        sharing[i] = quadratic(F(37), F(11), F(19), point<F>(i));
    for (size_t recipient = 0; recipient < parties; ++recipient)
    {
        Names names(recipient, parties);
        NoNetworkPlayer player(names);
        MaliciousShamirMC<NativeShare<F>> checker;
        checker.init_open(player);
        std::vector<F> rotated(parties);
        for (size_t i = 0; i < parties; ++i) rotated[i] = sharing[player.get_player(i)];
        require(checker.reconstruct(rotated) == F(37), "native reconstruction/rotation mismatch");
        for (size_t bad = 0; bad < parties; ++bad)
        {
            auto corrupted = rotated;
            corrupted[bad] += F(1);
            must_reject([&] { checker.reconstruct(corrupted); });
        }
        InjectedPrivateOutput<F> output(player);
        output.fixture(sharing);
        output.validate(1, recipient);
        require(output.finalize(NativeShare<F>(sharing[recipient])) == F(37),
                "native private output truncated a full-field value");
    }

    // Native serialization uses the actual backend field and share classes.
    for (size_t i = 0; i < 128; ++i)
    {
        F value = fresh_field<F>();
        octetStream encoded;
        NativeShare<F>(value).pack(encoded);
        validate_payload<F>(encoded, 1);
        require(decode_native<F>(encoded) == value, "native share round trip failed");
        if constexpr (std::is_same_v<F, gf2n_short>)
        {
            octetStream ccd;
            GC::MaliciousCcdShare<F>(value).pack(ccd);
            require(ccd.equals(encoded), "CCD component serialization is not compatible");
        }
    }
    octetStream empty;
    must_reject([&] { decode_native<F>(empty); });
    std::array<unsigned char, 32> invalid;
    invalid.fill(255);
    if constexpr (std::is_same_v<F, Prime>)
    {
        octetStream bad(F::size(), invalid.data());
        must_reject([&] { decode_native<F>(bad); });
    }
    else if (F::length() < 64)
    {
        octetStream bad(F::size(), invalid.data());
        must_reject([&] { decode_native<F>(bad); });
    }

    // Full raw private-output transcript, not just its final clear value:
    // perturb one honest dealer's inner coefficient sharings along a direction
    // invisible to a single corrupted transition participant B.
    for (size_t b = 0; b < parties; ++b)
    {
        F xb = point<F>(b);
        for (size_t sender = 0; sender < parties; ++sender)
        {
            F x = point<F>(sender);
            F g1 = quadratic(F(7), F(23), F(29), x);
            F g2 = quadratic(F(31), F(41), F(43), x);
            F h = x - xb;
            F changed1 = g1 + h;
            F changed2 = g2 - h / xb;
            require(g1 * xb + g2 * (xb * xb) ==
                changed1 * xb + changed2 * (xb * xb), "private transcript witness failed");
            if (sender == b)
                require(g1 == changed1 && g2 == changed2, "B's private inputs changed");
        }
        F changed_a1 = F(7) - xb;
        F changed_a2 = F(31) + F(1);
        for (size_t other = 0; other < parties; ++other)
        {
            F x = point<F>(other);
            F before = F(7) * x + F(31) * (x * x);
            F after = changed_a1 * x + changed_a2 * (x * x);
            require((before == after) == (other == b), "hidden mask direction was lost");
        }
    }

    // Rejected public-opening design: A before refresh, B during, C afterward.
    // Accounted coalitions {A,B} and {B,C} have size two, yet a public mask
    // translates A's old share to the successor polynomial.
    std::array<F, 3> translated;
    for (size_t i = 0; i < 3; ++i)
    {
        F x = point<F>(i);
        translated[i] = quadratic(F(37), F(11), F(19), x) + F(7) * x + F(31) * (x * x);
    }
    require(interpolate_three(translated) == F(37), "public-mask counterexample did not reconstruct");
    snapshot_checks<F>();
    std::cout << "{\"domain\":\"" << domain<F>()
        << "\",\"status\":\"passed\",\"network_mpc_executed\":false,"
        << "\"scope\":\"native checker, private-output primitive, serialization/snapshots, algebraic transcript witnesses\"}\n";
}

int main(int argc, char** argv)
{
    try
    {
        require(argc == 2, "usage: refresh-local-checks fp25519|ccd40|ccd64");
        std::string name = argv[1];
        configure(name);
        if (name == "fp25519") checks<Prime>();
        else checks<gf2n_short>();
        return 0;
    }
    catch (const std::exception& error)
    {
        std::cerr << "Local refresh check failed: " << error.what() << "\n";
        return 1;
    }
}
