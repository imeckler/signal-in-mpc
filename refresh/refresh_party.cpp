#include "NativeSnapshot.h"
#include <iostream>

using namespace tls_mpc_refresh;

template<class F> void run(char** argv)
{
    size_t party = number(argv[2]);
    auto port = number(argv[4]);
    uint64_t source_epoch = number(argv[5]);
    require(party < parties && port > 1024 && port < 65530, "invalid party/port");
    std::string source_manifest = argv[6];
    Binding binding{source_epoch, source_epoch + 1, argv[7]};
    // Also validate the source digest before it appears in a signed descriptor.
    Binding{0, 1, source_manifest}.encode<F>(1);
    auto current = load_local<F>(argv[8], party, source_epoch, source_manifest);
    auto encoded = binding.encode<F>(current.size()) + source_manifest;
    Names names(party, port, std::string(argv[3]));
    require(names.num_players() == int(parties), "hosts file must contain exactly five parties");
    CryptoPlayer player(names, "tls-mpc-refresh-" + binding.descriptor_sha256);
    agree(player, encoded); // Source manifest as well as successor descriptor.
    auto candidate = prepare<F>(player, binding, current);
    stage_local<F>(argv[9], party, binding, candidate);
    std::cout << "Candidate staged; epoch commit and proactive closure are NOT implemented.\n";
}

int main(int argc, char** argv)
{
    try
    {
        require(argc == 10, "usage: refresh-party DOMAIN PARTY HOSTS PORT SOURCE_EPOCH SOURCE_MANIFEST_SHA256 DESCRIPTOR_SHA256 INPUT CANDIDATE");
        configure(argv[1]);
        if (std::string(argv[1]) == "fp25519") run<Prime>(argv);
        else run<gf2n_short>(argv);
        return 0;
    }
    catch (const std::exception& error)
    {
        std::cerr << "Refresh aborted: " << error.what() << "\n";
        return 1;
    }
}
