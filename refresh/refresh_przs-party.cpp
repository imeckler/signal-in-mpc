#include "NativeSnapshot.h"
#include "NativePrzs.h"
#include <iostream>
#include <sstream>

using namespace tls_mpc_refresh;

std::vector<ComponentId> load_component_ids(const std::string& path, size_t count)
{
    std::ifstream file(path, std::ios::ate | std::ios::binary);
    require(bool(file) && file.tellg() >= 0 &&
            file.tellg() <= std::streamoff(max_components * 128), "invalid inventory file size");
    file.seekg(0);
    std::vector<ComponentId> result;
    std::string line;
    while (std::getline(file, line))
    {
        require(result.size() < count && line.size() <= 127, "oversized component inventory");
        std::istringstream fields(line);
        std::string handle, version, index, extra;
        require(bool(fields >> handle >> version >> index) && !(fields >> extra),
                "inventory row needs handle, version and component index");
        ComponentId id{handle, number(version), number(index)};
        id.encode();
        result.push_back(std::move(id));
    }
    require(result.size() == count, "inventory/source component count mismatch");
    component_manifest(result); // Includes duplicate-label rejection.
    return result;
}

template<class F> void run(char** argv)
{
    const size_t party = number(argv[2]);
    const auto port = number(argv[4]);
    const uint64_t epoch = number(argv[5]);
    require(party < parties && port > 1024 && port < 65530, "invalid party/port");
    const std::string source_manifest = argv[6];
    Binding binding{epoch, epoch + 1, argv[7]};
    Binding{0, 1, source_manifest}.encode<F>(1);
    auto current = load_local<F>(argv[8], party, epoch, source_manifest);
    auto ids = load_component_ids(argv[10], current.size());
    const auto context = binding.encode<F>(current.size()) + source_manifest;
    Names names(party, port, std::string(argv[3]));
    require(names.num_players() == int(parties), "hosts file must contain five parties");
    CryptoPlayer player(names, "tls-mpc-przs-refresh-" + binding.descriptor_sha256);
    agree(player, context);
    auto candidate = prepare_przs<F>(player, binding, current, ids);
    stage_local<F>(argv[9], party, binding, candidate);
    std::cout << "Experimental PRZS candidate staged; epoch commit, seed erasure closure, and mobile composition are NOT implemented.\n";
}

int main(int argc, char** argv)
{
    try
    {
        require(argc == 11, "usage: refresh-przs-party DOMAIN PARTY HOSTS PORT SOURCE_EPOCH SOURCE_MANIFEST_SHA256 DESCRIPTOR_SHA256 INPUT CANDIDATE COMPONENT_IDS");
        configure(argv[1]);
        if (std::string(argv[1]) == "fp25519") run<Prime>(argv);
        else run<gf2n_short>(argv);
        return 0;
    }
    catch (const std::exception& error)
    {
        std::cerr << "Experimental PRZS refresh aborted: " << error.what() << '\n';
        return 1;
    }
}
