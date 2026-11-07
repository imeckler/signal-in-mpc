#pragma once

#include "NativeRefresh.h"
#include <cerrno>
#include <charconv>
#include <filesystem>
#include <fcntl.h>
#include <fstream>
#include <unistd.h>

namespace tls_mpc_refresh {

inline uint64_t number(const std::string& text)
{
    uint64_t value = 0;
    auto result = std::from_chars(text.data(), text.data() + text.size(), value);
    require(result.ec == std::errc() && result.ptr == text.data() + text.size() &&
            text == std::to_string(value), "noncanonical unsigned integer");
    return value;
}

// The caller must already authenticate the source manifest, local file and its
// inventory. This envelope checks shape/context, not source-sharing validity.
// It deliberately is not the native MP-SPDZ Transactions stream format.
template<class F> SecretVector<NativeShare<F>> load_local(const std::string& path,
        size_t party, uint64_t epoch, const std::string& source_manifest)
{
    std::ifstream file(path, std::ios::binary | std::ios::ate);
    require(bool(file), "cannot open local source snapshot");
    auto length = file.tellg();
    require(length >= 0 && length <= std::streamoff(1024 + max_components * F::size()),
            "oversized source snapshot");
    file.seekg(0);
    std::array<std::string, 7> lines;
    for (auto& line : lines)
        require(bool(std::getline(file, line)) && line.size() <= 256, "invalid snapshot header");
    require(lines[0] == "TLSMPC-LOCAL-SHARES-v1" && lines[1] == "active" &&
            lines[2] == domain<F>() && number(lines[3]) == party &&
            number(lines[4]) == epoch && lines[5] == source_manifest,
            "source snapshot binding mismatch (candidate files cannot be used as active state)");
    size_t count = number(lines[6]);
    require(count > 0 && count <= max_components, "invalid source component count");
    SecretVector<unsigned char> bytes(count * F::size());
    file.read(reinterpret_cast<char*>(bytes.data()), bytes.size());
    require(file.gcount() == std::streamsize(bytes.size()) && file.peek() == EOF,
            "snapshot payload length mismatch");
    octetStream input(bytes.size(), bytes.data());
    SecretVector<NativeShare<F>> result(count);
    try { for (auto& share : result) share = decode_native<F>(input); }
    catch (...) { wipe(input); throw; }
    wipe(input);
    return result;
}

class LocalFd
{
    int value_;
public:
    explicit LocalFd(int value) : value_(value) {}
    LocalFd(const LocalFd&) = delete;
    LocalFd& operator=(const LocalFd&) = delete;
    ~LocalFd() { if (value_ >= 0) close(value_); }
    int get() const { return value_; }
};

template<class F> void stage_local(const std::string& path, size_t party,
        const Binding& binding, const std::vector<NativeShare<F>>& shares)
{
    require(party < parties, "invalid candidate party index");
    binding.encode<F>(shares.size());
    std::string header = "TLSMPC-LOCAL-SHARES-v1\ncandidate\n" + domain<F>() + "\n" +
        std::to_string(party) + "\n" + std::to_string(binding.target_epoch) + "\n" +
        binding.descriptor_sha256 + "\n" + std::to_string(shares.size()) + "\n";
    octetStream payload(header);
    for (const auto& share : shares) share.pack(payload);
    try
    {
        LocalFd fd(open(path.c_str(), O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC, 0600));
        require(fd.get() >= 0, "cannot create exclusive candidate file");
        size_t offset = 0;
        while (offset < payload.get_length())
        {
            auto written = write(fd.get(), payload.get_data() + offset,
                    payload.get_length() - offset);
            if (written < 0 && errno == EINTR) continue;
            require(written > 0, "candidate write failed");
            offset += written;
        }
        require(fsync(fd.get()) == 0, "candidate fsync failed");
        auto directory = std::filesystem::path(path).parent_path();
        if (directory.empty()) directory = ".";
        LocalFd parent(open(directory.c_str(), O_RDONLY | O_DIRECTORY | O_CLOEXEC));
        require(parent.get() >= 0 && fsync(parent.get()) == 0,
                "candidate directory fsync failed");
        wipe(payload);
    }
    catch (...) { wipe(payload); throw; }
    // No epoch commit or cleanup receipt. The containing directory is trusted.
    // A partial write remains a non-active candidate and needs recovery handling.
    // fsync is not an erasure proof or a universal power-loss durability guarantee.
}

} // namespace tls_mpc_refresh
