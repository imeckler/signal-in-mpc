#pragma once
#include "PinnedPrograms.h"
#include "KernelShape.h"
#include <spawn.h>
#include <sys/wait.h>
#include <fcntl.h>
#include <cerrno>
#include <functional>
#include <chrono>
#include <thread>
#include <signal.h>
#include <unistd.h>

extern char **environ;
namespace tls_mpc_worker {
// This process receives ONLY a public operation and dimensions. posix_spawn avoids
// running a compiler in a forked copy of the MPC process's private heap.
// The pinned local compiler and host interpreter/libraries remain trusted.
inline void run_shape_compiler(const KernelShape& shape) {
    std::string command="Worker-Public/tls-shape-compiler";
    auto arguments=shape.arguments();std::vector<char*> argv{command.data()};
    for(auto& argument:arguments)argv.push_back(argument.data());argv.push_back(nullptr);
    posix_spawn_file_actions_t actions;
    posix_spawnattr_t attr;
    public_require(posix_spawn_file_actions_init(&actions)==0,"spawn actions failed");
    if(posix_spawnattr_init(&attr)!=0) {posix_spawn_file_actions_destroy(&actions);throw std::runtime_error("spawn attributes failed");}
    int error=0;
    auto check=[&](int result){if(result!=0&&error==0)error=result;};
    // Never inherit the RPC pipe, player sockets, or other private descriptors.
    check(posix_spawn_file_actions_addopen(&actions,0,"/dev/null",O_RDONLY,0));
    check(posix_spawn_file_actions_addopen(&actions,1,"/dev/null",O_WRONLY,0));
    check(posix_spawn_file_actions_addopen(&actions,2,"/dev/null",O_WRONLY,0));
#if defined(__APPLE__)
    check(posix_spawnattr_setflags(&attr,POSIX_SPAWN_CLOEXEC_DEFAULT|POSIX_SPAWN_SETPGROUP));
#elif defined(__GLIBC__)
    check(posix_spawn_file_actions_addclosefrom_np(&actions,3));
    check(posix_spawnattr_setflags(&attr,POSIX_SPAWN_SETPGROUP));
#else
    error=ENOTSUP; // Refuse platforms without a safe close-all spawn primitive.
#endif
    check(posix_spawnattr_setpgroup(&attr,0));
    pid_t child=-1;
    if(error==0)error=posix_spawn(&child,command.c_str(),&actions,&attr,argv.data(),environ);
    posix_spawnattr_destroy(&attr);posix_spawn_file_actions_destroy(&actions);
    public_require(error==0,"shape compiler spawn failed");
    auto deadline=std::chrono::steady_clock::now()+std::chrono::minutes(31);
    int status=0;
    for(;;) {
        auto result=waitpid(child,&status,WNOHANG);
        if(result==child)break;
        if(result<0&&errno==EINTR)continue;
        if(result<0||std::chrono::steady_clock::now()>=deadline) {
            kill(-child,SIGKILL);
            while(waitpid(child,&status,0)<0&&errno==EINTR){}
            throw std::runtime_error("shape compiler failed or timed out");
        }
        std::this_thread::sleep_for(std::chrono::milliseconds(50));
    }
    public_require(WIFEXITED(status)&&WEXITSTATUS(status)==0,"shape compilation failed");
}

class ShapeCompiler {
    PinnedPrograms& pinned;
    std::function<void(const std::string&,const PublicBytes&)> agree;
public:
    static std::string descriptor(size_t size) {
        return KernelShape::handshake(size).descriptor();
    }
    ShapeCompiler(PinnedPrograms& pinned,std::function<void(const std::string&,const PublicBytes&)> agree)
        :pinned(pinned),agree(std::move(agree)){}
    void prepare(size_t size) {
        prepare(KernelShape::handshake(size));
    }
    void prepare(const KernelShape& shape) {
        auto path=shape.descriptor();
        if(pinned.contains(path)) {pinned.verify_descriptor(path);return;}
        pinned.verify_public("Worker-Public/tls-shape-compiler");
        pinned.verify_public("Worker-Public/tls-shape-toolchain.json");
        run_shape_compiler(shape);
        PinnedPrograms extension("Worker-Public/tls-shape-"+shape.key()+".manifest");
        extension.verify_exact_closure(path);
        agree(shape.key(),extension.digest()); // Before registration or private work.
        pinned.append(extension);
    }
};
}
