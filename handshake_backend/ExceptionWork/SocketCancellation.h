#pragma once
#include <sys/socket.h>
#include <map>
#include <mutex>
#include <stdexcept>
#include <cstdint>
namespace tls_caught_failure {
// Owns registrations, not descriptors. A token must unregister before its
// stream closes the descriptor, preventing cancellation of a reused fd.
class SocketRegistry {
    mutable std::mutex mutex;std::map<uint64_t,int> sockets;
    uint64_t next=1;bool failed=false;
public:
    uint64_t attach(int fd){
        std::lock_guard guard(mutex);
        if(fd<0)throw std::runtime_error("invalid MPC cancellation descriptor");
        if(failed){::shutdown(fd,SHUT_RDWR);throw std::runtime_error("MPC runtime cancelled");}
        for(const auto& item:sockets)if(item.second==fd)throw std::runtime_error("duplicate MPC cancellation descriptor");
        if(!next)throw std::runtime_error("MPC cancellation registration exhausted");
        auto ticket=next++;sockets.emplace(ticket,fd);return ticket;
    }
    void detach(uint64_t ticket)noexcept{std::lock_guard guard(mutex);sockets.erase(ticket);}
    void cancel()noexcept{
        std::lock_guard guard(mutex);if(failed)return;failed=true;
        for(const auto& item:sockets)::shutdown(item.second,SHUT_RDWR);
    }
    bool cancelled()const noexcept{std::lock_guard guard(mutex);return failed;}
    size_t active()const noexcept{std::lock_guard guard(mutex);return sockets.size();}
};
inline SocketRegistry runtime_sockets;
class SocketToken {
    SocketRegistry* registry;uint64_t ticket=0;
public:
    explicit SocketToken(SocketRegistry& registry=runtime_sockets):registry(&registry){}
    SocketToken(const SocketToken&)=delete;SocketToken&operator=(const SocketToken&)=delete;
    SocketToken(SocketToken&& other)noexcept:registry(other.registry),ticket(other.ticket){other.ticket=0;}
    ~SocketToken(){if(ticket)registry->detach(ticket);}
    void arm(int fd){if(ticket)throw std::runtime_error("MPC cancellation descriptor already armed");ticket=registry->attach(fd);}
};
}
