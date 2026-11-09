#pragma once
#include "PublicProtocol.h"
#include <sys/socket.h>
#include <netdb.h>
#include <unistd.h>
#include <fcntl.h>
#include <poll.h>
#include <cerrno>
#include <chrono>
#include <string>
#include <memory>
namespace tls_mpc_worker {
class TcpRecords {
    int fd=-1;
    PublicBytes pending_input;
    using Clock=std::chrono::steady_clock;
    static void ready(int socket,short events,Clock::time_point deadline) {
        for(;;) {
            auto left=std::chrono::duration_cast<std::chrono::milliseconds>(deadline-Clock::now()).count();
            public_require(left>0,"TLS public transport timed out");
            pollfd item{socket,events,0};int status=::poll(&item,1,int(left));
            if(status<0&&errno==EINTR)continue;
            public_require(status>0,"TLS public transport unavailable");return;
        }
    }
    PublicBytes read_exact(size_t count,Clock::time_point deadline) {
        PublicBytes out(count);size_t used=0;
        while(used<count) {ready(fd,POLLIN,deadline);auto n=::recv(fd,out.data()+used,count-used,0);
            if(n<0&&(errno==EINTR||errno==EAGAIN||errno==EWOULDBLOCK))continue;
            public_require(n>0,"TLS server closed or read failed");used+=n;}
        return out;
    }
public:
    TcpRecords()=default;
    // Take ownership of an already-connected stream (also used by local IPC
    // fixtures). The worker service never accepts descriptors from RPC input.
    explicit TcpRecords(int connected) : fd(connected) {
        public_require(fd>=0,"invalid connected descriptor");
        auto flags=::fcntl(fd,F_GETFL,0);
        if(flags<0||::fcntl(fd,F_SETFL,flags|O_NONBLOCK)<0){close();throw std::runtime_error("cannot configure stream");}
#ifdef SO_NOSIGPIPE
        int one=1;::setsockopt(fd,SOL_SOCKET,SO_NOSIGPIPE,&one,sizeof(one));
#endif
    }
    TcpRecords(const TcpRecords&)=delete;
    TcpRecords& operator=(const TcpRecords&)=delete;
    ~TcpRecords(){close();}
    void close() noexcept {if(fd>=0){::close(fd);fd=-1;}pending_input.clear();}
    void connect(const std::string& host,unsigned port) {
        public_require(fd<0&&!host.empty()&&host.size()<=253&&port>0&&port<=65535,"invalid TCP endpoint/state");
        for(unsigned char c:host)public_require((c>='a'&&c<='z')||(c>='A'&&c<='Z')||(c>='0'&&c<='9')||c=='.'||c=='-',"unsupported server hostname");
        addrinfo hints{};hints.ai_socktype=SOCK_STREAM;hints.ai_family=AF_UNSPEC;addrinfo* raw=nullptr;
        public_require(::getaddrinfo(host.c_str(),std::to_string(port).c_str(),&hints,&raw)==0,"server DNS resolution failed");
        std::unique_ptr<addrinfo,decltype(&freeaddrinfo)> addresses(raw,freeaddrinfo);
        auto deadline=Clock::now()+std::chrono::seconds(30);
        for(auto address=raw;address;address=address->ai_next) {
            int candidate=::socket(address->ai_family,address->ai_socktype,address->ai_protocol);if(candidate<0)continue;
            if(::fcntl(candidate,F_SETFL,O_NONBLOCK)<0){::close(candidate);continue;}
#ifdef SO_NOSIGPIPE
            int one=1;::setsockopt(candidate,SOL_SOCKET,SO_NOSIGPIPE,&one,sizeof(one));
#endif
            int status=::connect(candidate,address->ai_addr,address->ai_addrlen);
            if(status<0&&errno==EINPROGRESS) {
                try {ready(candidate,POLLOUT,deadline);int error=0;socklen_t size=sizeof(error);
                    status=::getsockopt(candidate,SOL_SOCKET,SO_ERROR,&error,&size)==0&&error==0?0:-1;
                }catch(...){::close(candidate);throw;}
            }
            if(status==0){fd=candidate;return;}::close(candidate);
        }
        throw std::runtime_error("TLS server connection failed");
    }
    void send(const PublicBytes& wire) {
        public_require(fd>=0&&wire.size()>=5&&wire.size()<=16645,"invalid public send record");
        size_t length=(size_t(wire[3])<<8)|wire[4];public_require(length==wire.size()-5,"invalid public record framing");
        auto deadline=Clock::now()+std::chrono::seconds(30);size_t used=0;
        while(used<wire.size()) {ready(fd,POLLOUT,deadline);
#ifdef MSG_NOSIGNAL
            constexpr int flags=MSG_NOSIGNAL;
#else
            constexpr int flags=0;
#endif
            auto n=::send(fd,wire.data()+used,wire.size()-used,flags);
            if(n<0&&(errno==EINTR||errno==EAGAIN||errno==EWOULDBLOCK))continue;
            public_require(n>0,"TLS public record write failed");used+=n;}
    }
    PublicBytes receive() {
        public_require(pending_input.empty(),"cannot switch to blocking receive during partial polling");
        public_require(fd>=0,"server socket not connected");auto deadline=Clock::now()+std::chrono::seconds(30);
        auto header=read_exact(5,deadline);size_t size=(size_t(header[3])<<8)|header[4];
        public_require(size<=16640,"server record exceeds TLS limit");auto body=read_exact(size,deadline);
        header.insert(header.end(),body.begin(),body.end());return header;
    }
    // Nonblocking, bounded one-record receive. Empty means not ready; a real
    // zero-length TLS record still has its five-byte header. Partial bytes are
    // retained locally so other agreed requests (especially send) can run.
    PublicBytes poll_receive() {
        public_require(fd>=0,"server socket not connected");
        for(;;) {
            size_t target=5;
            if(pending_input.size()>=5) {
                size_t length=(size_t(pending_input[3])<<8)|pending_input[4];
                public_require(length<=16640,"server record exceeds TLS limit");target+=length;
                if(pending_input.size()==target) {PublicBytes result;result.swap(pending_input);return result;}
            }
            public_require(pending_input.size()<target,"invalid pending record size");
            unsigned char buffer[16645];
            auto count=::recv(fd,buffer,target-pending_input.size(),0);
            if(count<0 && errno==EINTR)continue;
            if(count<0 && (errno==EAGAIN || errno==EWOULDBLOCK))return {};
            public_require(count>0,"TLS server closed or read failed");
            pending_input.insert(pending_input.end(),buffer,buffer+count);
        }
    }
};
}
