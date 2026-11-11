#pragma once
// Where the other party's worker is, and where this one listens.
//
// Two workers talk over: the Boolean engine's channel and every sibling it opens (its second
// channel and the AND-triple factories' channels: all on PORT), and the field engine's
// connections (the engine and its triple-stock lines: all on PORT+10). Party 0 listens on both
// and party 1 dials; nothing ever dials party 1. The controllers do not talk to each other.
//
//   TLS_WORKER_PEER=A.B.C.D   the other party's address (IPv4, numeric). Unset or 127.0.0.1:
//                             both parties on this machine, exactly as before. Only party 1
//                             dials it, but set it on both: it also selects the field engine's
//                             direct connection, which both parties must use alike.
//   TLS_WORKER_LISTEN=A.B.C.D the address the Boolean engine's listener binds (party 0 only).
//                             Unset: all interfaces, as before.
//
// With a peer set the field engine's parties connect directly (field_engine.h, `peer`): party 0
// listens on PORT+10 and party 1 dials the peer there. The field engine's library binds its
// listeners to all interfaces and has no setting for that; its connections are TLS with the two
// parties' certificates (Player-Data/). Restrict those ports with the firewall or the tunnel.
//
// Nothing here is cryptography: it only decides which address a socket binds or dials.
#include <emp-tool/emp-tool.h>
#include <arpa/inet.h>
#include <cstdlib>
#include <memory>
#include <stdexcept>
#include <string>
namespace emp_hybrid {
struct PeerLink {
    std::string peer="127.0.0.1",listen;   // listen empty: all interfaces
    bool remote()const{return peer!="127.0.0.1";}
    static bool ipv4(const std::string&text){in_addr parsed{};return !text.empty()&&::inet_pton(AF_INET,text.c_str(),&parsed)==1;}
    // Throws on a value that is not a numeric IPv4 address: a typo must not fall back to localhost.
    static PeerLink make(const char*peer_text,const char*listen_text){
        PeerLink link;
        if(peer_text&&*peer_text){if(!ipv4(peer_text))throw std::invalid_argument("peer address");link.peer=peer_text;}
        if(listen_text&&*listen_text){if(!ipv4(listen_text))throw std::invalid_argument("listen address");link.listen=listen_text;}
        return link;
    }
    static PeerLink from_environment(){return make(std::getenv("TLS_WORKER_PEER"),std::getenv("TLS_WORKER_LISTEN"));}
    // The field engine's `peer` argument: null keeps its local coordination exchange.
    const char*field_peer()const{return remote()?peer.c_str():nullptr;}
    // The Boolean engine's channel. `listener`: this party accepts (ALICE in every fixture and
    // the worker); the other dials `peer` on `port`. Siblings follow the channel they come from.
    std::unique_ptr<emp::NetIO> open(bool listener,unsigned port)const{
        if(!listener)return std::make_unique<emp::NetIO>(peer.c_str(),int(port),true);
        if(listen.empty())return std::make_unique<emp::NetIO>(nullptr,int(port),true);
        // As NetIO's own listening constructor (emp-tool tcp_socket.h, open_listener), bound to one address.
        sockaddr_in at{};at.sin_family=AF_INET;at.sin_port=htons(uint16_t(port));
        if(port>65535||::inet_pton(AF_INET,listen.c_str(),&at.sin_addr)!=1)throw std::invalid_argument("listen address");
        const int fd=::socket(AF_INET,SOCK_STREAM,0);if(fd<0)throw std::runtime_error("listen socket");
        auto handle=std::make_shared<emp::tcp::ListenerHandle>(fd);
        emp::tcp::apply_socket_options(fd,emp::tcp::SocketOptions{});
        int reuse=1;::setsockopt(fd,SOL_SOCKET,SO_REUSEADDR,&reuse,sizeof reuse);
        if(::bind(fd,reinterpret_cast<sockaddr*>(&at),sizeof at)<0||::listen(fd,SOMAXCONN)<0)throw std::runtime_error("listen on "+listen+":"+std::to_string(port));
        auto io=std::make_unique<emp::NetIO>(emp::tcp::accept_one_confirmed(fd),true);
        io->is_server=true;io->port_=int(port);io->listener=std::move(handle);
        return io;
    }
};
}
