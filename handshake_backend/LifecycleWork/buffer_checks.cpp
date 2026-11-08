// Public synthetic payloads only. Observe live allocations immediately before free.
#include "Tools/octetStream.h"
#include "Tools/FlexBuffer.h"
#include "Tools/Hash.h"
#include "Tools/BitVector.h"
#include "Networking/Exchanger.h"
#include <cstdlib>
#include <new>
#include <thread>
#include <atomic>
#include <sys/socket.h>
#include <unistd.h>
#include <fcntl.h>
#include <cstring>
#include <iostream>

namespace {
void* watched = nullptr;
size_t watched_size = 0, releases = 0;
bool fail_next = false;
void checked(bool ok, int line) { if (!ok) { std::cerr << "buffer check failed at line " << line << "\n"; std::abort(); } }
#define require(ok) checked((ok), __LINE__)
void watch(void* p, size_t n) { require(!watched && p && n); watched=p; watched_size=n; }
void released() { if(watched) std::cerr << "observer missed release after " << releases << " observations\n"; require(!watched); }
void fill(octetStream& s, size_t n) { s.reset_write_head(); auto p=s.append(n); memset(p,0xa5,n); }
template<class F> void failure(F f) {
    fail_next=true;
    try { f(); require(false); } catch (const std::bad_alloc&) { require(!fail_next); }
}
}
void* operator new[](size_t n) {
    if (fail_next) { fail_next=false; throw std::bad_alloc(); }
    if (auto p=std::malloc(n ? n : 1)) return p;
    throw std::bad_alloc();
}
void operator delete[](void* p) noexcept {
    if (p && p==watched) {
        const unsigned char* b=static_cast<unsigned char*>(p);
        for (size_t i=0;i<watched_size;i++) require(b[i]==0);
        watched=nullptr; ++releases;
    }
    std::free(p);
}

int main() {
    // Growth, borrowed consume, cursors, self-assignment and copy independence.
    {
        octetStream s; fill(s,32); s.consume(7);
        auto borrowed=s.get_data(); require(borrowed[0]==0xa5);
        s.assign(s); require(s.get_ptr()==7 && s.get_length()==32);
        failure([&]{s.resize_precise(128);});
        require(s.get_data()==borrowed && s.get_ptr()==7 && s.get_length()==32);
        memset(s.get_data(),0xa5,s.get_max_length()); watch(s.get_data(),s.get_max_length());
        s.resize_precise(128); released(); require(s.get_ptr()==7 && s.get_length()==32);
        octetStream copy(s); require(copy==s && copy.get_ptr()==7);
        memset(s.get_data(),0xa5,s.get_max_length()); watch(s.get_data(),s.get_max_length());
        s.resize_precise(4); released(); require(s.get_length()==4 && s.get_ptr()==4);
        require(copy.get_length()==32 && copy.get_data()[0]==0xa5);
        watch(s.get_data(),s.get_max_length()); s.clear(); released(); require(s.empty());
        fill(s,8); memset(s.get_data(),0xa5,s.get_max_length()); watch(s.get_data(),s.get_max_length());
    }
    released();
    {
        octetStream source, dest; fill(source,100); source.consume(9); fill(dest,8);
        auto old=dest.get_data(); failure([&]{dest.assign(source);});
        require(dest.get_data()==old && dest.get_length()==8 && dest.get_ptr()==0);
        memset(dest.get_data(),0xa5,dest.get_max_length()); watch(dest.get_data(),dest.get_max_length());
        dest=source; released(); require(dest==source && dest.get_ptr()==9);
        // Reused allocation replacement also clears the discarded suffix.
        octetStream small; fill(small,3); dest=small;
        for(size_t i=3;i<dest.get_max_length();i++) require(dest.get_data()[i]==0);
    }
    {
        octetStream bits; bits.store_bits<3>(5); octetStream copy(bits);
        failure([&]{bits.resize_precise(32);});
        bits.resize_precise(32); bits.flush_bits(); copy.flush_bits(); require(bits==copy);
        bits.reset_read_head(); require(bits.get_bits<2>()==1);
        octetStream reading(bits); bits.resize_precise(64);
        require(bits.get_bits<3>()==reading.get_bits<3>());
        // Hash::final intentionally shrinks an existing destination.
        fill(bits,100); bits.consume(90); Hash h; h.update(std::string("abc")); h.final(bits);
        require(bits.get_ptr()==0 && bits.get_length()==crypto_generichash_BYTES);
        octet expected[crypto_generichash_BYTES];
        crypto_generichash(expected,sizeof(expected),(const octet*)"abc",3,nullptr,0);
        require(memcmp(bits.get_data(),expected,sizeof(expected))==0);
    }
    {
        octetStream s; fill(s,20); s.consume(6); auto allocation=s.get_data();
        LocalBuffer buffer; static_cast<FlexBuffer&>(buffer)=s;
        require(s.empty() && buffer.data()==(char*)allocation && buffer.left()==14);
        auto p=buffer.data(); failure([&]{buffer.resize_copy(128);});
        require(buffer.data()==p && buffer.size()==20 && buffer.left()==14);
        memset(buffer.data(),0xa5,buffer.capacity()); watch(buffer.data(),buffer.capacity());
        buffer.resize_copy(128); released(); require(buffer.size()==20 && buffer.left()==14);
        for(size_t i=0;i<20;i++) require((unsigned char)buffer.data()[i]==0xa5);
        failure([&]{static_cast<ReceivedMsg&>(buffer).resize(256);});
        require(buffer.size()==20 && buffer.left()==14);
        octetStream moved(buffer); require(buffer.size()==0 && moved.get_ptr()==6 && moved.get_length()==20);
        memset(moved.get_data(),0xa5,moved.get_max_length()); watch(moved.get_data(),moved.get_max_length());
    }
    released();
    {
        LocalBuffer a,b; static_cast<ReceivedMsg&>(a).resize(17); static_cast<ReceivedMsg&>(b).resize(5);
        memset(b.data(),0xa5,b.capacity()); watch(b.data(),b.capacity()); static_cast<FlexBuffer&>(b)=a; released();
        require(a.size()==0 && b.size()==17); static_cast<FlexBuffer&>(b)=b; require(b.size()==17);
        memset(b.data(),0xa5,b.capacity()); watch(b.data(),b.capacity());
        static_cast<ReceivedMsg&>(b).resize(100); released();
        memset(b.data(),0xa5,b.capacity()); watch(b.data(),b.capacity());
    }
    released();
    {
        octetStream s; fill(s,11); s.consume(4);
        LocalBuffer destination; static_cast<ReceivedMsg&>(destination).resize(9);
        memset(destination.data(),0xa5,destination.capacity());
        watch(destination.data(),destination.capacity());
        static_cast<FlexBuffer&>(destination)=s; released();
        require(s.empty() && destination.size()==11 && destination.left()==7);
        memset(destination.data(),0xa5,destination.capacity());
        watch(destination.data(),destination.capacity());
    }
    released();
    {
        LocalBuffer empty;
        octetStream zero(empty); require(zero.empty() && !zero.get_data());
        static_cast<FlexBuffer&>(empty)=zero;
        require(empty.size()==0 && !empty.data());
        octetStream copied(zero); zero.assign(copied); require(zero.empty());
    }
    {
        int pair[2]; require(socketpair(AF_UNIX,SOCK_STREAM,0,pair)==0);
        require(fcntl(pair[0],F_SETFL,O_NONBLOCK)==0);
        octetStream s; fill(s,32); auto allocation=s.get_data(); auto capacity=s.get_max_length();
        size_t incoming=1<<20; send(pair[1],incoming,LENGTH_SIZE);
        try {
            Exchanger<int> exchanger(pair[0],s,pair[0],s);
            fail_next=true; exchanger.round(false); require(false);
        } catch(const std::bad_alloc&) { require(!fail_next); }
        require(s.get_data()==allocation && s.get_max_length()==capacity && s.empty() && s.get_ptr()==0);
        close(pair[0]); close(pair[1]);
    }
    {
        BitVector value(128); memset(value.get_ptr(),0xa5,16); watch(value.get_ptr(),16);
        value.resize_exact(512); released();
        for(size_t i=0;i<16;++i)require(value.get_ptr()[i]==0xa5);
        memset(value.get_ptr(),0xa5,64); value.resize(0);
        watch(value.get_ptr(),64);
    }
    released();
    // An incoming length is processed while only a small prefix has been sent.
    // The same stream reallocates, then continues partial sends using its new owner.
    int fd[2]; require(socketpair(AF_UNIX,SOCK_STREAM,0,fd)==0);
    require(fcntl(fd[0],F_SETFL,O_NONBLOCK)==0);
    int small=1024; require(setsockopt(fd[0],SOL_SOCKET,SO_SNDBUF,&small,sizeof(small))==0);
    constexpr size_t outgoing=1<<20, incoming=3<<20;
    octetStream stream; fill(stream,outgoing);
    std::atomic<bool> grown{false};
    auto old_capacity=stream.get_max_length();
    std::thread peer([&]{
        size_t n=0; receive(fd[1],n,LENGTH_SIZE); require(n==outgoing);
        send(fd[1],incoming,LENGTH_SIZE);
        while(!grown.load()) std::this_thread::yield();
        std::vector<octet> sent(outgoing); receive(fd[1],sent.data(),sent.size());
        for(auto x:sent) require(x==0xa5);
        std::vector<octet> reply(incoming,0x3c); send(fd[1],reply.data(),reply.size());
    });
    {
        Exchanger<int> exchanger(fd[0],stream,fd[0],stream);
        while(stream.get_max_length()==old_capacity) require(exchanger.round(false));
        grown.store(true);
        while(exchanger.round()) {}
    }
    peer.join(); close(fd[0]); close(fd[1]);
    require(stream.get_length()==incoming && stream.get_ptr()==0);
    for(size_t i=0;i<incoming;i++) require(stream.get_data()[i]==0x3c);
    std::cout << "serialized buffer cleanup passed: " << releases << " observed releases; allocation failures; copies/bits/transfers/zero-size; allocation-failure exchange unwind; partial socket exchange\n";
}
