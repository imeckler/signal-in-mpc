// TEST ONLY: a local TCP relay that adds a fixed one-way delay to every byte, in both
// directions, of every connection through it. It stands between the two workers on one
// machine so that their links behave like a link with latency (no root, no dummynet).
//
//   delay_relay DELAY_MS LISTEN:TARGET [LISTEN:TARGET ...]
//
// Every connection accepted on 127.0.0.1:LISTEN is forwarded to 127.0.0.1:TARGET. A chunk
// read at time t from one side is written to the other side at t + DELAY_MS, in order; the
// reader never waits for the writer (up to 256 MiB queued per direction), so the delay does
// not accumulate and bandwidth is not limited: this models latency only. Round trip = 2 x
// DELAY_MS. A closed side is passed on after the queued bytes, also delayed.
// On exit (SIGTERM) it prints per listening port: connections, bytes each way.
//
// The workers use it through TLS_WORKER_TEST_LINK_SHIFT (tls_worker_v3.cpp): the party that
// connects dials PORT + SHIFT instead of PORT for every link, and this relay listens there.
#include <arpa/inet.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <sys/socket.h>
#include <unistd.h>
#ifdef __APPLE__
#include <pthread/qos.h>
#endif
#include <atomic>
#include <cerrno>
#include <chrono>
#include <condition_variable>
#include <csignal>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <deque>
#include <memory>
#include <mutex>
#include <string>
#include <thread>
#include <vector>
using Clock=std::chrono::steady_clock;
static std::chrono::microseconds delay{0};
struct Counters{int listen=0,target=0;std::atomic<uint64_t>connections{0},forward{0},backward{0};};
struct Chunk{Clock::time_point due;std::vector<char>bytes;bool end=false;};
struct Pipe{
    std::mutex m;std::condition_variable changed;std::deque<Chunk>queue;size_t queued=0;
    static constexpr size_t LIMIT=size_t(256)<<20;
    void put(Chunk c){
        std::unique_lock<std::mutex>lock(m);
        changed.wait(lock,[&]{return queued<LIMIT;});
        queued+=c.bytes.size();queue.push_back(std::move(c));changed.notify_all();
    }
    Chunk take(){
        std::unique_lock<std::mutex>lock(m);
        changed.wait(lock,[&]{return !queue.empty();});
        Chunk c=std::move(queue.front());queue.pop_front();queued-=c.bytes.size();changed.notify_all();return c;
    }
};
static void nodelay(int fd){int one=1;::setsockopt(fd,IPPROTO_TCP,TCP_NODELAY,&one,sizeof one);
#ifdef SO_NOSIGPIPE
    ::setsockopt(fd,SOL_SOCKET,SO_NOSIGPIPE,&one,sizeof one);
#endif
}
// One direction: a reader that stamps what arrives and a writer that releases it when due.
static void direction(int from,int to,std::atomic<uint64_t>&count,std::shared_ptr<std::atomic<int>>open,int a,int b){
    auto pipe=std::make_shared<Pipe>();
    std::thread reader([=]{
        for(;;){
            Chunk c;c.bytes.resize(1<<16);ssize_t n;
            do{n=::read(from,c.bytes.data(),c.bytes.size());}while(n<0&&errno==EINTR);
            c.due=Clock::now()+delay;
            if(n<=0){c.bytes.clear();c.end=true;pipe->put(std::move(c));return;}
            c.bytes.resize(size_t(n));pipe->put(std::move(c));
        }
    });
    std::thread writer([=,&count]{
#ifdef __APPLE__
        // macOS lets a sleeping thread of ordinary priority wake late by a fraction of the sleep.
        pthread_set_qos_class_self_np(QOS_CLASS_USER_INTERACTIVE,0);
#endif
        for(;;){
            Chunk c=pipe->take();
            // Sleep to just before the time, then spin: a 1 ms delay must not become 1.3 ms.
            // (macOS wakes a sleeper late by about a fifth of the sleep: sleep 60% of what is left, repeatedly.)
            // Bulk traffic (full reads) is only slept for, once: its exact timing does not matter and
            // spinning for it would take the processors the interactive connections need.
            if(c.bytes.size()>=16384){auto left=c.due-Clock::now();if(left>std::chrono::microseconds(0))std::this_thread::sleep_for(left);}
            else{
                for(auto left=c.due-Clock::now();left>std::chrono::microseconds(200);left=c.due-Clock::now())std::this_thread::sleep_for(left*3/5);
                while(Clock::now()<c.due)std::this_thread::yield();
            }
            if(c.end){::shutdown(to,SHUT_WR);break;}
            size_t sent=0;bool failed=false;
            while(sent<c.bytes.size()){
                ssize_t n=::write(to,c.bytes.data()+sent,c.bytes.size()-sent);
                if(n<0&&errno==EINTR)continue;
                if(n<=0){failed=true;break;}
                sent+=size_t(n);
            }
            count+=sent;
            if(failed){::shutdown(from,SHUT_RD);break;}
        }
        if(open->fetch_sub(1)==1){::close(a);::close(b);}   // both directions done
    });
    reader.detach();writer.detach();
}
static std::vector<std::unique_ptr<Counters>>all;
static void report(int){
    for(auto&c:all)std::fprintf(stderr,"delay-relay port %d -> %d: connections=%llu bytes_forward=%llu bytes_backward=%llu\n",c->listen,c->target,
        (unsigned long long)c->connections.load(),(unsigned long long)c->forward.load(),(unsigned long long)c->backward.load());
    std::_Exit(0);
}
int main(int argc,char**argv){
    if(argc<3){std::fprintf(stderr,"usage: delay_relay DELAY_MS LISTEN:TARGET ...\n");return 2;}
    const double ms=std::atof(argv[1]);if(ms<0||ms>10000)return 2;
    delay=std::chrono::microseconds(int64_t(ms*1000));
    ::signal(SIGPIPE,SIG_IGN);
    std::vector<std::thread>acceptors;
    for(int i=2;i<argc;i++){
        int listen_port=0,target_port=0;
        if(std::sscanf(argv[i],"%d:%d",&listen_port,&target_port)!=2||listen_port<1||listen_port>65535||target_port<1||target_port>65535)return 2;
        int listener=::socket(AF_INET,SOCK_STREAM,0);int one=1;::setsockopt(listener,SOL_SOCKET,SO_REUSEADDR,&one,sizeof one);
        sockaddr_in address{};address.sin_family=AF_INET;address.sin_addr.s_addr=htonl(INADDR_LOOPBACK);address.sin_port=htons(uint16_t(listen_port));
        if(listener<0||::bind(listener,reinterpret_cast<sockaddr*>(&address),sizeof address)!=0||::listen(listener,SOMAXCONN)!=0){
            std::fprintf(stderr,"delay-relay: cannot listen on %d: %s\n",listen_port,std::strerror(errno));return 1;
        }
        all.push_back(std::make_unique<Counters>());auto*counters=all.back().get();counters->listen=listen_port;counters->target=target_port;
        acceptors.emplace_back([listener,target_port,counters]{
            for(;;){
                int client=::accept(listener,nullptr,nullptr);
                if(client<0){if(errno==EINTR)continue;return;}
                // The target may not be listening yet (the connecting worker retries; so do we, for a minute).
                int server=-1;
                for(int attempt=0;attempt<60000&&server<0;attempt++){
                    int s=::socket(AF_INET,SOCK_STREAM,0);sockaddr_in to{};to.sin_family=AF_INET;to.sin_addr.s_addr=htonl(INADDR_LOOPBACK);to.sin_port=htons(uint16_t(target_port));
                    if(s>=0&&::connect(s,reinterpret_cast<sockaddr*>(&to),sizeof to)==0)server=s;
                    else{if(s>=0)::close(s);::usleep(1000);}
                }
                if(server<0){::close(client);continue;}
                nodelay(client);nodelay(server);counters->connections++;
                auto open=std::make_shared<std::atomic<int>>(2);
                direction(client,server,counters->forward,open,client,server);
                direction(server,client,counters->backward,open,client,server);
            }
        });
    }
    ::signal(SIGTERM,report);::signal(SIGINT,report);
    std::fprintf(stderr,"delay-relay ready delay_ms=%g\n",ms);
    for(auto&t:acceptors)t.join();
    return 0;
}
