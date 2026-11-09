#include <emp-tool/emp-tool.h>
#include <emp-ag2pc/2pc.h>
#include <atomic>
#include <chrono>
#include <fstream>
#include <memory>
#include <sys/resource.h>

// Application payload bytes, including all preprocessing subchannels; excludes
// TCP/IP headers and retransmissions. Count receive separately from send.
class MeasuredIO : public emp::IOChannel<MeasuredIO> {
    emp::NetIO io;
public:
    inline static std::atomic<uint64_t> sent{0}, received{0};
    bool is_server;
    std::string addr;
    int port;
    MeasuredIO(const char* address, int p, bool quiet=false)
        : io(address,p,quiet), is_server(address==nullptr), addr(address?address:""), port(p) {}
    void send_data_internal(const void* p,size_t n) { io.send_data(p,n); sent+=n; }
    void recv_data_internal(void* p,size_t n) { io.recv_data(p,n); received+=n; }
    void flush() { io.flush(); }
    void sync() { io.sync(); }
};
using Clock=std::chrono::steady_clock;
double seconds(Clock::time_point t) {return std::chrono::duration<double>(Clock::now()-t).count();}

int main(int argc,char**argv) {
    if(argc!=7) return 2; // party port Bristol own-input-bits output-file metrics-file
    int party=std::stoi(argv[1]),port=std::stoi(argv[2]);
    try {
        auto start=Clock::now(), load=start;
        emp::BristolFormat circuit(argv[3]);
        double load_seconds=seconds(load);
        size_t total=circuit.n1+circuit.n2;
        std::unique_ptr<bool[]> input(new bool[total]()), output(new bool[circuit.n3]());
        std::ifstream in(argv[4],std::ios::binary);
        size_t begin=party==emp::BOB?0:circuit.n1;
        size_t count=party==emp::BOB?circuit.n1:circuit.n2;
        for(size_t i=0;i<count;i++) {char bit;if(!in.get(bit)||bit<0||bit>1) return 3;input[begin+i]=bit;}
        char extra;if(in.get(extra)) return 3;
        MeasuredIO io(party==emp::ALICE?nullptr:"127.0.0.1",port,true);
        auto setup=Clock::now();
        emp::C2PC<MeasuredIO> protocol(&io,party,&circuit);
        io.flush();
        double setup_seconds=seconds(setup);
        auto independent=Clock::now();
        protocol.function_independent();io.flush();
        double independent_seconds=seconds(independent);
        auto dependent=Clock::now();
        protocol.function_dependent();io.flush();
        double dependent_seconds=seconds(dependent);
        uint64_t offline_sent=MeasuredIO::sent,offline_received=MeasuredIO::received;
        // Deterministic negative control: Delta has low bit1, so toggling bit2
        // produces neither valid output-key candidate under the20-bit check.
        if(party==emp::BOB && std::getenv("EMP_TEST_CORRUPT_OUTPUT_KEY"))
            protocol.key[circuit.num_wire-circuit.n3] = protocol.key[circuit.num_wire-circuit.n3] ^ emp::makeBlock(0,4);
        auto online=Clock::now();
        protocol.online(input.get(),output.get(),false);io.flush();
        double online_seconds=seconds(online);
        // Only Bob receives padded results. Alice must never receive these.
        if(party==emp::BOB) {
            std::ofstream out(argv[5],std::ios::binary);
            for(int i=0;i<circuit.n3;i++) out.put(output[i]?1:0);
        }
        rusage usage{};getrusage(RUSAGE_SELF,&usage);
        auto tv=[](timeval t){return t.tv_sec+t.tv_usec/1e6;};
        std::ofstream report(argv[6]);
        report<<"{\"party\":"<<party<<",\"load_seconds\":"<<load_seconds
              <<",\"setup_seconds\":"<<setup_seconds<<",\"independent_seconds\":"<<independent_seconds
              <<",\"dependent_seconds\":"<<dependent_seconds<<",\"online_seconds\":"<<online_seconds
              <<",\"wall_seconds\":"<<seconds(start)<<",\"cpu_seconds\":"<<tv(usage.ru_utime)+tv(usage.ru_stime)
              <<",\"peak_rss_bytes\":"<<usage.ru_maxrss
              <<",\"sent_bytes\":"<<MeasuredIO::sent<<",\"received_bytes\":"<<MeasuredIO::received
              <<",\"offline_sent_bytes\":"<<offline_sent<<",\"offline_received_bytes\":"<<offline_received
              <<",\"generated_triples\":"<<protocol.fpre->batch_size
              <<",\"consumed_ands\":"<<protocol.num_ands<<"}\n";
        return 0;
    } catch(...) { std::cerr<<"benchmark rejected category=backend-exception\n";return 4; }
}
