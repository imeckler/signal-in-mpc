// Public synthetic component fixture ONLY. It deliberately opens every output
// to check memory I/O and the router. It neither activates Session nor implements
// retirement, and must never receive live application inputs or keys.
#include "NativeWorker.h"
#include "NativeCollective.h"
#include "ShapeCompiler.h"
#include "Protocols/Opener.h"
#include <iostream>
using namespace tls_mpc_worker;
int main(int argc,char** argv) {
    if(argc!=7)return 2;
    try {
        unsigned party=std::stoul(argv[1]),port=std::stoul(argv[3]);
        size_t capacity=std::stoul(argv[5]);
        public_require(party<5&&port>1024&&port<65530&&capacity>=6&&capacity<=16385,"invalid fixture arguments");
        PinnedPrograms pinned(argv[4]);
        std::string encoded=argv[6],digits="0123456789abcdef";
        public_require(encoded.size()==64,"invalid public fixture context");
        PublicBytes session_id;
        for(size_t i=0;i<64;i+=2) {
            auto a=digits.find(encoded[i]),b=digits.find(encoded[i+1]);
            public_require(a<16&&b<16,"invalid public fixture context");session_id.push_back(16*a+b);
        }
        ShamirOptions::singleton={5,2};
        OnlineOptions options;options.playerno=party;options.live_prep=true;
        options.security_parameter=128;options.lg2=128;options.lgp=255;
        options.prime=1;options.prime<<=255;options.prime-=19;
        Names names(party,port,std::string(argv[2]));
        public_require(names.num_players()==5,"fixture requires five parties");
        Machine<tls_mpc_worker::Share> machine(names,true,options);
        Collective collective(machine.get_player(),pinned.digest(),session_id);
        ShapeCompiler shapes(pinned,[&](const std::string& shape,const PublicBytes& digest){
            collective.agree_program(shape,digest);
        });
        shapes.prepare(KernelShape::route(capacity));
        Worker worker(machine,pinned);
        std::vector<uint8_t> input(capacity+15,0),expected(capacity+15,0);
        size_t length=capacity-1;
        input[11]=255;input[12]=23;input[13]=length>>8;input[14]=length&255;
        for(size_t i=0;i<length;++i)input[15+i]=(i*73+19)&255;
        expected=input;expected[0]=1;expected[11]=0;expected[12]=0;
        auto share=[&](const std::vector<uint8_t>& value) {
            auto result=worker.allocate(value.size()*8);
            for(size_t i=0;i<value.size()*8;++i)result[i][0]=tls_mpc_worker::Bit::constant(
                (value[i/8]>>(7-i%8))&1,party,machine.get_bit_mac_key());
            return result;
        };
        auto check=[&](const tls_mpc_worker::Bits& result,const std::vector<uint8_t>& wanted) {
            public_require(result.size()==wanted.size()*8,"fixture output size mismatch");
            Opener<tls_mpc_worker::Bit> opener(machine.get_player(),machine.get_bit_mac_key());
            opener.init_open();for(const auto& bit:result)opener.prepare_open(bit[0]);
            opener.exchange();bool correct=true;
            for(size_t i=0;i<result.size();++i)
                correct&=(opener.finalize_open().get()&1)==((wanted[i/8]>>(7-i%8))&1);
            opener.Check();public_require(correct,"public fixture output mismatch");
        };
        const auto stem="tls-route-application-"+std::to_string(capacity);
        auto first=worker.binary(stem,share(input),expected.size()*8);
        check(first,expected);
        // Feed the actual protocol-produced shares back through memory I/O.
        // Their local field values need not be bits, unlike public constants.
        auto next=share(input);
        for(size_t i=13*8;i<next.size();++i)next[i]=first[i];
        auto second=worker.binary(stem,std::move(next),expected.size()*8);
        check(second,expected);
        input[11]=0;expected.assign(expected.size(),0);expected[12]=255;
        auto rejected=worker.binary(stem,share(input),expected.size()*8);
        check(rejected,expected);
        std::cout<<"public router fixture passed: capacity="<<capacity<<"; three calls; no application activation\n";
        return 0;
    } catch(const std::exception& error) {
        std::cerr<<"public router fixture failed: "<<error.what()<<'\n';return 1;
    }
}
