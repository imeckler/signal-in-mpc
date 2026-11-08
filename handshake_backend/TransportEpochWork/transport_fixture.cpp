// Public synthetic fixture only. Never receives live keys or application data.
#include "ScratchWork/VmScratch.h"
#include "LifecycleWork/SecureGmp.h"
#include "NativeCollective.h"
#include "Protocols/Opener.h"
#include <iostream>
using namespace tls_mpc_worker;

int main(int argc,char** argv) {
    if(argc!=6)return 2;
    try {
        SecureGmp::install_before_threads();
        public_require(SecureGmp::installed(),"GMP cleanup hooks unavailable");
        unsigned party=std::stoul(argv[1]),port=std::stoul(argv[3]);
        size_t capacity=std::stoul(argv[5]);
        public_require(party<5&&port>1024&&port<65530&&capacity>=6&&capacity<=16385,"invalid fixture arguments");
        PinnedPrograms pinned(argv[4]);
        ShamirOptions::singleton={5,2};
        OnlineOptions options;options.playerno=party;options.live_prep=true;
        options.security_parameter=128;options.lg2=128;options.lgp=255;
        options.prime=1;options.prime<<=255;options.prime-=19;
        Names names(party,port,std::string(argv[2]));
        public_require(names.num_players()==5,"fixture requires five parties");
        Machine<tls_mpc_worker::Share> machine(names,true,options);
        Collective collective([&]() -> Player& {return machine.get_player();},pinned.digest(),PublicBytes(32,0x3c));
        collective.public_random();
        ScratchCounts last_cleanup;size_t cleanup_calls=0;
        Worker worker(machine,pinned,[&]() {
            last_cleanup=wipe_vm_secret_scratch(machine);++cleanup_calls;
        });
        size_t rejections=0, epochs=0;
        try { machine.retire_worker_epoch(); } catch(const std::runtime_error&) { ++epochs; }
        public_require(epochs==1,"uninitialized epoch retirement accepted");
        epochs=0;
        try {wipe_vm_secret_scratch(machine);}
        catch(const std::runtime_error&){++rejections;}
        public_require(rejections==1,"uninitialized scratch visitation accepted");
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
        auto open_public=[&](const tls_mpc_worker::Bits& result) {
            public_require(result.size()%8==0,"fixture output size mismatch");
            Opener<tls_mpc_worker::Bit> opener(machine.get_player(),machine.get_bit_mac_key());
            opener.init_open();for(const auto& bit:result)opener.prepare_open(bit[0]);
            opener.exchange();std::vector<uint8_t> value(result.size()/8,0);
            for(size_t i=0;i<result.size();++i)
                value[i/8]|=(opener.finalize_open().get()&1)<<(7-i%8);
            opener.Check();return value;
        };
        auto check=[&](const tls_mpc_worker::Bits& result,const std::vector<uint8_t>& wanted) {
            public_require(open_public(result)==wanted,"public fixture output mismatch");
        };
        ScratchCounts total;
        auto sweep=[&]() {
            auto count=last_cleanup;ScratchCounts observed;
            machine.visit_secret_scratch([&](const tls_mpc_worker::Share& value) {
                public_require(value.is_zero(),"arithmetic scratch not zero");++observed.arithmetic;
            },[&](const tls_mpc_worker::Bit& value) {
                ++observed.binary_registers;observed.binary_fields+=value.get_regs().size();
                for(const auto& field:value.get_regs())
                    public_require(field.is_zero(),"binary scratch not zero");
            });
            public_require(count==observed&&count.binary_fields>0,"scratch traversal mismatch");
            total.arithmetic+=count.arithmetic;total.binary_registers+=count.binary_registers;
            total.binary_fields+=count.binary_fields;
        };
        auto renew=[&]() {
            auto stacks=ErasingThreadStack::wiped_stacks.load();
            auto limbs=SecureGmp::wiped_allocations.load();
            machine.retire_worker_epoch(); ++epochs;
            public_require(machine.get_player().get_id().find("machineepoch")==0,"host transport was not renewed");
            collective.public_random();
            public_require(ErasingThreadStack::wiped_stacks>stacks,"worker stack was not erased");
            public_require(SecureGmp::wiped_allocations>limbs,"worker GMP history not released");
            public_require(machine.queues.empty() && machine.Mp.size_s()==0 &&
                machine.bit_memories.MS.empty(), "epoch retained runtime owners/memory");
        };
        if(capacity==6) {
            auto public_point=worker.begin();sweep();
            auto public_bytes=open_public(public_point);
            renew();
            // Multiplying the base point again must reproduce the public key.
            // This checks that the external scalar survives VM cleanup.
            auto repeated=worker.agreement(Field(9));sweep();
            check(repeated,public_bytes);
        }
        auto stem="tls-route-application-"+std::to_string(capacity);
        auto first=worker.binary(stem,share(input),expected.size()*8);
        sweep();check(first,expected);
        // A queued check must reject BEFORE any visitor runs, even if the
        // worker finishes it before the host reaches the visitation call.
        ThreadJob job;job.type=CHECK_JOB;machine.queues[0]->schedule(job);
        size_t forbidden_visits=0;
        bool epoch_rejected=false;
        try { machine.retire_worker_epoch(); } catch(const std::runtime_error&) { epoch_rejected=true; }
        public_require(epoch_rejected,"epoch accepted outstanding job");
        try {machine.visit_secret_scratch([&](auto&){++forbidden_visits;},[&](auto&){++forbidden_visits;});}
        catch(const std::runtime_error&){++rejections;}
        machine.queues[0]->result();
        public_require(rejections==2&&forbidden_visits==0,"outstanding-job guard failed");
        auto next=share(input);
        for(size_t i=13*8;i<next.size();++i)next[i]=first[i];
        renew();
        auto second=worker.binary(stem,std::move(next),expected.size()*8);
        sweep();check(second,expected);
        input[11]=0;expected.assign(expected.size(),0);expected[12]=255;
        renew();
        auto rejected=worker.binary(stem,share(input),expected.size()*8);
        sweep();check(rejected,expected);
        public_require(cleanup_calls==(capacity==6?5:3),"missing automatic cleanup call");
        renew();
        public_require(epochs==(capacity==6?4:3),"epoch count mismatch");
        std::cout<<"transport epoch fixture passed: capacity="<<capacity<<"; three calls; two guards; "
                 <<total.arithmetic<<" arithmetic objects; "<<total.binary_registers
                 <<" binary registers; "<<total.binary_fields<<" fields; fresh protocol owners; no retirement receipt\n";
        return 0;
    } catch(const std::exception& error) {
        std::cerr<<"scratch fixture failed: "<<error.what()<<'\n';return 1;
    }
}
