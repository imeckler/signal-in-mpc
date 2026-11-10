#include <emp-ag2pc/emp-ag2pc.h>
#include "pad_program.h"
#include <array>
#include <iostream>
using namespace emp;
int main(int argc,char**argv){
    if(argc!=3)return 2;
    int party=std::stoi(argv[1]),port=std::stoi(argv[2]);if(party!=ALICE&&party!=BOB)return 2;
    try{
        using C=AG2PCSession::ctx_t;using I=BitVec_T<C,2>;using D=BitVec_T<C,1023>;using R=BitVec_T<C,1024>;using O=BitVec_T<C,1>;
        circuit::BooleanProgram p;p.num_inputs=4;p.num_wires=7;
        p.gates={{0,2,4,circuit::Op::Xor},{1,3,5,circuit::Op::Xor},{4,5,6,circuit::Op::And}};p.outputs={6};
        auto padded=emp_hybrid::pad_program(p);
        NetIO io(party==ALICE?nullptr:"127.0.0.1",port,true);ThreadPool pool(4);
        {
            AG2PCSession session(&io,&pool,party,40);I::clear_t bv{},av{};D::clear_t random{};
            // Logical fixture bits1,1 split as Bob(1,0) XOR Alice(0,1).
            if(party==BOB)bv={true,false};else av={false,true};
            PRG prg;std::array<uint8_t,1023>raw{};prg.random_data(raw.data(),raw.size());
            for(size_t i=0;i<raw.size();i++)random[i]=raw[i]&1;
            auto b=session.input<I>(BOB,bv),a=session.input<I>(ALICE,av);
            auto db=session.input<D>(BOB,random),da=session.input<D>(ALICE,random);
            if(party==BOB&&std::getenv("EMP_TEST_CORRUPT_PADDED_DELTA"))session.protocol().Delta=session.protocol().Delta^makeBlock(0,4);
            auto result=session.run_artifact<R>(padded.program,b,a,db,da);
            session.checkpoint(result);
            std::array<uint32_t,1024>wires{};result.pack_wires(wires.data());
            auto original=O::from_wires(session.ctx(),wires.data());session.checkpoint(original);
            auto clear=session.reveal(original,BOB);
            if(party==BOB&&(!clear||!(*clear)[0]))throw std::runtime_error("output mismatch");
            if(session.num_and()!=1024)throw std::runtime_error("padding did not execute");
            std::cout<<"fixture passed real_ands=1 checked_ands=1024 dummy_outputs_opened=0\n";
        }
    }catch(...){std::cerr<<"fixture rejected category=adapter-exception\n";return 4;}
}
