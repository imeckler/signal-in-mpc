#include <emp-ag2pc/emp-ag2pc.h>
#include "pad_program.h"
#include <array>
#include <fstream>
#include <iostream>
using namespace emp;
using C=AG2PCSession::ctx_t;
template<int N>using V=BitVec_T<C,N>;
template<int N>static typename V<N>::clear_t random_bits(){typename V<N>::clear_t out{};std::array<uint8_t,N>x{};PRG prg;prg.random_data_unaligned(x.data(),x.size());for(int i=0;i<N;i++)out[i]=x[i]&1;return out;}
int main(int argc,char**argv){
    if(argc!=5)return 2;
    try{
        int party=std::stoi(argv[1]),port=std::stoi(argv[2]);std::string mode=argv[3];if(party!=ALICE&&party!=BOB)return 2;
        NetIO io(party==ALICE?nullptr:"127.0.0.1",port,true);ThreadPool pool(4);AG2PCSession s(&io,&pool,party,40);
        if(mode=="input"||mode=="bob-input"){
            int owner=mode=="input"?ALICE:BOB;V<256>::clear_t clear{};
            if(party==owner){std::ifstream f(argv[4],std::ios::binary);for(auto&b:clear){char x;if(!f.get(x)||x<0||x>1)throw std::runtime_error("fixture bit input");b=x;}char extra;if(f.get(extra))throw std::runtime_error("fixture input size");}
            auto private_input=s.input<V<256>>(owner,clear);s.checkpoint(private_input);
            std::cout<<"input_fixture settled_without_opening=1\n";
        }else if(mode=="public"){
            auto bit=s.input<V<1>>(ALICE,{true});auto clear=s.reveal(bit,PUBLIC);
            if(!clear)throw std::runtime_error("missing public result");std::cout<<"output_fixture accepted_value="<<(*clear)[0]<<"\n";
        }else if(mode=="gamma"){
            auto a=s.input<V<1>>(ALICE,{true}),b=s.input<V<1>>(BOB,{true});
            circuit::BooleanProgram p;p.num_inputs=2;p.num_wires=3;p.gates={{0,1,2,circuit::Op::And}};p.outputs={2};auto padded=emp_hybrid::pad_program(p);
            auto da=s.input<V<1023>>(ALICE,random_bits<1023>()),db=s.input<V<1023>>(BOB,random_bits<1023>());
            auto result=s.run_artifact<V<1024>>(padded.program,a,b,da,db);s.checkpoint(result);
            std::array<uint32_t,1024>ids{};result.pack_wires(ids.data());auto original=V<1>::from_wires(s.ctx(),ids.data());
            auto clear=s.reveal(original,ALICE);if(party==ALICE){if(!clear)throw std::runtime_error("missing A result");std::cout<<"output_fixture accepted_value="<<(*clear)[0]<<"\n";}
        }else return 2;
    }catch(...){std::cerr<<"boundary probe rejected category=adapter\n";return 4;}
}
