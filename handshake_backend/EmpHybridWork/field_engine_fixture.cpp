#include "field_engine.h"
#include <iostream>
#include <stdexcept>
int main(int argc,char**argv){
    if(argc!=3)return 2;
    try{
        unsigned party=std::stoul(argv[1]),port=std::stoul(argv[2]);
        emp_hybrid::FieldEngine engine(party,port);
        auto x=engine.input_coins({party?7u:5u,party?11u:3u});
        auto product=engine.mul(x[0],x[1]);
        auto sum=engine.add(product[0],product[1]);
        auto expected=engine.constant(68);
        auto delta=engine.sub(sum,expected);
        auto check=engine.checked_open({delta});
        for(auto b:check.at(0))if(b)throw std::runtime_error("fixture equality");
        // Second operation consumes retained authenticated product rather than
        // reinputting it. No raw product/sender value is revealed.
        auto square=engine.mul({sum},{sum});
        auto equality=engine.sub(square[0],engine.constant(4624));
        check=engine.checked_open({equality});
        for(auto b:check.at(0))if(b)throw std::runtime_error("continuation equality");
        std::cout<<"native field fixture passed equality_only=2\n";
    }catch(...){std::cerr<<"native field fixture rejected category=protocol-or-adapter\n";return 4;}
}
