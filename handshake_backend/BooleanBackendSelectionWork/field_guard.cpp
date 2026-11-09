// Public type/configuration fixture only. No parties, secret inputs or MPC.
#include "Math/gf2n.h"
#include "Protocols/mac_key.hpp"
#include <iostream>
int main(int argc,char**argv){
 if(argc!=4)return 2;int degree=std::stoi(argv[1]),security=std::stoi(argv[2]);bool expected=std::stoi(argv[3]);
 OnlineOptions::singleton.security_parameter=security;bool rejected=false;octetStream os;int width=0;
 try{
  if(degree<=64){gf2n_short::init_field(degree);gf2n_short value(1);value.pack(os);width=gf2n_short::length();check_field_size<gf2n_short>();}
  else{gf2n_long::init_field(degree);gf2n_long value(1);value.pack(os);width=gf2n_long::length();check_field_size<gf2n_long>();}
 }catch(const field_too_small&){rejected=true;}
 if(rejected!=expected||width!=degree)return 1;
 std::cout<<"{\"field_bits\":"<<degree<<",\"configured_statistical_security\":"<<security<<",\"guard_rejected\":"<<(rejected?"true":"false")<<",\"public_field_codec_bytes\":"<<os.get_length()<<",\"MPC_executed\":false}\n";
}
