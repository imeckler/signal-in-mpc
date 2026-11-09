#pragma once
#include "NativeWorker.h"
namespace signal_mpc {
class UpgradeShape {
 size_t password_;
public:
 explicit UpgradeShape(size_t password):password_(password){if(password>256)throw std::runtime_error("upgrade password too long");}
 size_t input_bytes()const{return 32+password_;}
 size_t output_bytes()const{return 265+4*((37+password_+2)/3);}
 std::string name()const{return "signal_relay_upgrade_"+std::to_string(password_);}
 std::string descriptor()const{return "Programs/Functions/"+name()+"-sbv:["+
  std::to_string(8*input_bytes())+"x1]-sbv:["+std::to_string(8*output_bytes())+"x1]";}
};
class NativeUpgrade {
 Machine<tls_mpc_worker::Share>& machine_;
 tls_mpc_worker::Worker& allocation_;
 const tls_mpc_worker::PinnedPrograms& pinned_;
public:
 NativeUpgrade(Machine<tls_mpc_worker::Share>& m,tls_mpc_worker::Worker& w,const tls_mpc_worker::PinnedPrograms& p)
  :machine_(m),allocation_(w),pinned_(p){}
 // Shared UUID16,passwordN,public-fresh-WebSocket-key16. No credential opening.
 tls_mpc_worker::Bits evaluate(const UpgradeShape& shape,tls_mpc_worker::Bits input){
  if(input.size()!=shape.input_bytes()*8)throw std::runtime_error("upgrade input size mismatch");
  auto output=allocation_.allocate(shape.output_bytes()*8);
  std::vector<FunctionArgument> args={{1,input.function_argument()},{1,output.function_argument()}};
  pinned_.verify_function(shape.name(),args);FunctionArgument ignored;machine_.run_function(shape.name(),ignored,args);return output;
 }
};
}
