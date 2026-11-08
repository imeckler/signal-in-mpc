#pragma once
#include "Tools/PublicProtocolMetrics.h"
#include <iostream>
inline void emit_backend_totals(const char* backend){auto value=tls_public_diagnostics::snapshot();std::cout<<"DIAGNOSTIC_TOTAL {\"backend\":\""<<backend<<"\",\"bytes\":[";for(size_t i=0;i<9;++i){if(i)std::cout<<',';std::cout<<value.bytes[i];}std::cout<<"]}\n";}
inline void require_component_security(int argc,const char** argv){
 unsigned count=0;
 for(int i=1;i<argc;++i){std::string token(argv[i]);
  if(token=="-S"){if(++count!=1||i+1>=argc||std::string(argv[++i])!="128")throw std::runtime_error("component requires explicit security128");}
  else if(token.rfind("-S",0)==0||token.rfind("--security",0)==0)throw std::runtime_error("unsupported security spelling");
 }
 if(count!=1)throw std::runtime_error("component requires explicit security128");
}
