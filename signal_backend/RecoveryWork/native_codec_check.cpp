// PUBLIC local-field codec fixture; no private-MPC import or reconstruction.
#include "NativeOwnShareArchive.h"
#include <iostream>
using namespace signal_mpc::recovery;
int main(){try{gf2n_long::init_field(128);size_t checks=0;
 for(size_t i=0;i<128;++i){gf2n_long field(1);field<<=i;unsigned char bytes[16];detail::encode_own_evaluation(bytes,field);
  for(size_t j=0;j<128;++j){require(((bytes[j/8]>>(j%8))&1)==(j==i),"local GF128 archive basis mismatch");++checks;}}
 auto method=&NativeOwnShareArchive::seal;(void)method;
 std::cout<<checks<<" native GF128 basis/typed archive checks passed\n";return 0;
 }catch(const std::exception& e){std::cerr<<e.what()<<'\n';return 1;}}
