// Public local storage values only, no MPC or key/share openings.
#include "RawFieldReadmitV2.h"
#include "NativeWorker.h"
#include <iostream>
using namespace signal_mpc::recovery::import_v2;
int main(){try{gf2n_long::init_field(128);using Field=gf2n_long;using Share=tls_mpc_worker::StrongShamirShare<Field>;size_t checks=0;
 static_assert(std::is_nothrow_destructible_v<Field>&&std::is_nothrow_destructible_v<Share>);
 for(size_t count:{size_t(1),size_t(17),size_t(4096)}){
  auto* p=std::allocator<Field>{}.allocate(count);for(size_t i=0;i<count;++i)std::construct_at(p+i,Field(73));
  for(size_t i=0;i<count;++i)std::destroy_at(p+i);
  wipe_then_release(p,count,[&](Field* data,size_t n)noexcept{auto* bytes=reinterpret_cast<unsigned char*>(data);for(size_t i=0;i<n*sizeof(Field);++i)if(bytes[i]!=0)std::abort();++checks;std::allocator<Field>{}.deallocate(data,n);});
  PrivateVector<Field> fields;fields.reserve(count);for(size_t i=0;i<count;++i)fields.push_back(Field(int(i+1)));fields.reserve(2*count);for(size_t i=0;i<count;++i)if(fields[i]!=Field(int(i+1)))throw std::runtime_error("private allocator changed values");++checks;
  PrivateVector<Share> shares(count,Share(Field(9)));auto moved=std::move(shares);if(moved.size()!=count||static_cast<const Field&>(moved.back())!=Field(9))throw std::runtime_error("private allocator changed share move");++checks;
 }
 std::cout<<checks<<" wiping allocator checks passed\n";return 0;
 }catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 1;}}
