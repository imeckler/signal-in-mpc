#pragma once
// Local helper-container hygiene only, not complete protocol/PRNG retirement.
#include <sodium.h>
#include <memory>
#include <type_traits>
#include <vector>
namespace signal_mpc::recovery::import_v2 {
template<class T,class Release>void wipe_then_release(T* pointer,size_t count,Release&& release)noexcept{
 static_assert(std::is_trivially_destructible_v<T>,"only pinned scalar/share value storage");
 if(pointer)sodium_memzero(pointer,count*sizeof(T));
 release(pointer,count);
}
template<class T>struct WipingAllocator {
 using value_type=T;using is_always_equal=std::true_type;
 WipingAllocator()noexcept=default;
 template<class U>WipingAllocator(const WipingAllocator<U>&)noexcept{}
 T* allocate(size_t n){return std::allocator<T>{}.allocate(n);}
 void deallocate(T* pointer,size_t count)noexcept{
  wipe_then_release(pointer,count,[](T* p,size_t n)noexcept{std::allocator<T>{}.deallocate(p,n);});
 }
 template<class U>bool operator==(const WipingAllocator<U>&)const noexcept{return true;}
};
template<class T>using PrivateVector=std::vector<T,WipingAllocator<T>>;
}
