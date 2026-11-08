#pragma once
#include <exception>
#include <atomic>
#include <utility>
namespace tls_caught_failure {
#ifdef TLS_CAUGHT_FAILURE_TEST_HOOKS
inline std::atomic<unsigned> fixture_fault_stage{0};
#endif
template<class F> class OnUnwind {
 F callback;int entered=std::uncaught_exceptions();
public:
 explicit OnUnwind(F callback):callback(std::move(callback)){}
 OnUnwind(const OnUnwind&)=delete;
 ~OnUnwind()noexcept{if(std::uncaught_exceptions()>entered)callback();}
};
template<class F> OnUnwind(F)->OnUnwind<F>;
}
