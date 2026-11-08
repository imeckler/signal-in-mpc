#pragma once
#include <exception>
#include <atomic>
#include <utility>
#include <memory>
#include "SocketCancellation.h"
namespace tls_caught_failure {
inline std::atomic<size_t> runtime_threads_started{0}, runtime_threads_joined{0};
inline std::atomic<bool> runtime_join_error{false};
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
