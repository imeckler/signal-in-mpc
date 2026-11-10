#pragma once
// Run a callable on a thread with an explicit large stack. The typed Boolean
// values hold their wire ids inline, so large mask batches need more than the
// default main-thread stack. Exceptions are carried back to the caller.
#include <pthread.h>
#include <cstddef>
#include <exception>
#include <functional>
#include <stdexcept>
namespace emp_hybrid {
inline void run_with_stack(size_t bytes,std::function<void()> body){
    struct Job {std::function<void()> body;std::exception_ptr error;} job{std::move(body),nullptr};
    pthread_attr_t attr;if(pthread_attr_init(&attr)||pthread_attr_setstacksize(&attr,bytes))throw std::runtime_error("stack attribute");
    pthread_t thread;
    int rc=pthread_create(&thread,&attr,[](void*p)->void*{auto*j=static_cast<Job*>(p);try{j->body();}catch(...){j->error=std::current_exception();}return nullptr;},&job);
    pthread_attr_destroy(&attr);if(rc)throw std::runtime_error("stack thread");
    pthread_join(thread,nullptr);if(job.error)std::rethrow_exception(job.error);
}
}
