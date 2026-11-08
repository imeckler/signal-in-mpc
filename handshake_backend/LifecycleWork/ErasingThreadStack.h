#pragma once
#include <sodium.h>
#include <sys/mman.h>
#include <unistd.h>
#include <atomic>
#include <stdexcept>

// A worker stack has one exclusive owner. Erase/release only after pthread_join.
class ErasingThreadStack {
    void* mapping;
    size_t mapped_size, page;
public:
    void* data;
    size_t size;
    static inline std::atomic<size_t> wiped_stacks{0}, wiped_bytes{0};
    explicit ErasingThreadStack(size_t requested=8*1024*1024) {
        page=static_cast<size_t>(getpagesize());
        size=(requested+page-1)/page*page;
        mapped_size=size+2*page;
        mapping=mmap(nullptr,mapped_size,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANON,-1,0);
        if(mapping==MAP_FAILED) throw std::runtime_error("worker stack allocation failed");
        data=static_cast<char*>(mapping)+page;
        if(mprotect(mapping,page,PROT_NONE) ||
            mprotect(static_cast<char*>(data)+size,page,PROT_NONE)) {
            munmap(mapping,mapped_size);
            throw std::runtime_error("worker stack guard setup failed");
        }
    }
    ErasingThreadStack(const ErasingThreadStack&)=delete;
    ErasingThreadStack& operator=(const ErasingThreadStack&)=delete;
    void erase() noexcept { sodium_memzero(data,size); }
    ~ErasingThreadStack() {
        erase(); ++wiped_stacks; wiped_bytes+=size;
        munmap(mapping,mapped_size);
    }
};
