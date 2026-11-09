#pragma once
#include <cstdint>
#include <stdexcept>
#include <utility>
namespace tls_mpc_worker {
// Same-worker private cursor. Durable mode stages a range; one account Reserve
// certificate must burn its final successor with all frozen intents before eval.
template<class Bits> class PrivateRequestCursor {
    enum class Phase {empty,ready,staging,committing,closed};
    Phase phase=Phase::empty;Bits current,staged;bool durable=false;
    uint64_t lease=0;size_t count=0;
    static void require(bool ok){if(!ok)throw std::runtime_error("private request cursor unavailable");}
public:
    PrivateRequestCursor()=default;
    PrivateRequestCursor(const PrivateRequestCursor&)=delete;
    PrivateRequestCursor& operator=(const PrivateRequestCursor&)=delete;
    ~PrivateRequestCursor(){close();}
    void initialize(Bits next,bool recoverable=false){
        try{require(phase==Phase::empty&&next.size()==64);current=std::move(next);durable=recoverable;phase=Phase::ready;}
        catch(...){close();throw;}
    }
    bool committed()const{return phase==Phase::empty||phase==Phase::ready;}
    template<class Next> Bits reserve(Next&& next){
        try{
            require(phase==Phase::ready||(durable&&phase==Phase::staging&&count<4));
            bool first=phase==Phase::ready;
            if(first){require(lease!=UINT64_MAX);++lease;count=0;staged=Bits(current);}
            phase=Phase::committing;auto selected=Bits(staged);
            auto successor=next(Bits(staged));require(successor.size()==64&&phase==Phase::committing);
            staged=std::move(successor);++count;
            if(durable)phase=Phase::staging;
            else{current=std::move(staged);count=0;phase=Phase::ready;}
            return selected;
        }catch(...){close();throw;}
    }
    // Callback must finish actual whole-account authorization, not enqueue it.
    // Uncertain certificates remain burned in recovery; this object never retries.
    template<class Commit>void commit_pending(Commit&& commit){
        try{
            require(durable&&phase==Phase::staging&&count>0);phase=Phase::committing;
            commit(static_cast<const Bits&>(current),static_cast<const Bits&>(staged),lease,count);
            require(phase==Phase::committing);current=std::move(staged);count=0;phase=Phase::ready;
        }catch(...){close();throw;}
    }
    void close()noexcept{phase=Phase::closed;current.clear();staged.clear();count=0;}
};
}
