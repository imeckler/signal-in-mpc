#pragma once
#include "EstablishedSendStore.h"
#include <cerrno>
#include <fcntl.h>
#include <sys/file.h>
#include <unistd.h>

namespace signal_mpc {
// Fail-closed persistence boundary, NOT state recovery. A stable opaque local
// slot is created exclusively and never removed/reopened by this API. Any
// restart must refuse that slot, even if a send was interrupted before commit.
// Slot names must come from the authoritative session binding: a caller may
// not relabel an old state snapshot as a new session to evade its tombstone.
// Only public attempt numbers reach disk; no key, identity or share is opened.
class PersistentSendFence {
    int fd_=-1;
    uint64_t attempt_=0;
    bool closed_=false;
    static void require(bool ok,const char* why){if(!ok)throw std::runtime_error(why);}
    void write_record(const unsigned char* data,size_t count){
        while(count){auto n=::write(fd_,data,count);if(n<0&&errno==EINTR)continue;
            require(n>0,"send fence write failed");data+=n;count-=size_t(n);}
        require(::fsync(fd_)==0,"send fence sync failed");
    }
public:
    explicit PersistentSendFence(const std::string& path){
        auto split=path.find_last_of('/');
        auto directory=split==std::string::npos?".":path.substr(0,split);
        if(directory.empty())directory="/";
        auto name=split==std::string::npos?path:path.substr(split+1);
        require(!name.empty()&&name!="."&&name!="..","invalid send fence slot");
        int parent=::open(directory.c_str(),O_RDONLY|O_DIRECTORY|O_CLOEXEC|O_NOFOLLOW);
        require(parent>=0,"send fence directory unavailable");
        fd_=::openat(parent,name.c_str(),O_WRONLY|O_APPEND|O_CREAT|O_EXCL|O_CLOEXEC|O_NOFOLLOW,0600);
        if(fd_<0){::close(parent);throw std::runtime_error("send slot exists or cannot be created; state recovery forbidden");}
        try{
            require(::flock(fd_,LOCK_EX|LOCK_NB)==0,"send slot lock failed");
            const unsigned char magic[]={'S','I','G','N','A','L','-','B','U','R','N','-','1','\n'};
            write_record(magic,sizeof(magic));
            require(::fsync(parent)==0,"send fence directory sync failed");
            ::close(parent);
        }catch(...){::close(parent);close();throw;}
    }
    PersistentSendFence(const PersistentSendFence&)=delete;
    PersistentSendFence& operator=(const PersistentSendFence&)=delete;
    ~PersistentSendFence(){close();}
    void reserve(){
        try{
            require(!closed_&&attempt_!=UINT64_MAX,"send fence unavailable/exhausted");
            auto value=++attempt_;unsigned char encoded[8];
            for(int i=7;i>=0;--i){encoded[i]=value&255;value>>=8;}
            write_record(encoded,sizeof(encoded));
        }catch(...){close();throw;}
    }
    void close()noexcept{closed_=true;if(fd_>=0){::close(fd_);fd_=-1;}}
};

template<class SharedBits> class FencedSendStore {
    PersistentSendFence fence_;
    EstablishedSendStore<SharedBits> store_;
public:
    FencedSendStore(const std::string& slot,SharedBits state,SharedBits addresses)
      :fence_(slot),store_(std::move(state),std::move(addresses)){}
    template<class Evaluate> auto produce(const SendShape& shape,SharedBits payload,Evaluate&& evaluate){
        try{fence_.reserve();return store_.produce(shape,std::move(payload),std::forward<Evaluate>(evaluate));}
        catch(...){close();throw;}
    }
    void transport_complete(uint64_t ticket){try{store_.transport_complete(ticket);}catch(...){close();throw;}}
    void close()noexcept{store_.close();fence_.close();}
};
}
