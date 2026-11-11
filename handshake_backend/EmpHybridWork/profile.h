#pragma once
// Where a worker's time goes: wall time, AND gates, field products and bytes sent, by label,
// each counted once (a nested scope's cost is not also charged to the scope around it).
// Measurement only: nothing here touches a protocol value. The counters are read through
// callbacks the worker installs; without them only time and call counts are kept.
#include <chrono>
#include <cstdint>
#include <functional>
#include <map>
#include <ostream>
#include <string>
#include <vector>
namespace emp_hybrid {
struct Profile {
    struct Counters {double seconds=0;uint64_t gates=0,products=0,boolean_bytes=0,field_bytes=0;
        Counters&operator+=(const Counters&o){seconds+=o.seconds;gates+=o.gates;products+=o.products;boolean_bytes+=o.boolean_bytes;field_bytes+=o.field_bytes;return *this;}
        Counters operator-(const Counters&o)const{return {seconds-o.seconds,gates-o.gates,products-o.products,boolean_bytes-o.boolean_bytes,field_bytes-o.field_bytes};}
    };
    struct Row {Counters total;uint64_t calls=0;};
    std::map<std::string,Row>rows;
    std::function<uint64_t()>gates,products,boolean_bytes,field_bytes;
    struct Frame {Counters start,children;};
    std::vector<Frame>stack;
    static Profile&get(){static Profile p;return p;}
    Counters now()const{
        return {std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count(),gates?gates():0,products?products():0,
            boolean_bytes?boolean_bytes():0,field_bytes?field_bytes():0};
    }
    void enter(){stack.push_back({now(),{}});}
    // The scope's own cost (what happened inside it, less its nested scopes) goes to `label`.
    Counters leave(const std::string&label){
        auto frame=stack.back();stack.pop_back();auto whole=now()-frame.start;auto own=whole-frame.children;
        auto&row=rows[label];row.total+=own;row.calls++;
        if(!stack.empty())stack.back().children+=whole;
        return whole;
    }
    void report(std::ostream&out,const char*prefix)const{
        for(auto&entry:rows)out<<prefix<<" seconds="<<entry.second.total.seconds<<" calls="<<entry.second.calls<<" and_gates="<<entry.second.total.gates
            <<" field_products="<<entry.second.total.products<<" boolean_bytes="<<entry.second.total.boolean_bytes<<" field_bytes="<<entry.second.total.field_bytes
            <<" label="<<entry.first<<"\n";
    }
};
struct ProfileScope {
    std::string label;
    explicit ProfileScope(std::string l):label(std::move(l)){Profile::get().enter();}
    ~ProfileScope(){Profile::get().leave(label);}
    ProfileScope(const ProfileScope&)=delete;ProfileScope&operator=(const ProfileScope&)=delete;
};
}
