#pragma once
#include <cstddef>
#include <stdexcept>
#include <string>
#include <vector>

namespace signal_mpc {
// Public circuit shape, matching the bounded Lean signal-spqr-send export.
// Every identifier, counter value, key and message byte is a shared input.
class SendShape {
    size_t size_, cw_, pw_, ew_, iw_, kw_;
    bool chunk_, addresses_;
    static size_t varint_size(size_t n) {
        size_t result=1;while(n>=128){n>>=7;++result;}return result;
    }
public:
    SendShape(size_t size,size_t cw,size_t pw,size_t ew,size_t iw,size_t kw,
              bool chunk,bool addresses)
        :size_(size),cw_(cw),pw_(pw),ew_(ew),iw_(iw),kw_(kw),chunk_(chunk),addresses_(addresses) {
        if(size>1024 || cw<1 || cw>5 || pw<1 || pw>5 || ew<1 || ew>10 ||
           iw<1 || iw>5 || (chunk?(kw<1 || kw>3):kw!=0))
            throw std::invalid_argument("invalid Signal send shape");
    }
    size_t plaintext_bytes() const {return size_;}
    size_t chunk_bytes() const {return chunk_?34:0;}
    size_t address_bytes() const {return addresses_?36:0;}
    size_t input_bytes() const {return 182+chunk_bytes()+size_+address_bytes();}
    size_t wire_bytes() const {
        size_t ciphertext=16*(size_/16+1);
        size_t pq=2+ew_+iw_+(chunk_?kw_+32:0);
        return 1+35+1+cw_+1+pw_+1+varint_size(ciphertext)+ciphertext+
            1+varint_size(pq)+pq+(addresses_?38:0)+8;
    }
    size_t output_bytes() const {return 73+wire_bytes();}
    std::vector<std::string> arguments() const {
        return {"signal-spqr-send",std::to_string(size_),std::to_string(cw_),
            std::to_string(pw_),std::to_string(ew_),std::to_string(iw_),std::to_string(kw_),
            chunk_?"present":"none",addresses_?"present":"none"};
    }
    std::string stem() const {
        std::string result;for(const auto& s:arguments()){if(!result.empty())result+='-';result+=s;}return result;
    }
    std::string function_name() const {
        auto name=stem();for(auto& c:name)if(c=='-')c='_';return "signal_binary_"+name;
    }
    std::string descriptor() const {
        return "Programs/Functions/"+function_name()+"-sbv:["+std::to_string(input_bytes()*8)+
            "x1]-sbv:["+std::to_string(output_bytes()*8)+"x1]";
    }
};
}
