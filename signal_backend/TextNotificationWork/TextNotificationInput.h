#pragma once
#include <stdexcept>
#include <utility>
namespace signal_mpc {
// Result of the ACTUAL builder evaluation, moved into normal provider input.
// All field widths are public. No flag is synthesized or opened here.
template<class Bits>struct TextNotificationInput {Bits payload,timestamp,validity;};
template<class Bits>TextNotificationInput<Bits> split_text_notification(Bits result){
 if(result.size()!=720)throw std::runtime_error("text notification result dimensions");
 Bits validity(result.begin(),result.begin()+8);
 Bits payload(result.begin()+8,result.begin()+656);
 Bits timestamp(result.begin()+656,result.end());
 result.clear();
 return{std::move(payload),std::move(timestamp),std::move(validity)};
}
}
