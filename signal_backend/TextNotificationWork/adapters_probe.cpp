// Compile/link only; no native evaluation or secret inputs.
#include "NativeTextNotification.h"
#include "PublicTextFixture.h"
#include <cassert>
#include "TextNotificationInput.h"
auto text_method=&signal_mpc::NativeTextNotification::evaluate;
int main(){
 assert(signal_mpc::PublicTextFixture::initial(0).size()==611);
 assert(signal_mpc::PublicTextFixture::initial(1).size()==611);
 for(size_t slot=0;slot<2;++slot)for(size_t round=0;round<2;++round)
  assert(signal_mpc::PublicTextFixture::text_input(slot,round).size()==59);
 std::vector<unsigned char> out(720);for(size_t i=0;i<out.size();++i)out[i]=i%251;
 auto parts=signal_mpc::split_text_notification(out);
 assert(parts.validity==std::vector<unsigned char>(out.begin(),out.begin()+8));
 assert(parts.payload==std::vector<unsigned char>(out.begin()+8,out.begin()+656));
 assert(parts.timestamp==std::vector<unsigned char>(out.begin()+656,out.end()));
 bool wrong=false;try{signal_mpc::split_text_notification(std::vector<unsigned char>(719));}catch(...){wrong=true;}assert(wrong);
 bool rejected=false;try{signal_mpc::PublicTextFixture::text_input(0,2);}catch(...){rejected=true;}
 assert(rejected);return 0;
}
