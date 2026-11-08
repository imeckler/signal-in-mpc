#pragma once
#include "PublicProtocol.h"
#include "Networking/Player.h"
#include "Tools/octetStream.h"
#include <sodium.h>
#include <array>
#include <string>
#include <functional>

namespace tls_mpc_worker {
class Collective {
    std::function<Player&()> current_player;
    PublicBytes context;
    RequestSequence requests;
    static PublicBytes digest(const PublicBytes& input) {
        PublicBytes output(crypto_hash_sha256_BYTES);
        crypto_hash_sha256(output.data(),input.data(),input.size()); return output;
    }
    static octetStream stream(const PublicBytes& value) {
        return octetStream(std::string(value.begin(),value.end()));
    }
    std::vector<octetStream> broadcast(const PublicBytes& value) {
        auto& player=current_player();
        std::vector<octetStream> all(player.num_players());
        all.at(player.my_num())=stream(value);
        player.Broadcast_Receive(all); player.Check_Broadcast(); return all;
    }
    void identical(const PublicBytes& value) {
        auto expected=stream(value); auto all=broadcast(value);
        for(const auto& item:all) public_require(item.equals(expected),"collective public request mismatch");
    }
public:
    // Context must bind pinned program/config/trust manifest and fresh session ID.
    Collective(Player& player, const PublicBytes& manifest, const PublicBytes& session_id)
        : Collective([&player]() -> Player& {return player;},manifest,session_id) {}
    // Reacquire the host player on every operation across secure epoch renewal.
    Collective(std::function<Player&()> player, const PublicBytes& manifest, const PublicBytes& session_id)
        : current_player(std::move(player)) {
        auto& current=current_player();
        public_require(current.num_players()==5,"TLS worker requires five parties");
        public_require(manifest.size()==32&&session_id.size()==32,"invalid worker context");
        public_require(sodium_init()>=0,"random initialization failed");
        const std::string label="tls-mpc-worker-public-v4;shamir5t2;fp25519;ccd128;security128;dabit;typed-shape-extensions";
        context.assign(label.begin(),label.end());
        context.insert(context.end(),manifest.begin(),manifest.end());
        context.insert(context.end(),session_id.begin(),session_id.end());
        identical(digest(context));
    }
    void agree(const Request& request) {
        requests.reserve(request.sequence);
        auto frame=encode_request(request); auto bound=context;
        bound.insert(bound.end(),frame.begin(),frame.end()); identical(digest(bound));
    }
    void agree_program(const std::string& shape,const PublicBytes& manifest) {
        public_require(!shape.empty()&&shape.size()<=128&&manifest.size()==32,"invalid program extension context");
        auto bound=context;bound.push_back(0x50);put_number(bound,shape.size(),4);
        bound.insert(bound.end(),shape.begin(),shape.end());
        bound.insert(bound.end(),manifest.begin(),manifest.end());identical(digest(bound));
    }
    // Public local readiness (for example durable reservation), before entering
    // a private producer. Every party must join even after a local failure.
    void require_local_success(bool ready) {
        auto all=broadcast(PublicBytes{0x53,uint8_t(ready?255:0)});
        for(const auto& item:all)public_require(item.get_length()==2&&
            item.get_data()[0]==0x53&&item.get_data()[1]==255,"collective producer preparation failed");
    }
    template<class Action> PublicBytes leader(Action&& action) {
        auto& player=current_player();
        PublicBytes packet;
        if(player.my_num()==0) {
            try {packet=action();public_require(packet.size()<=16645,"leader response too large");packet.insert(packet.begin(),0);}
            catch(...) {packet={1};}
        }
        auto all=broadcast(packet);
        for(size_t i=1;i<all.size();++i)public_require(all[i].get_length()==0,"nonleader sent a transport response");
        auto& result=all[0];public_require(result.get_length()>=1&&result.get_length()<=16646,"invalid leader response");
        public_require(result.get_data()[0]==0,"leader transport failed");
        return PublicBytes(result.get_data()+1,result.get_data()+result.get_length());
    }
    PublicBytes public_random() {
        auto& player=current_player();
        PublicBytes random(32); randombytes_buf(random.data(),random.size());
        auto bound=context; bound.push_back(0x52); put_number(bound,player.my_num(),4); bound.insert(bound.end(),random.begin(),random.end());
        auto commits=broadcast(digest(bound)); auto openings=broadcast(random);
        PublicBytes result(32,0);
        for(size_t i=0;i<openings.size();++i) {
            auto& opening=openings[i]; public_require(opening.get_length()==32,"invalid random opening");
            PublicBytes value(opening.get_data(),opening.get_data()+32);
            auto candidate=context; candidate.push_back(0x52); put_number(candidate,i,4); candidate.insert(candidate.end(),value.begin(),value.end());
            public_require(commits[i].equals(stream(digest(candidate))),"random commitment mismatch");
            for(size_t j=0;j<32;++j) result[j]^=value[j];
        }
        sodium_memzero(random.data(),random.size()); return result;
    }
};
}
