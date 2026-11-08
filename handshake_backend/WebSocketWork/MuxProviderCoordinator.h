#pragma once
#include "ProviderCoordinator.h"
#include "NativeConversation.h"
#include "PrivateMuxRegistry.h"
namespace tls_mpc_worker {
struct ConversationAdmission {
    std::unique_ptr<NativeConversation> conversation;Bits computed_validity;
    std::vector<std::unique_ptr<PrivateInputBuilder>> inputs;
};
struct MuxProviderAdmission {
    signal_mpc::UpgradeShape upgrade_shape{22};Bits credentials,computed_credential_validity;
    std::vector<ConversationAdmission> conversations;
};
using MuxProviderFactory=std::function<MuxProviderAdmission(Session&,Collective&,unsigned)>;
MuxProviderFactory make_mux_provider_factory();
class MuxProviderCoordinator {
    using Registry=PrivateMuxRegistry<Bits,NativeConversation>;
    Session& session;Collective& collective;MuxProviderFactory factory;
    std::unique_ptr<Registry> registry;signal_mpc::UpgradeShape shape{22};
    Bits credentials,credential_validity;PublicBytes nonce;
    std::vector<std::pair<uint64_t,std::vector<uint64_t>>> catalogue_rows;
    bool initialized=false,upgrading=false,upgraded=false,closed=false;
    static PublicBytes accept(const PublicBytes& nonce){
        public_require(nonce.size()==16,"invalid public WebSocket nonce");
        unsigned char key[25]={},digest[20],encoded[29]={};EVP_EncodeBlock(key,nonce.data(),16);
        std::string material(reinterpret_cast<char*>(key),24);material+="258EAFA5-E914-47DA-95CA-C5AB0DC85B11";
        SHA1(reinterpret_cast<const unsigned char*>(material.data()),material.size(),digest);EVP_EncodeBlock(encoded,digest,20);return PublicBytes(encoded,encoded+28);
    }
public:
    MuxProviderCoordinator(Session& session,Collective& collective,MuxProviderFactory factory,PublicBytes nonce)
      :session(session),collective(collective),factory(std::move(factory)),nonce(std::move(nonce)){}
    void initialize(unsigned party,std::function<void()> terminal){
        public_require(!initialized&&!closed,"mux provider initialization repeated");initialized=true;
        collective.agree_provider_availability(bool(factory));if(!factory)return;
        bool joined=false;
        try{
            auto admission=factory(session,collective,party);factory={};shape=admission.upgrade_shape;
            public_require(admission.credentials.size()==8*(shape.input_bytes()-16)&&admission.computed_credential_validity.size()==8&&
                !admission.conversations.empty()&&admission.conversations.size()<=4,"invalid mux provider admission");
            credentials=std::move(admission.credentials);credential_validity=std::move(admission.computed_credential_validity);
            registry=std::make_unique<Registry>(typename Registry::Hooks{
                [&]{return session.reserve_private_request_id();},
                [&](Bits a,Bits b){return session.combine_private_validity(std::move(a),std::move(b));},
                [&](size_t slot,Bits id,Bits valid){session.expect_websocket_mux_response(slot,std::move(id),std::move(valid));},
                [&](Bits payload,size_t capacity){return session.retain_private_result(std::move(payload),capacity);},
                [&]{session.checkpoint_private_computation();},std::move(terminal)},Bits(credential_validity));
            std::string inventory=shape.descriptor();
            for(auto& conversation:admission.conversations){
                public_require(bool(conversation.conversation),"missing private conversation");
                inventory+="\nconversation:"+conversation.conversation->public_profile();
                auto owner=registry->admit(std::move(conversation.conversation),std::move(conversation.computed_validity));
                catalogue_rows.push_back({owner,{}});
                for(const auto& input:conversation.inputs){public_require(bool(input),"missing mux input builder");input->validate_public_shape();auto profile=input->public_profile();public_require(!profile.empty(),"missing private input profile");inventory+="\ninput:"+profile;}
            }
            joined=true;collective.require_local_success(true);
            PublicBytes public_inventory(inventory.begin(),inventory.end());public_inventory.insert(public_inventory.end(),nonce.begin(),nonce.end());
            PublicBytes inventory_digest(32);SHA256(public_inventory.data(),public_inventory.size(),inventory_digest.data());
            collective.agree_program("mux-provider-inventory-v1",inventory_digest);
            // No private execution until all local factories/fences/shapes are
            // collectively ready. All temporary state is dropped before renewal.
            session.initialize_private_request_ids(nonce);
            for(size_t i=0;i<admission.conversations.size();++i){
                for(auto& builder:admission.conversations[i].inputs){auto input=builder->evaluate(session);
                    catalogue_rows[i].second.push_back(registry->admit_input(catalogue_rows[i].first,
                        std::move(input.payload),std::move(input.timestamp),std::move(input.computed_validity)));}
                admission.conversations[i].inputs.clear();
            }
            admission.conversations.clear();session.checkpoint_private_computation();
        }catch(...){factory={};if(!joined){joined=true;collective.require_local_success(false);}close();throw;}
    }
    PublicBytes catalogue()const{
        public_require(initialized&&!closed,"mux catalogue unavailable");PublicBytes out{1,static_cast<uint8_t>(catalogue_rows.size())};
        for(const auto& row:catalogue_rows){put_number(out,row.first,8);put_number(out,row.second.size(),2);for(auto input:row.second)put_number(out,input,8);}return out;
    }
    ProviderRegistry::Receipt upgrade(){
        public_require(initialized&&!closed&&registry&&!upgrading,"mux upgrade unavailable");upgrading=true;
        session.start_websocket_mux(accept(nonce));auto input=std::move(credentials);auto shared_nonce=session.share_public_constants(nonce);
        input.insert(input.end(),shared_nonce.begin(),shared_nonce.end());
        auto output=session.evaluate_upgrade(shape,std::move(input));
        auto handle=session.retain_validated_upgrade(std::move(output),std::move(credential_validity));session.checkpoint_private_computation();
        return{handle,shape.output_bytes()};
    }
    ProviderRegistry::Receipt produce(uint64_t owner,uint64_t input){
        public_require(initialized&&!closed&&registry&&upgraded,"mux producer unavailable");auto receipt=registry->produce(owner,input);return{receipt.handle,receipt.capacity};
    }
    // Receipt schema is versioned by the dedicated mux opcode, not opcode18.
    // Called in a new erased host call after receive's successful cleanup barrier.
    PublicBytes authenticated_receipt(const PublicBytes& receipt){
        public_require(initialized&&!closed&&registry,"mux receipt unavailable");Cursor in{receipt};auto is_upgraded=in.number(1);auto count=in.number(1);
        public_require(is_upgraded<=1&&count<=4,"invalid mux completion metadata");std::vector<size_t> slots;
        for(size_t i=0;i<count;++i)slots.push_back(in.number(1));auto control_offset=in.offset;auto controls=in.number(1);public_require(controls<=4,"invalid mux control count");bool closing=false;
        for(size_t i=0;i<controls;++i){auto kind=in.number(1);closing=closing||kind==8;in.take(10);}in.done();
        if(closing){close();PublicBytes out{uint8_t(is_upgraded),0};out.insert(out.end(),receipt.begin()+control_offset,receipt.end());return out;}
        if(is_upgraded&&!upgraded){public_require(upgrading,"unsolicited mux upgrade acknowledgement");registry->authenticated_connection_ready();upgraded=true;}
        PublicBytes out{uint8_t(is_upgraded),uint8_t(slots.size())};
        for(auto slot:slots)put_number(out,registry->authenticated_response_complete(slot),8);
        out.insert(out.end(),receipt.begin()+control_offset,receipt.end());return out;
    }
    void close()noexcept{closed=true;factory={};credentials.clear();credential_validity.clear();if(registry){registry->close();registry.reset();}}
};
}
