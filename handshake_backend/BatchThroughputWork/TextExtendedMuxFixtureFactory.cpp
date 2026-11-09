// Disposable public fixtures only. Never linked into the default worker.
#include "MuxProviderCoordinator.h"
#include "NativeTextInput.h"
#include "../../signal_backend/TextNotificationWork/PublicTextExtendedFixture.h"
namespace tls_mpc_worker {
MuxProviderFactory make_mux_provider_factory(){return [](Session& session,Collective& collective,unsigned party){
    auto share=[&](const PublicBytes& bytes){return session.share_public_constants(bytes);};
    MuxProviderAdmission result;PublicBytes credentials={0,17,34,51,68,85,102,119,136,153,170,187,204,221,238,255};credentials.insert(credentials.end(),22,'x');
    result.credentials=share(credentials);result.computed_credential_validity=share({255});
    for(unsigned slot=0;slot<2;++slot){
        ConversationAdmission entry;entry.computed_validity=share({255});
        entry.conversation=std::make_unique<NativeConversation>(session,collective,signal_mpc::VariableShape(260,80,false,false),
            share(signal_mpc::PublicTextExtendedFixture::initial(slot)),"private-text-throughput-party-"+std::to_string(party)+"-conversation-"+std::to_string(slot));
        for(unsigned round=0;round<4;++round)entry.inputs.push_back(std::make_unique<NativeTextInput>(
            share(signal_mpc::PublicTextExtendedFixture::text_input(slot,round)),share({255})));
        result.conversations.push_back(std::move(entry));
    }
    return result;
};}
}
