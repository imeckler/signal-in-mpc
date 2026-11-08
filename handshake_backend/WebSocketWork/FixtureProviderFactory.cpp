// Disposable public-fixture adapter only. Normalcore/NoProvider do not include it.
#include "ProviderCoordinator.h"
#include "../../signal_backend/VariableServiceWork/PublicFixtureProducer.h"
namespace tls_mpc_worker {
ProviderFactory make_provider_factory(){return [](Session& session,Collective& collective,unsigned party){
    auto share=[&](const PublicBytes& bytes){return session.share_public_constants(bytes);};
    PublicBytes credentials={0,17,34,51,68,85,102,119,136,153,170,187,204,221,238,255};
    credentials.insert(credentials.end(),22,'x');
    ProviderAdmission result;
    result.provider=std::make_unique<NativeProvider>(session,collective,signal_mpc::UpgradeShape(22),share(credentials),
        signal_mpc::VariableShape(260,0,false,false),share(signal_mpc::PublicVariableFixture::initial()),
        "private-provider-fixture-party-"+std::to_string(party));
    result.credential_validity=share({255});result.state_validity=share({255});
    for(unsigned i=0;i<2;++i)result.inputs.push_back({share({0}),share(signal_mpc::PublicVariableFixture::timestamp()),share({255})});
    return result;
};}
}
