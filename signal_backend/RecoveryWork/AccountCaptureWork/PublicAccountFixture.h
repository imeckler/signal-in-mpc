#pragma once
// PUBLIC DISPOSABLE keys/config only. Never linked into default/no-provider worker.
#include "../AccountRecoveryEngineV1.h"
namespace signal_mpc::recovery {
inline std::shared_ptr<AccountRecoveryEngineV1::Config> public_account_fixture(const std::string& root,unsigned party){
 require(party<5,"public account party");auto config=std::make_shared<AccountRecoveryEngineV1::Config>();config->epoch.number=1;config->epoch.genesis=hash(label("PUBLIC-RESTORED-ACCOUNT-V2/904c8dc"));
 for(unsigned p=0;p<5;++p){Digest seed;seed.fill(p+17);Signer signer(seed);config->epoch.members[p]=signer.public_key();}
 config->context.fill(81);config->archive_sharing_domain.fill(82);config->signing_seed.fill(party+17);for(size_t i=0;i<64;++i)config->local_storage_key[i]=i+party*7;config->local_directory=root+"/"+std::to_string(party);return config;
}
}
