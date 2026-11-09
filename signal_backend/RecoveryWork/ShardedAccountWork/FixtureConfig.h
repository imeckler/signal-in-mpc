#pragma once
#include "ShardPersistence.h"
namespace signal_mpc::recovery::sharded {
// Same NEW disposable domain for its fresh process and authorized restart.
inline std::unique_ptr<Persistence::Config> fixture_config(const std::string& root,unsigned party){
 require(party<5&&!root.empty(),"fresh sharded fixture configuration");auto c=std::make_unique<Persistence::Config>();c->epoch.number=1;c->epoch.genesis=hash(label("NEW-SHARDED-ACCOUNT-FIXTURE-GENESIS-SEEDS91-97"));
 for(unsigned p=0;p<5;++p){Digest seed{};seed.fill(p+191);Signer signer(seed);c->epoch.members[p]=signer.public_key();}c->signing_seed.fill(party+191);c->context=hash(label("NEW-SHARDED-ACCOUNT-FIXTURE-CONTEXT-SEEDS91-97"));c->sharing=hash(label("NEW-SHARDED-ACCOUNT-FIXTURE-SHARING-SEEDS91-97"));for(size_t i=0;i<64;++i)c->storage_key[i]=i+party*11+91;c->directory=root+"/"+std::to_string(party);return c;
}
}
