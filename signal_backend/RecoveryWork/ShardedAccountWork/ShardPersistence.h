#pragma once
#include "NativeShardCapture.h"
#include "../AccountCheckpointCoordinator.h"
#include <filesystem>
namespace signal_mpc::recovery::sharded {
// Native embedding configuration, never RPC/plaintext account admission.
class Persistence {
public:
 struct Config {
  Epoch epoch;Digest context{},sharing{},signing_seed{};std::array<unsigned char,64> storage_key{};std::string directory;
  Config(){require(tls_mpc_worker::ErasedHostCall::active(),"shard config requires erased host");}
  ~Config(){OPENSSL_cleanse(signing_seed.data(),signing_seed.size());OPENSSL_cleanse(storage_key.data(),storage_key.size());}
  Config(const Config&)=delete;Config&operator=(const Config&)=delete;
 };
private:
 std::unique_ptr<Config> config_;Digest manifest_;Signer signer_;OwnShareBox box_;
 static std::unique_ptr<Config> initialize(std::unique_ptr<Config> config,tls_mpc_worker::Session& session,unsigned party){
  require(tls_mpc_worker::ErasedHostCall::active()&&config&&party<5&&!config->directory.empty(),"shard persistence construction");session.require_application();
  require(session.machine.get_player().num_players()==5&&unsigned(session.machine.get_player().my_num())==party,"shard persistence runtime party");
  for(auto name:{"nodes","shards","certificates"})std::filesystem::create_directories(config->directory+"/"+name);return config;
 }
 static Digest pin(tls_mpc_worker::Session& session){Digest result{};std::copy_n(session.pinned_programs.digest().begin(),32,result.begin());return result;}
 Digest directory_domain(unsigned party)const{auto b=label("SIGNAL-SHARDED-ACCOUNT-DIRECTORY-DOMAIN-V1");append(b,config_->epoch.digest());append(b,config_->context);append(b,manifest_);append(b,config_->sharing);b.push_back(party);return hash(b);}
public:
 CiphertextStore nodes,bodies;PublicCheckpointStore certificates;VoteJournal journal;Directory directory;Checkpoint local;NativeShardCapture capture;AccountCheckpointCoordinator coordinator;
 Persistence(std::unique_ptr<Config> config,tls_mpc_worker::Session& session,tls_mpc_worker::Collective& collective,unsigned party)
 :config_(initialize(std::move(config),session,party)),manifest_(pin(session)),signer_(config_->signing_seed),box_(config_->storage_key),
 nodes(config_->directory+"/nodes"),bodies(config_->directory+"/shards"),certificates(config_->directory+"/certificates"),journal(config_->directory+"/votes.journal",config_->epoch,config_->context,party,signer_),
 directory(nodes,directory_domain(party)),local(directory,bodies,journal,config_->epoch,config_->context,manifest_,party),capture(box_,bodies,config_->epoch,config_->context,manifest_,config_->sharing,party),
 coordinator(config_->epoch,config_->context,manifest_,party,[this](Phase phase,uint64_t slot,const auto& sections){require(sections.empty(),"sharded coordinator requires tokenized local capture");return local.persist(phase,slot);},[this](const Proposal& proposal,const CertifiedPhase* previous){return local.vote(proposal,previous);},journal,certificates,collective,[&session]()->Player&{return session.machine.get_player();}){}
 const Epoch& epoch()const{return config_->epoch;}const Digest& manifest()const{return manifest_;}
};
}
