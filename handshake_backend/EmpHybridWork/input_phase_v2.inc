// KRRW18 Fig.3 input steps: reveal non-owner mask share TO OWNER only;
// then the owner broadcasts Gamma=x XOR lambda. Never send raw x.
std::vector<SecureWires> AG2PCProtocol::process_inputs(
    const std::vector<int>& owners,
    const std::vector<std::vector<uint8_t>>& bits_per_owner) {
  AG2PC_PHASE_BEGIN(); ++process_input_calls;
  if(owners.size()!=bits_per_owner.size())error("process_inputs: owner dimensions");
  const int K=(int)owners.size();int n_total=0;std::vector<int> offsets(K);
  for(int k=0;k<K;k++){
    if(owners[k]!=ALICE&&owners[k]!=BOB)error("process_inputs: invalid owner");
    if(bits_per_owner[k].size()>size_t(INT_MAX-n_total))error("process_inputs: width overflow");
    offsets[k]=n_total;n_total+=(int)bits_per_owner[k].size();
    for(auto bit:bits_per_owner[k])if(bit>1)error("process_inputs: noncanonical local input");
  }
  if(!n_total)return std::vector<SecureWires>(K);
  SecureWires sw;sw.Lambda.resize(n_total);sw.wire_bundle.resize(n_total);
  if(party==ALICE)sw.label0.resize(n_total);else sw.eval_label.resize(n_total);
  fpre->draw(n_total,sw.wire_bundle);
  if(party==ALICE)prg.random_block(sw.label0.data(),n_total);
  std::vector<int> mine,theirs;std::vector<uint8_t> own_x(n_total,0);
  for(int k=0;k<K;k++)for(size_t j=0;j<bits_per_owner[k].size();j++){
    int id=offsets[k]+(int)j;
    if(owners[k]==party){mine.push_back(id);own_x[id]=bits_per_owner[k][j];}
    else theirs.push_back(id);
  }
  // Send only mask shares belonging to PEER-owned wires. Never reveal my
  // mask share for a peer's view of a wire that I own.
  std::vector<uint8_t> send_share;BlockVec send_mac;
  for(int id:theirs){send_share.push_back(LSB(sw.wire_bundle[id].mac));send_mac.push_back(sw.wire_bundle[id].mac);}
#ifdef EMP_HYBRID_TEST_ATTACKS
  if(party==BOB&&std::getenv("EMP_TEST_NONCANONICAL_SHARE")&&!send_share.empty())send_share[0]=2;
#endif
  char send_digest[Hash::DIGEST_SIZE],peer_digest[Hash::DIGEST_SIZE];
  if(!theirs.empty())Hash::hash_once(send_digest,send_mac.data(),send_mac.size()*sizeof(block));
  std::vector<uint8_t> peer_share(mine.size());
  std::vector<std::future<void>> jobs;
  jobs.push_back(pool->enqueue([&]{if(!theirs.empty()){send_io->send_data(send_share.data(),send_share.size());send_io->send_data(send_digest,Hash::DIGEST_SIZE);send_io->flush();}}));
  jobs.push_back(pool->enqueue([&]{if(!mine.empty()){recv_io->recv_data(peer_share.data(),peer_share.size());recv_io->recv_data(peer_digest,Hash::DIGEST_SIZE);}}));
  ::joinNclean(jobs);
  for(auto bit:peer_share)if(bit>1)error("process_inputs: noncanonical peer share");
  if(!mine.empty()){
    BlockVec expected(mine.size());for(size_t j=0;j<mine.size();j++)expected[j]=sw.wire_bundle[mine[j]].key^(select_mask[peer_share[j]]&Delta);
    char digest[Hash::DIGEST_SIZE];Hash::hash_once(digest,expected.data(),expected.size()*sizeof(block));
    if(memcmp(digest,peer_digest,Hash::DIGEST_SIZE))error("process_inputs: peer share-MAC hash mismatch");
  }
  std::vector<uint8_t> own_gamma(mine.size()),peer_gamma(theirs.size());
  for(size_t j=0;j<mine.size();j++){
    int id=mine[j];own_gamma[j]=LSB(sw.wire_bundle[id].mac)^peer_share[j]^own_x[id];sw.Lambda[id]=own_gamma[j];
  }
#ifdef EMP_HYBRID_TEST_ATTACKS
  if(party==BOB&&std::getenv("EMP_TEST_NONCANONICAL_INPUT")&&!own_gamma.empty())own_gamma[0]=2;
#endif
  jobs.push_back(pool->enqueue([&]{if(!mine.empty()){send_io->send_data(own_gamma.data(),own_gamma.size());send_io->flush();}}));
  jobs.push_back(pool->enqueue([&]{if(!theirs.empty())recv_io->recv_data(peer_gamma.data(),peer_gamma.size());}));
  ::joinNclean(jobs);
  for(auto bit:peer_gamma)if(bit>1)error("process_inputs: noncanonical peer Gamma");
#ifdef EMP_HYBRID_INPUT_OBSERVER
  if(party==BOB)hybrid_observe_input(peer_gamma);
#endif
  for(size_t j=0;j<theirs.size();j++)sw.Lambda[theirs[j]]=peer_gamma[j];
  if(party==ALICE){BlockVec labels(n_total);for(int i=0;i<n_total;i++)labels[i]=sw.label0[i]^(select_mask[sw.Lambda[i]]&Delta);io->send_data(labels.data(),labels.size()*sizeof(block));io->flush();}
  else io->recv_data(sw.eval_label.data(),sw.eval_label.size()*sizeof(block));
  std::vector<SecureWires>result(K);
  for(int k=0;k<K;k++){
    int off=offsets[k],n=bits_per_owner[k].size();auto&sub=result[k];
    sub.Lambda.assign(sw.Lambda.begin()+off,sw.Lambda.begin()+off+n);sub.wire_bundle.assign(sw.wire_bundle.begin()+off,sw.wire_bundle.begin()+off+n);
    if(party==ALICE)sub.label0.assign(sw.label0.begin()+off,sw.label0.begin()+off+n);else sub.eval_label.assign(sw.eval_label.begin()+off,sw.eval_label.begin()+off+n);
  }
  AG2PC_PHASE("process_inputs");return result;
}
