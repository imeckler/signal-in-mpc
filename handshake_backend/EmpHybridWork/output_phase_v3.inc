// v3 output phase (replaces the stock decode). Every opening is an IT-MAC
// Open of the non-recipient's mask share to the recipient, who combines it
// with its OWN masked value Lambda. No plaintext is ever forwarded: PUBLIC is
// two independent directed openings. Soundness for recipient ALICE relies on
// the engine's v3 label check, which authenticates every Lambda the garbler
// holds; without that check ALICE's Lambda would be evaluator-chosen.
std::vector<uint8_t> AG2PCProtocol::decode(const SecureWires &wires,
                                        int recipient) {
  check_secure_wires(wires, party, "decode");   // reject malformed bundles before OOB access
  if (recipient != ALICE && recipient != BOB && recipient != PUBLIC)
    error("decode: invalid recipient");
  const int n = (int)wires.size();
  for (int i = 0; i < n; ++i)
    if (wires.Lambda[i] > 1) error("decode: noncanonical local Lambda");
  AG2PC_PHASE_BEGIN();
  // Every COT minted since the last consistency check (e.g. input masks drawn
  // with no nonlinear chunk in between) is validated before any share opens.
  fpre->maybe_flush_cot_check();

  std::vector<unsigned char> my_share(n);
  BlockVec my_macs(n);
  for (int i = 0; i < n; ++i) {
    my_share[i] = (unsigned char)LSB(wires.wire_bundle[i].mac);
    my_macs[i]  = wires.wire_bundle[i].mac;
  }
  std::vector<uint8_t> result;
  auto open_to = [&](int to) {
    const uint64_t ctr = fpre->tag_ctr++;
    if (party != to) {
      std::vector<unsigned char> sent = my_share;
#ifdef EMP_HYBRID_TEST_ATTACKS
      if (party == BOB && to == ALICE && std::getenv("EMP_TEST_OUTPUT_SHARE_LIE") && n) sent[0] ^= 1;
#endif
      char D[Hash::DIGEST_SIZE];
      tagged_digest(D, "AG2PC decode", party, ctr, my_macs.data(), (size_t)n * sizeof(block));
      io->send_data(sent.data(), n);
      io->send_data(D, Hash::DIGEST_SIZE);
      io->flush();
      return;
    }
    std::vector<unsigned char> peer(n);
    char D_peer[Hash::DIGEST_SIZE];
    io->recv_data(peer.data(), n);
    io->recv_data(D_peer, Hash::DIGEST_SIZE);
    for (int i = 0; i < n; ++i)
      if (peer[i] > 1) error("decode: noncanonical peer share");
    BlockVec exp_macs(n);
    for (int i = 0; i < n; ++i)
      exp_macs[i] = wires.wire_bundle[i].key ^ (select_mask[peer[i]] & Delta);
    char D_exp[Hash::DIGEST_SIZE];
    tagged_digest(D_exp, "AG2PC decode", 3 - party, ctr, exp_macs.data(), (size_t)n * sizeof(block));
    if (memcmp(D_exp, D_peer, Hash::DIGEST_SIZE) != 0)
      error("decode: peer share-MAC hash mismatch");
    result.resize(n);
    for (int i = 0; i < n; ++i)
      result[i] = (uint8_t)((my_share[i] ^ wires.Lambda[i] ^ peer[i]) & 1);
  };
  if (recipient == PUBLIC) { open_to(BOB); open_to(ALICE); }
  else open_to(recipient);
  AG2PC_PHASE("decode[step14]");
  return result;
}

#endif // EMP_AG2PC_PROTOCOL_H__
