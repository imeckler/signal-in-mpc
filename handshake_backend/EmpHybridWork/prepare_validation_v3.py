"""Generate the lambda-leak diagnostic tree and the validated-output v3 tree.

Both start from the hash-pinned private-input-v2 tree. The diagnostic tree
adds ONLY attacker hooks/recording (protocol messages unchanged). The v3 tree
adds the evaluator masked-value label check and directed authenticated
outputs. Neither is a security proof; see VALIDATION_ROUTE.md.
"""
import difflib,hashlib,json,pathlib
ROOT=pathlib.Path(__file__).resolve().parents[2];BASE=ROOT/'.deps/two-party-comparison';HERE=pathlib.Path(__file__).resolve().parent
prior=json.loads((BASE/'input-fix-build-source.json').read_text());v2=prior['variants']['emp-ag2pc-private-input-v2']
src=pathlib.Path(v2['target']);sha=lambda b:hashlib.sha256(b).hexdigest()
def once(data,needle,replacement,what):
    if data.count(needle)!=1:raise ValueError('patch anchor '+what)
    return data.replace(needle,replacement)

RUN_STATE_ANCHOR='''  std::vector<unsigned char> Lambda_AND;
'''
RUN_STATE_ADD=RUN_STATE_ANCHOR+'''  // Per-AND output label. Evaluator: the label it holds, L_{gamma,Lambda}.
  // Garbler: L_{gamma,0} xor Lambda*Delta for the Lambda the evaluator reported.
  BlockVec Lbl_t;
#ifdef EMP_HYBRID_TEST_ATTACKS
  // Evaluator-local values a malicious evaluator already holds (recorded for
  // the lambda-leak probe only): key/public mask/own share of AND operand 1.
  BlockVec atk_in1_key;
  std::vector<unsigned char> atk_in1_pub, atk_in1_share;
#endif
'''
EVAL_ANCHOR='''      s.M1_t[my_ai] = m;
    }
    ++loc;
'''
EVAL_ADD='''      s.M1_t[my_ai] = m;
      s.Lbl_t[my_ai] = t;
#ifdef EMP_HYBRID_TEST_ATTACKS
      s.atk_in1_key[my_ai] = wb_in1.key;
      s.atk_in1_pub[my_ai] = (unsigned char)Lb;
      s.atk_in1_share[my_ai] = (unsigned char)v_in1;
#endif
    }
    ++loc;
'''
GAMMA_ANCHOR='''    s.M1_t[my_ai] = m;
    return id;
'''
GAMMA_ADD='''    s.M1_t[my_ai] = m;
    s.Lbl_t[my_ai] = s.lbl(id) ^ (select_mask[s.Lambda_AND[my_ai] & 1] & s.Delta);
    return id;
'''
BUFFER_ANCHOR='''    st.Lambda_AND.assign(std::max(1, st.num_ands), 0);
'''
BUFFER_ADD=BUFFER_ANCHOR+'''    st.Lbl_t.resize(std::max(1, st.num_ands));
#ifdef EMP_HYBRID_TEST_ATTACKS
    st.atk_in1_key.resize(std::max(1, st.num_ands));
    st.atk_in1_pub.assign(std::max(1, st.num_ands), 0);
    st.atk_in1_share.assign(std::max(1, st.num_ands), 0);
#endif
'''
GARBLER_RECV_ANCHOR='''    if (st.num_ands > 0) {
      mpc->io->recv_bool((bool*)st.Lambda_AND.data(), st.num_ands);
    }
'''
GARBLER_RECV_V3='''    char D_lbl[Hash::DIGEST_SIZE];
    if (st.num_ands > 0) {
      mpc->io->recv_bool((bool*)st.Lambda_AND.data(), st.num_ands);
      mpc->io->recv_data(D_lbl, Hash::DIGEST_SIZE);
      for (int i = 0; i < st.num_ands; ++i)
        if (st.Lambda_AND[i] > 1) error("noncanonical Lambda_AND");
    }
'''
GARBLER_SEND_ANCHOR='''    if (st.num_ands > 0) {
      char D2[Hash::DIGEST_SIZE];
'''
GARBLER_SEND_V3='''    if (st.num_ands > 0) {
      // v3: Open([Lambda]_B) with the garbled label as the MAC tag. The
      // evaluator can hold L_{gamma,Lambda} only for the masked value its
      // evaluation actually produced; it cannot shift by Delta_A. This check
      // MUST pass before the M1_t digest below is released: that digest is a
      // function of the garbler's secret mask shares whenever a reported
      // Lambda is false.
      char D_lbl_exp[Hash::DIGEST_SIZE];
      Hash::hash_once(D_lbl_exp, st.Lbl_t.data(), (size_t)st.num_ands * sizeof(block));
      if (memcmp(D_lbl_exp, D_lbl, Hash::DIGEST_SIZE) != 0)
        error("evaluator masked-value label check failed");
      char D2[Hash::DIGEST_SIZE];
'''
EVAL_SEND_ANCHOR='''      mpc->io->send_bool((const bool*)st.Lambda_AND.data(), st.num_ands);
      mpc->io->flush();
'''
ATTACK_PARSE='''      auto reported = st.Lambda_AND;
#ifdef EMP_HYBRID_TEST_ATTACKS
      int atk_flip = -1, atk_target = -1;
      if (const char* spec = std::getenv("EMP_TEST_LAMBDA_LEAK")) {
        if (std::sscanf(spec, "%d,%d", &atk_flip, &atk_target) != 2 || atk_flip < 0 ||
            atk_target < 0 || atk_flip >= st.num_ands || atk_target >= st.num_ands)
          error("EMP_TEST_LAMBDA_LEAK: bad spec");
        reported[atk_flip] ^= 1;
      }
      if (std::getenv("EMP_TEST_FALSE_GAMMA")) reported[0] ^= 1;
#endif
'''
EVAL_SEND_DIAG=ATTACK_PARSE+'''      mpc->io->send_bool((const bool*)reported.data(), st.num_ands);
      mpc->io->flush();
'''
EVAL_SEND_V3=ATTACK_PARSE+'''      // v3: authenticate the reported masked values with the labels we hold.
      char D_lbl[Hash::DIGEST_SIZE];
      Hash::hash_once(D_lbl, st.Lbl_t.data(), (size_t)st.num_ands * sizeof(block));
      mpc->io->send_bool((const bool*)reported.data(), st.num_ands);
      mpc->io->send_data(D_lbl, Hash::DIGEST_SIZE);
      mpc->io->flush();
'''
EVAL_CHECK_ANCHOR='''      mpc->io->recv_data(D2, Hash::DIGEST_SIZE);
'''
EVAL_CHECK_ADD=EVAL_CHECK_ANCHOR+'''#ifdef EMP_HYBRID_TEST_ATTACKS
      if (atk_target >= 0) {
        // The garbler computed M1_t[target] with operand-0 mask flipped, i.e.
        // shifted by ITS MAC on its share r of operand 1: K_B[r] xor r*Delta_B.
        // We hold K_B[r] and Delta_B, so the digest is a one-bit oracle for r.
        int found = -1;
        for (int g = 0; g < 2; ++g) {
          BlockVec c = st.M1_t;
          c[atk_target] = c[atk_target] ^ st.atk_in1_key[atk_target] ^ (select_mask[g] & st.Delta);
          char Dg[Hash::DIGEST_SIZE];
          Hash::hash_once(Dg, c.data(), (size_t)st.num_ands * sizeof(block));
          if (memcmp(Dg, D2, Hash::DIGEST_SIZE) == 0) found = g;
        }
        if (found < 0) std::cout << "lambda_leak recovered_wire_value=none\\n";
        else std::cout << "lambda_leak recovered_wire_value="
                       << int(found ^ st.atk_in1_pub[atk_target] ^ st.atk_in1_share[atk_target]) << "\\n";
        return;   // the attacker does not run its own abort check
      }
#endif
'''
# --- v3 preprocessing hardening (triple_pool.h). Conservative ordering only:
# each leaky-AND layer is COT-checked before use and F_eq-checked before it is
# combined, and the bucketing coin is a commit/open joint coin fixed after the
# layer is checked. The cyclic-shift family and the in-place mask handling are
# unchanged and remain review items (TRIPLE_POOL_AUDIT.md).
TP_COIN_ANCHOR='''  // Fold B-1 sacrifice layers into acc, one layer at a time and reusing a single
'''
HELPER_ANCHOR='''#endif // __HELPER
'''
HELPER_ADD='''// v3: every check digest is bound to its purpose, its sender and a per-session
// counter that both parties advance in lockstep.
inline void tagged_digest(char *out, const char *tag, int sender, uint64_t ctr,
                          const void *data, size_t len) {
  Hash h;
  h.put(tag, (int64_t)strlen(tag) + 1);
  uint64_t hdr[2] = {(uint64_t)sender, ctr};
  h.put(hdr, sizeof(hdr));
  h.put(data, (int64_t)len);
  h.digest(out);
}

'''+HELPER_ANCHOR
TP_DOPEN_ANCHOR='''    std::vector<future<void>> res;
    res.push_back(pool->enqueue([&, this]() {
      send_io->send_bool((const bool *)d_me.data(), L);
      send_io->flush();
    }));
    res.push_back(pool->enqueue([&, this]() {
      recv_io->recv_bool((bool *)d_peer.data(), L);
    }));
    ::joinNclean(res);
'''
TP_DOPEN_V3='''    // v3: d is an authenticated open (Fig. 5.5 step 6b), not a raw bit exchange.
    {
      BlockVec dm(L), dk(L);
      for (int i = 0; i < L; ++i) {
        int src = (i < cut) ? i + r : i + r - L;
        dm[i] = am[L + i] ^ lm[L + src];
        dk[i] = ak[L + i] ^ lk[L + src];
      }
      auth_open_(dm.data(), dk.data(), L, d_peer);
    }
'''
TP_SEED_ANCHOR='''    const block pair_seed = makeBlock((uint64_t)std::min(party, 3 - party),
                                      (uint64_t)std::max(party, 3 - party));
'''
TP_SEED_V3='''    // v3: a distinct hash-tweak seed per call, so tweaks never repeat under one Delta.
    const block pair_seed = makeBlock(tag_ctr++, 0x4c61414e44ULL);
'''
TP_REPCOPY_ANCHOR='''    for (int i = 0; i < L; ++i) {
      acc_mac[i]     = rep_a[i].mac;  acc_key[i]     = rep_a[i].key;
      acc_mac[L + i] = rep_b[i].mac;  acc_key[L + i] = rep_b[i].key;
    }
'''
TP_REPCOPY_V3='''    // v3: function-independent form. Layer 0 is a FRESH random triple like every
    // other layer; the gate's own masks never enter a leaky AND. They are joined
    // to the finished triple only by the authenticated Beaver openings below.
'''
TP_REPGEN_ANCHOR='''    gen_cot_shares(acc_mac.data() + 2 * L, acc_key.data() + 2 * L, L);   // region r
'''
TP_REPGEN_V3='''    gen_cot_shares(acc_mac.data(), acc_key.data(), 3 * L);   // fresh a, b, r
'''
TP_BEAVER_ANCHOR='''    {
      std::vector<future<void>> res;
      res.push_back(pool->enqueue([&, this]() {
        send_io->send_bool((const bool *)xb_me.data(), L);
        send_io->send_bool((const bool *)yb_me.data(), L);
        send_io->flush();
      }));
      res.push_back(pool->enqueue([&, this]() {
        recv_io->recv_bool((bool *)xb_pe.data(), L);
        recv_io->recv_bool((bool *)yb_pe.data(), L);
      }));
      ::joinNclean(res);
    }
'''
TP_BEAVER_V3='''    {
      // v3: authenticated opens of e = lambda_alpha xor X and f = lambda_beta xor Y.
      // X is the XOR of B independent leaky x-values and Y is never queried, so
      // both differences are masked by the finished triple.
      BlockVec em((size_t)2 * L), ek((size_t)2 * L);
      for (int i = 0; i < L; ++i) {
        em[i]     = rep_a[i].mac ^ acc_mac[i];      ek[i]     = rep_a[i].key ^ acc_key[i];
        em[L + i] = rep_b[i].mac ^ acc_mac[L + i];  ek[L + i] = rep_b[i].key ^ acc_key[L + i];
      }
      std::vector<unsigned char> pe;
      auth_open_(em.data(), ek.data(), 2 * L, pe);
      for (int i = 0; i < L; ++i) { xb_pe[i] = pe[i]; yb_pe[i] = pe[L + i]; }
    }
'''
TP_BUCKET_ANCHOR='''    size = std::max(size, 1024);
    const double log2_L = std::log2((double)size);
'''
TP_BUCKET_V3='''    // v3: size from the ACTUAL layer length (no 1024 floor), clamped so that a
    // tiny layer gets a large bucket instead of a bound it does not meet.
    const double log2_L = std::max(1.0, std::log2((double)std::max(size, 1)));
'''
TP_COIN_ADD='''  // v3: lockstep counter for digest tags and per-call hash seeds.
  uint64_t tag_ctr = 0;

  // v3: authenticated open of L shared bits to both parties at once. Each side
  // sends its share bits and a tagged hash of its MACs; the receiver recomputes
  // the MACs from its keys. A wrong bit needs the peer's Delta.
  void auth_open_(const block *mac, const block *key, int L,
                  std::vector<unsigned char> &peer_bits) {
    const uint64_t ctr = tag_ctr++;
    std::vector<unsigned char> mine(L);
    peer_bits.assign(L, 0);
    for (int i = 0; i < L; ++i) mine[i] = LSB(mac[i]);
#ifdef EMP_HYBRID_TEST_ATTACKS
    if (party == 2 && std::getenv("EMP_TEST_OPEN_LIE") && L) mine[0] ^= 1;
#endif
    char Dme[Hash::DIGEST_SIZE], Dpeer[Hash::DIGEST_SIZE], Dexp[Hash::DIGEST_SIZE];
    tagged_digest(Dme, "AG2PC open", party, ctr, mac, (size_t)L * sizeof(block));
    std::vector<future<void>> res;
    res.push_back(pool->enqueue([&, this]() {
      send_io->send_bool((const bool *)mine.data(), L);
      send_io->send_data(Dme, Hash::DIGEST_SIZE);
      send_io->flush();
    }));
    res.push_back(pool->enqueue([&, this]() {
      recv_io->recv_bool((bool *)peer_bits.data(), L);
      recv_io->recv_data(Dpeer, Hash::DIGEST_SIZE);
    }));
    ::joinNclean(res);
    BlockVec expect(L);
    for (int i = 0; i < L; ++i)
      expect[i] = key[i] ^ (select_mask[peer_bits[i] & 1] & Delta);
    tagged_digest(Dexp, "AG2PC open", 3 - party, ctr, expect.data(), (size_t)L * sizeof(block));
    if (memcmp(Dexp, Dpeer, Hash::DIGEST_SIZE) != 0)
      error("authenticated open: peer MAC digest mismatch");
  }

  // v3: jointly sampled public coin. P1 commits to its seed, P2 replies with its
  // seed, P1 opens. Neither party can choose the result after seeing the other's.
  block joint_coin_() {
    block mine, theirs, nonce;
    prg.random_block(&mine, 1);
    char com[Hash::DIGEST_SIZE], chk[Hash::DIGEST_SIZE];
    if (party == 1) {
      prg.random_block(&nonce, 1);
      { Hash h; h.put(&mine, sizeof(block)); h.put(&nonce, sizeof(block)); h.digest(com); }
      io->send_data(com, Hash::DIGEST_SIZE); io->flush();
      io->recv_data(&theirs, sizeof(block));
      io->send_data(&mine, sizeof(block)); io->send_data(&nonce, sizeof(block)); io->flush();
    } else {
      io->recv_data(com, Hash::DIGEST_SIZE);
      io->send_data(&mine, sizeof(block)); io->flush();
      io->recv_data(&theirs, sizeof(block)); io->recv_data(&nonce, sizeof(block));
      { Hash h; h.put(&theirs, sizeof(block)); h.put(&nonce, sizeof(block)); h.digest(chk); }
      if (memcmp(chk, com, Hash::DIGEST_SIZE) != 0) error("joint coin: commit-open mismatch");
    }
    block pair[2];
    pair[0] = party == 1 ? mine : theirs;
    pair[1] = party == 1 ? theirs : mine;
    char out[Hash::DIGEST_SIZE];
    Hash::hash_once(out, pair, sizeof(pair));
    block coin; memcpy(&coin, out, sizeof(block));
    return coin;
  }
  // v3: check one leaky-AND layer (COTs first, then the layer's own F_eq)
  // before anything derived from it is combined or opened.
  void checked_leaky_layer_(block *mac, block *key, int L,
                            MITCCRH<8> &gmitc, MITCCRH<8> &emitc) {
    flush_cot_check();
    Hash layer;
    leaky_and_halfgate(mac, key, L, gmitc, emitc, layer);
    char D[Hash::DIGEST_SIZE]; layer.digest(D);
    feq_check(io, party, D, "LaAND F_eq: leaky-AND check failed");
  }

'''+TP_COIN_ANCHOR
TP_LAYER_ANCHOR='''      leaky_and_halfgate(sac_mac.data(), sac_key.data(), L, gmitc, emitc, feq);
      // Per-layer public coin: same labeled (io, sib) digests on both ends → same S.
      block S = RO("AG2PC RO", zero_block)
                    .absorb(io->get_digest()).absorb(sib->get_digest()).squeeze_block();
      uint32_t raw;
      { PRG prg2(&S); prg2.random_data_unaligned(&raw, sizeof(uint32_t)); }
      int r_k = (int)(raw % (uint32_t)L);
'''
TP_LAYER_V3='''      checked_leaky_layer_(sac_mac.data(), sac_key.data(), L, gmitc, emitc);
      // v3: the shift is a joint coin drawn only after this layer passed its checks.
      block S = joint_coin_();
      uint64_t raw;
      memcpy(&raw, &S, sizeof(uint64_t));
      int r_k = (int)(raw % (uint64_t)L);
'''
TP_REP_ANCHOR='''    leaky_and_halfgate(acc_mac.data(), acc_key.data(), L, gmitc, emitc, feq);
    AG2PC_TP("in-place layer 0 (rep + r + leaky)");
'''
TP_REP_V3='''    checked_leaky_layer_(acc_mac.data(), acc_key.data(), L, gmitc, emitc);
    AG2PC_TP("in-place layer 0 (rep + r + leaky)");
'''
TP_BATCH_ANCHOR='''      char Dme[Hash::DIGEST_SIZE]; feq.digest(Dme);
      feq_check(io, party, Dme, "LaAND F_eq: leaky-AND check failed");
'''
TP_BATCH_V3='''      // v3: every layer was already F_eq-checked individually before combining.
      (void)feq;
'''
# --- Triples ahead of use (applied to the v3 text). Since v3 the triple generation is
# function-independent: steps 1-2 of TRIPLE_POOL_AUDIT.md produce L finished triples and only
# step 3 (the authenticated Beaver openings) touches a circuit's masks. `mint` is steps 1-2,
# moved out of compute_inplace without change; compute_inplace takes its triples from `stock`
# when one is installed (dyn_session.h: a second pool of the same session, same Delta, on its
# own channels and counters, minting in batches whose own length fixes the bucket size) and
# mints them itself otherwise. No check, opening or parameter changes.
TP_MINT='''  // Steps 1-2 of the construction: L finished triples (a, b, c = a AND b) in region-major
  // layout, stride L. Function-independent. Every COT is checked before its layer is used and
  // every layer is F_eq-checked before it is combined, so nothing unchecked is left behind.
  uint64_t mint_ns = 0, minted = 0;
  void mint(int L, block *acc_mac_p, block *acc_key_p) {
    const auto mint_start = std::chrono::steady_clock::now();
    const int B = get_bucket_size(L);
    // v3: a distinct hash-tweak seed per call, so tweaks never repeat under one Delta.
    const block pair_seed = makeBlock(tag_ctr++, 0x4c61414e44ULL);
    MITCCRH<8> gmitc, emitc;
    gmitc.setS(pair_seed);
    emitc.setS(pair_seed);
#ifdef AG2PC_PROFILE
    g_tp_cot_ns = g_tp_hg_ns = 0;
    g_tp_sopen_ns = g_tp_feq_ns = g_tp_bkt_ns = 0;
#endif
    // v3: function-independent form. Layer 0 is a FRESH random triple like every
    // other layer; the gate's own masks never enter a leaky AND. They are joined
    // to the finished triple only by the authenticated Beaver openings in compute_inplace.
    Hash feq;
    gen_cot_shares(acc_mac_p, acc_key_p, 3 * L);   // fresh a, b, r
    checked_leaky_layer_(acc_mac_p, acc_key_p, L, gmitc, emitc);
    layered_bucket_into_acc(acc_mac_p, acc_key_p, B, L, gmitc, emitc, feq);
    // v3: every layer was already F_eq-checked individually before combining.
    (void)feq;
    mint_ns += (uint64_t)std::chrono::duration_cast<std::chrono::nanoseconds>(
        std::chrono::steady_clock::now() - mint_start).count();
    minted += (uint64_t)L;
  }
  // Optional source of triples minted ahead of use: fills the two 3L-block region-major
  // buffers with L finished triples under THIS pool's Delta and returns true, or returns
  // false (then they are minted here). Both parties must install the same kind of source.
  std::function<bool(int, block *, block *)> stock;

'''
TP_INPLACE_BODY='''    const int B = get_bucket_size(num_ands);
    (void)B;
    const int L = num_ands;
    AG2PC_TP_BEGIN();
    BlockVec acc_mac((size_t)3 * L), acc_key((size_t)3 * L);
    if (!(stock && stock(L, acc_mac.data(), acc_key.data())))
      mint(L, acc_mac.data(), acc_key.data());
    AG2PC_TP("triples (stock or mint)");
'''
TP_FIXED_DELTA='''    tmp[1] = (party == 1);    // garbler pins bit1(Δ) = 1; evaluator pins 0
    if (fixed_delta) {
      // A further pool of the same session (triples minted ahead of use): the same Delta.
      uint64_t words[2];
      memcpy(words, fixed_delta, sizeof(words));
      for (int i = 0; i < 128; ++i) tmp[i] = (words[i / 64] >> (i % 64)) & 1;
      if (!tmp[0] || tmp[1] != (party == 1)) error("fixed Delta: pinned bits");
    }
'''
def stock_patch(data):
    data=once(data,'#include <atomic>\n','#include <atomic>\n#include <chrono>\n#include <functional>\n','stock includes')
    data=once(data,'  TriplePool(NetIO *io, NetIO *sib, ThreadPool *pool, int party, int ssp = 40)\n',
        '  // fixed_delta / first_tag: for a further pool of the same session (see `stock`): the\n  // session\'s Delta, and a counter range of its own for digest tags and hash-tweak seeds.\n'
        '  TriplePool(NetIO *io, NetIO *sib, ThreadPool *pool, int party, int ssp = 40,\n             const block *fixed_delta = nullptr, uint64_t first_tag = 0)\n','stock constructor')
    data=once(data,'    init_abit_();\n  }\n','    tag_ctr = first_tag;\n    init_abit_(fixed_delta);\n  }\n','stock constructor body')
    data=once(data,'  void init_abit_() {\n','  void init_abit_(const block *fixed_delta = nullptr) {\n','fixed delta parameter')
    data=once(data,'    tmp[1] = (party == 1);    // garbler pins bit1(Δ) = 1; evaluator pins 0\n',TP_FIXED_DELTA,'fixed delta bits')
    data=once(data,'    Delta = abit1->Delta;\n','    Delta = abit1->Delta;\n    if (fixed_delta && memcmp(&Delta, fixed_delta, sizeof(block)) != 0) error("fixed Delta: encoding");\n','fixed delta check')
    if data.count('    const int B = get_bucket_size(num_ands);\n')!=1 or data.count('    AG2PC_TP("F_eq (batched)");\n')!=1:raise ValueError('patch anchor stock body')
    start=data.index('    const int B = get_bucket_size(num_ands);\n');end=data.index('    AG2PC_TP("F_eq (batched)");\n')+len('    AG2PC_TP("F_eq (batched)");\n')
    data=data[:start]+TP_INPLACE_BODY+data[end:]
    data=once(data,'  // In-place (function-dependent) AND-share generation (KRRW §5.2 bucket-saving).\n',TP_MINT+'  // In-place (function-dependent) AND-share generation (KRRW §5.2 bucket-saving).\n','mint')
    return data

reports={}
for name,fix in [('emp-ag2pc-lambda-diagnostic-v2',False),('emp-ag2pc-validated-v3',True)]:
    target=BASE/name;files={};diffs=[]
    for rel,expected in v2['files'].items():
        raw=(src/rel).read_bytes()
        if sha(raw)!=expected:raise ValueError('base source drift '+rel)
        data=raw.decode()
        if rel=='emp-ag2pc/backend/run_state.h':data=once(data,RUN_STATE_ANCHOR,RUN_STATE_ADD,'run state')
        if rel=='emp-ag2pc/backend/pass_ctx.h':
            data=once(data,EVAL_ANCHOR,EVAL_ADD,'evaluate pass');data=once(data,GAMMA_ANCHOR,GAMMA_ADD,'gamma pass')
        if rel=='emp-ag2pc/backend/engine.h':
            data=once(data,'#include <cstring>\n','#include <cstdio>\n#include <cstdlib>\n#include <cstring>\n#include <iostream>\n','includes')
            data=once(data,BUFFER_ANCHOR,BUFFER_ADD,'buffers')
            data=once(data,EVAL_SEND_ANCHOR,EVAL_SEND_V3 if fix else EVAL_SEND_DIAG,'evaluator send')
            data=once(data,EVAL_CHECK_ANCHOR,EVAL_CHECK_ADD,'evaluator check')
            if fix:
                data=once(data,GARBLER_RECV_ANCHOR,GARBLER_RECV_V3,'garbler receive')
                data=once(data,GARBLER_SEND_ANCHOR,GARBLER_SEND_V3,'garbler send')
                data=once(data,'    // Half-gate tweak seed from the transcript.\n','''    // v3: validate every COT minted for this chunk before any garbled material,
    // masked value or check digest derived from it is exchanged. The stock
    // call after c_gamma is kept and becomes a no-op.
    mpc->flush_cot_check();

    // Half-gate tweak seed from the transcript.
''','early COT check')
        if rel=='emp-ag2pc/backend/triple_pool.h' and fix:
            data=once(data,'#include <cmath>\n','#include <cmath>\n#include <cstdlib>\n#include <cstring>\n','pool includes')
            # Production statistical parameter: a caller asking for less is raised to the floor.
            data=once(data,'using OTExt = emp::SoftSpoken<4>;\n','using OTExt = emp::SoftSpoken<4>;\n\n#ifndef EMP_HYBRID_MIN_SSP\n#define EMP_HYBRID_MIN_SSP 128\n#endif\n','ssp floor define')
            data=once(data,'party(party), ssp(ssp), io(io)','party(party), ssp(std::max(ssp, EMP_HYBRID_MIN_SSP)), io(io)','ssp floor')
            data=once(data,TP_COIN_ANCHOR,TP_COIN_ADD,'joint coin');data=once(data,TP_LAYER_ANCHOR,TP_LAYER_V3,'layer check')
            data=once(data,TP_REP_ANCHOR,TP_REP_V3,'representative check');data=once(data,TP_BATCH_ANCHOR,TP_BATCH_V3,'batched feq')
            data=once(data,TP_DOPEN_ANCHOR,TP_DOPEN_V3,'authenticated d');data=once(data,TP_SEED_ANCHOR,TP_SEED_V3,'tweak seed')
            data=once(data,TP_REPCOPY_ANCHOR,TP_REPCOPY_V3,'fresh layer 0');data=once(data,TP_REPGEN_ANCHOR,TP_REPGEN_V3,'fresh layer 0 mint')
            data=once(data,TP_BEAVER_ANCHOR,TP_BEAVER_V3,'authenticated Beaver');data=once(data,TP_BUCKET_ANCHOR,TP_BUCKET_V3,'bucket size')
            data=stock_patch(data)
        if rel=='emp-ag2pc/backend/helper.h' and fix:
            data=once(data,'#include <condition_variable>\n','#include <condition_variable>\n#include <cstring>\n','helper includes')
            data=once(data,HELPER_ANCHOR,HELPER_ADD,'tagged digest')
        if rel=='emp-ag2pc/backend/engine.h' and fix:
            blk='(size_t)st.num_ands * sizeof(block));'
            data=once(data,'    { AG2PCGarblePass gp(','    const uint64_t chk_ctr = mpc->fpre->tag_ctr++;\n    { AG2PCGarblePass gp(','garbler counter')
            data=once(data,'    { AG2PCEvaluatePass ep(','    const uint64_t chk_ctr = mpc->fpre->tag_ctr++;\n    { AG2PCEvaluatePass ep(','evaluator counter')
            data=once(data,'Hash::hash_once(D_lbl_exp, st.Lbl_t.data(), '+blk,'tagged_digest(D_lbl_exp, "AG2PC label", BOB, chk_ctr, st.Lbl_t.data(), '+blk,'label tag A')
            data=once(data,'Hash::hash_once(D_lbl, st.Lbl_t.data(), '+blk,'tagged_digest(D_lbl, "AG2PC label", BOB, chk_ctr, st.Lbl_t.data(), '+blk,'label tag B')
            data=once(data,'Hash::hash_once(D2, st.M1_t.data(), '+blk,'tagged_digest(D2, "AG2PC cgamma", ALICE, chk_ctr, st.M1_t.data(), '+blk,'cgamma tag A')
            data=once(data,'Hash::hash_once(D1, st.M1_t.data(), '+blk,'tagged_digest(D1, "AG2PC cgamma", ALICE, chk_ctr, st.M1_t.data(), '+blk,'cgamma tag B')
        if rel=='emp-ag2pc/backend/protocol.h' and fix:
            data=once(data,'if(!theirs.empty())Hash::hash_once(send_digest,send_mac.data(),','if(!theirs.empty())tagged_digest(send_digest,"AG2PC input",party,in_ctr,send_mac.data(),','input tag send')
            data=once(data,'Hash::hash_once(digest,expected.data(),','tagged_digest(digest,"AG2PC input",3-party,in_ctr,expected.data(),','input tag check')
        if rel=='emp-ag2pc/backend/protocol.h' and fix:
            data=once(data,'  fpre->draw(n_total,sw.wire_bundle);\n','''  fpre->draw(n_total,sw.wire_bundle);
  // v3: input mask shares are opened to their owner below; validate the COTs first.
  fpre->maybe_flush_cot_check();
  const uint64_t in_ctr=fpre->tag_ctr++;
''','input COT check')
        if rel=='emp-ag2pc/backend/protocol.h' and fix:
            start=data.index('std::vector<uint8_t> AG2PCProtocol::decode(')
            if data.count('#endif // EMP_AG2PC_PROTOCOL_H__')!=1:raise ValueError('protocol tail')
            data=data[:start]+(HERE/'output_phase_v3.inc').read_text()
        out=data.encode();dest=target/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(out);files[rel]=sha(out)
        if raw!=out:diffs.extend(difflib.unified_diff(raw.decode().splitlines(True),data.splitlines(True),fromfile='a/'+rel,tofile='b/'+rel))
    (HERE/(name+'.patch')).write_text(''.join(diffs))
    reports[name]=dict(target=str(target),validated_output=fix,files=files)
report=dict(base_revision=prior['base_revision'],base_variant=v2,variants=reports,scope='Diagnostic: attacker hooks only over private-input-v2. v3: evaluator masked-value label check before the garbler digest, directed authenticated A/B/PUBLIC openings, COT check before every opening. Unaudited candidate; preprocessing (TriplePool) not reviewed here.')
(BASE/'validation-v3-build-source.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v['target'] for k,v in reports.items()}))
