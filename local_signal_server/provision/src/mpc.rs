//! Export of provisioned LOCAL test state in the layout the MPC client's kernels read, and a
//! conventional reference sender that uses ONLY that export.
//!
//! Layout source (read-only): TlsMpc/HybridKernels.lean
//!   conversationBytes cert size = cert + 182 + size + 57            (cert = 260, size = 80)
//!   record   = certificate[cert] || session[182 + 80] || metadata[57]
//!   session  (SpqrSend.Input, signalSealFixed `staged`):
//!     0 version | 1..5 counter (BE) | 5..9 previous counter | 9..41 ratchet (sender ratchet public, no 0x05)
//!     41..73 chain key | 73..105 SPQR chain key (send direction) | 105..109 SPQR counter
//!     109..117 SPQR epoch (BE, the message epoch E; the key comes from the chain link for E-1)
//!     117 kind (overwritten by the text input) | 118..150 sender identity public | 150..182 receiver
//!     identity public (signalConversationView "recipient") | 182..262 plaintext (overwritten)
//!   metadata (signalRequestSeal / staged57):
//!     0..16 recipient ACI | 16..32 access key | 32..40 timestamp (overwritten) | 40..48 request id
//!     48 device id | 49..53 registration id (BE) | 53..57 mask (overwritten)
//!   initial blob (signal_backend/TextNotificationWork/check_recipient.py): identity secret[32] || record
//! The inverse mapping (block -> libsignal session) is signal_backend/Oracle's
//! signal-text-recipient-oracle.rs; the write-back after a send is Oracle's
//! session_send_projection.rs, included below unchanged.
use crate::*;

#[allow(dead_code, clippy::all)]
#[path = "../../../signal_backend/Oracle/src/session_send_projection.rs"]
mod session_send_projection;

pub const CERT_SLOT: usize = 260; // service_kernels.h: CERT=260
pub const SIZE: usize = 80;
pub const SESSION: usize = 182 + SIZE;
pub const META: usize = 57;
pub const RECORD: usize = CERT_SLOT + SESSION + META;

pub fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}
fn unhex(s: &str) -> R<Vec<u8>> {
    if s.len() % 2 != 0 {
        return Err("odd hex".into());
    }
    Ok((0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16)).collect::<Result<_, _>>()?)
}
fn be32(b: &[u8]) -> u32 {
    u32::from_be_bytes(b.try_into().unwrap())
}
fn uuid_bytes(s: &str) -> R<[u8; 16]> {
    let h: String = s.chars().filter(|c| *c != '-').collect();
    Ok(unhex(&h)?.try_into().map_err(|_| "uuid")?)
}
fn uuid_text(b: &[u8]) -> String {
    let h = hex(b);
    format!("{}-{}-{}-{}-{}", &h[0..8], &h[8..12], &h[12..16], &h[16..20], &h[20..32])
}
pub fn export_path() -> PathBuf {
    state_dir().join("../mpc-export.json")
}

/// Pad a serialized SenderCertificate to `slot` bytes by appending an unknown protobuf field
/// (field 15, length-delimited) to the outer SenderCertificate message. The signature covers only
/// the inner `certificate` bytes, and protobuf parsers skip unknown fields.
pub fn pad_certificate(cert: &[u8], slot: usize) -> R<Vec<u8>> {
    let need = slot.checked_sub(cert.len()).ok_or("certificate longer than slot")?;
    let mut out = cert.to_vec();
    match need {
        0 => {}
        1 => return Err("cannot pad by exactly one byte".into()),
        n if n - 2 < 128 => {
            out.push((15 << 3) | 2);
            out.push((n - 2) as u8);
            out.extend(std::iter::repeat_n(0u8, n - 2));
        }
        n => {
            let l = n - 3; // two-byte length varint
            out.push((15 << 3) | 2);
            out.push((l as u8 & 127) | 128);
            out.push((l >> 7) as u8);
            out.extend(std::iter::repeat_n(0u8, l));
        }
    }
    if out.len() != slot {
        return Err("padding arithmetic".into());
    }
    Ok(out)
}

fn spqr_phase(pq: &pqr::PqRatchetState) -> &'static str {
    use pqr::v1_state::InnerState as S;
    match &pq.inner {
        None => "none (SPQR disabled)",
        Some(pqr::pq_ratchet_state::Inner::V1(v1)) => match &v1.inner_state {
            None => "v1 without state",
            Some(S::KeysUnsampled(_)) => "KeysUnsampled",
            Some(S::KeysSampled(_)) => "KeysSampled",
            Some(S::HeaderSent(_)) => "HeaderSent",
            Some(S::Ct1Received(_)) => "Ct1Received",
            Some(S::EkSentCt1Received(_)) => "EkSentCt1Received",
            Some(S::NoHeaderReceived(_)) => "NoHeaderReceived",
            Some(S::HeaderReceived(_)) => "HeaderReceived",
            Some(S::Ct1Sampled(_)) => "Ct1Sampled",
            Some(S::EkReceivedCt1Sampled(_)) => "EkReceivedCt1Sampled",
            Some(S::Ct1Acknowledged(_)) => "Ct1Acknowledged",
            Some(S::Ct2Sampled(_)) => "Ct2Sampled",
        },
    }
}

fn varint(b: &[u8], at: &mut usize) -> R<u64> {
    let (mut n, mut s) = (0u64, 0);
    loop {
        let x = *b.get(*at).ok_or("varint")?;
        *at += 1;
        n |= ((x & 127) as u64) << s;
        s += 7;
        if x < 128 {
            return Ok(n);
        }
    }
}

/// Forward projection: the sender's libsignal SessionRecord for one contact -> 262-byte session block.
/// Also simulates libsignal's next SPQR send (spqr::send on the stored state) to learn the message
/// epoch, index and payload type the next conventional send would use.
fn project(record: &[u8]) -> R<(Vec<u8>, Value)> {
    let rec = storage::RecordStructure::decode(record)?;
    let s = rec.current_session.ok_or("no current session")?;
    let pending_prekey = s.pending_pre_key.is_some();
    let chain = s.sender_chain.as_ref().ok_or("no sender chain")?;
    let ck = chain.chain_key.as_ref().ok_or("no chain key")?;
    let pq = pqr::PqRatchetState::decode(s.pq_ratchet_state.as_slice())?;
    let phase = spqr_phase(&pq);
    let sim = spqr::send(&s.pq_ratchet_state, &mut rand::rng()).map_err(|e| format!("spqr::send: {e:?}"))?;
    let msg = &sim.msg;
    let mut at = 1;
    let epoch = varint(msg, &mut at)?;
    let sim_epoch = epoch;
    let index = varint(msg, &mut at)? as u32;
    let kind = *msg.get(at).ok_or("spqr msg type")?;
    let pq_chain = pq.chain.as_ref().ok_or("SPQR chain not materialized in the stored state (derived lazily from version negotiation)")?;
    // libsignal's own next send: exact iff it adds no epoch and carries no chunk. Otherwise the MPC
    // kernel (chunk-less SPQR messages only) cannot reproduce it; we then project the newest chain
    // link (message epoch = current_epoch + 1, the convention of the oracle fixtures), which is what
    // a chunk-less sender with this state would use.
    // (spqr::Send.key is the per-message key; a new epoch shows up as a larger current_epoch.)
    let after = pqr::PqRatchetState::decode(sim.state.as_slice())?;
    let adds_epoch = after.chain.as_ref().map(|c| c.current_epoch).unwrap_or(0) > pq_chain.current_epoch;
    let exact = !adds_epoch && (kind == 0 || kind == 4);
    let mpc_epoch = if exact { epoch } else { pq_chain.current_epoch + 1 };
    let back = pq_chain.current_epoch.checked_sub(mpc_epoch - 1).ok_or("SPQR epoch ahead of chain")? as usize;
    let idx = pq_chain.links.len().checked_sub(1 + back).ok_or("SPQR link out of range")?;
    let link = pq_chain.links[idx].send.as_ref().ok_or("no SPQR send link")?;
    if link.next.len() != 32 {
        return Err("SPQR send link has no next key".into());
    }
    if exact && index != link.ctr + 1 {
        return Err(format!("SPQR index {index} != link ctr {} + 1", link.ctr).into());
    }
    if mpc_epoch - 1 < pq_chain.send_epoch {
        return Err("projected epoch below the chain's send epoch".into());
    }
    let epoch = mpc_epoch;
    if s.local_identity_public.len() != 33 || s.remote_identity_public.len() != 33 || chain.sender_ratchet_key.len() != 33 {
        return Err("unexpected key encoding".into());
    }
    let mut b = vec![0u8; SESSION];
    b[0] = s.session_version as u8;
    b[1..5].copy_from_slice(&ck.index.to_be_bytes());
    b[5..9].copy_from_slice(&s.previous_counter.to_be_bytes());
    b[9..41].copy_from_slice(&chain.sender_ratchet_key[1..33]);
    b[41..73].copy_from_slice(&ck.key);
    b[73..105].copy_from_slice(&link.next);
    b[105..109].copy_from_slice(&link.ctr.to_be_bytes());
    b[109..117].copy_from_slice(&epoch.to_be_bytes());
    b[118..150].copy_from_slice(&s.local_identity_public[1..33]);
    b[150..182].copy_from_slice(&s.remote_identity_public[1..33]);
    let kinds = ["None", "Hdr", "Ek", "EkCt1Ack", "Ct1Ack", "Ct1", "Ct2"];
    let info = json!({
        "session_version": s.session_version,
        "pending_prekey_unacknowledged": pending_prekey,
        "signal_counter": ck.index, "previous_counter": s.previous_counter,
        "skipped_sender_message_keys": chain.message_keys.len(),
        "spqr_phase": phase,
        "spqr_chain_current_epoch": pq_chain.current_epoch, "spqr_chain_send_epoch": pq_chain.send_epoch,
        "spqr_chain_links": pq_chain.links.len(), "spqr_link_used": idx,
        "next_conventional_send": {"epoch": sim_epoch, "index": index,
            "payload_type": kinds.get(kind as usize).copied().unwrap_or("?"), "payload_type_byte": kind,
            "adds_epoch": adds_epoch, "message_bytes": msg.len()},
        "projection_exact": exact,
        "projected": {"epoch": epoch, "index": link.ctr + 1, "payload_type": "None"},
    });
    Ok((b, info))
}

/// Kyber-1024 decapsulation with one of the account's Kyber prekeys (keys both MPC parties hold;
/// this step runs outside the engines). Arguments and result in hex, in libsignal's serialization
/// (type byte first) for the key and the ciphertext.
pub fn kem_decapsulate(key: &str, ciphertext: &str) -> R<()> {
    let secret = kem::SecretKey::deserialize(&unhex(key)?)?;
    let shared = secret.decapsulate(&unhex(ciphertext)?.into_boxed_slice())?;
    println!("{}", hex(&shared));
    Ok(())
}

pub async fn export_mpc(sender_name: &str, contact_names: &[&str]) -> R<()> {
    let sender = Account::load(sender_name).await?;
    let cert = sender.sender_certificate.clone().ok_or("sender has no certificate")?;
    // What receiving needs. Our prekey private keys (held in the clear by both parties), and the
    // server certificate that signs sender certificates, validated here against the trust root.
    let mut one_time = vec![];
    for id in sender.store.all_pre_key_ids().cloned().collect::<Vec<_>>() {
        one_time.push(json!({"id": u32::from(id), "key_hex": hex(&sender.store.get_pre_key(id).await?.private_key()?.serialize())}));
    }
    let mut signed = vec![];
    for id in sender.store.all_signed_pre_key_ids().cloned().collect::<Vec<_>>() {
        signed.push(json!({"id": u32::from(id), "key_hex": hex(&sender.store.get_signed_pre_key(id).await?.private_key()?.serialize())}));
    }
    let mut kyber = vec![];
    for id in sender.store.all_kyber_pre_key_ids().cloned().collect::<Vec<_>>() {
        kyber.push(json!({"id": u32::from(id), "key_hex": hex(&sender.store.get_kyber_pre_key(id).await?.secret_key()?.serialize())}));
    }
    let parsed = SenderCertificate::deserialize(&cert)?;
    let trust = PublicKey::deserialize(&unb64(TEST_TRUST_ROOT)?)?;
    let signer = parsed.signer()?.clone();
    if !signer.validate(&trust)? {
        return Err("server certificate does not validate against the trust root".into());
    }
    let slot_cert = pad_certificate(&cert, CERT_SLOT)?;
    let identity = sender.store.get_identity_key_pair().await?;
    let mut contacts = vec![];
    for (slot, name) in contact_names.iter().enumerate() {
        let c = Account::load(name).await?;
        let record = sender.store.load_session(&c.address()).await?.ok_or(format!("no session with {name}; run establish"))?;
        let (block, info) = project(&record.serialize()?)?;
        let request_id: u64 = (1u64 << 63) + slot as u64;
        let mut meta = vec![0u8; META];
        meta[0..16].copy_from_slice(&uuid_bytes(&c.aci)?);
        meta[16..32].copy_from_slice(&c.access_key());
        meta[40..48].copy_from_slice(&request_id.to_be_bytes());
        meta[48] = 1;
        meta[49..53].copy_from_slice(&c.registration_id.to_be_bytes());
        let mut rec = slot_cert.clone();
        rec.extend(&block);
        rec.extend(&meta);
        assert_eq!(rec.len(), RECORD);
        let mut initial = identity.private_key().serialize().to_vec();
        initial.extend(&rec);
        let mut contact_id = [0u8; 16];
        contact_id[15] = slot as u8 + 1; // service_kernels.h fixture_id(slot)
        contacts.push(json!({
            "slot": slot, "name": name, "contact_id_u128_hex": hex(&contact_id),
            "recipient_aci": c.aci, "recipient_aci_hex": hex(&uuid_bytes(&c.aci)?),
            "device_id": 1, "registration_id": c.registration_id, "access_key_hex": hex(&c.access_key()),
            "access_key_base64": b64(&c.access_key()),
            "request_id": request_id.to_string(),
            "session_block_hex": hex(&block), "metadata_hex": hex(&meta),
            "conversation_record_hex": hex(&rec), "conversation_record_bytes": rec.len(),
            "initial_hex": hex(&initial),
            "projection": info,
        }));
    }
    let root = unb64(TEST_TRUST_ROOT)?;
    let password = sender.password.clone();
    let v = json!({
        "format": "lss-mpc-export/1",
        "WARNING": "LOCAL TEST ACCOUNTS on the local Signal-Server only. Contains a private key and a password.",
        "server": {"endpoint": "127.0.0.1", "port": 18443, "hostname": "server.example", "plain_port": 18080,
            "tls_trust_root_pem": state_dir().join("../tls/ca.pem").canonicalize()?.display().to_string()},
        "sealed_sender_trust_root_hex": hex(&root),
        "sealed_sender_server": {"certificate_hex": hex(signer.serialized()?), "key_id": signer.key_id()?,
            "public_key_hex": hex(&signer.public_key()?.serialize()[1..])},
        "layout": {"cert_slot": CERT_SLOT, "session_block": SESSION, "metadata": META, "conversation_record": RECORD,
            "initial": "identity_private[32] || conversation_record"},
        "sender": {
            "name": sender_name, "aci": sender.aci, "aci_hex": hex(&uuid_bytes(&sender.aci)?), "device_id": 1,
            "registration_id": sender.registration_id,
            "password": password, "password_hex": hex(password.as_bytes()), "password_bytes": password.len(),
            "upgrade_credentials_hex": hex(&[uuid_bytes(&sender.aci)?.to_vec(), password.as_bytes().to_vec()].concat()),
            "identity_private_hex": hex(&identity.private_key().serialize()),
            "identity_public_hex": hex(&identity.public_key().serialize()[1..]),
            "certificate_hex": hex(&cert), "certificate_bytes": cert.len(),
            "one_time_prekeys": one_time, "signed_prekeys": signed, "kyber_prekeys": kyber,
            "certificate_slot_hex": hex(&slot_cert),
            "certificate_slot_note": if cert.len() == CERT_SLOT { "exact".to_string() } else {
                format!("{}-byte certificate padded to the {}-byte slot with unknown protobuf field 15", cert.len(), CERT_SLOT) },
        },
        "contacts": contacts,
    });
    let path = export_path();
    std::fs::write(&path, serde_json::to_string_pretty(&v)? + "\n")?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o600))?;
    }
    eprintln!("wrote {}", path.display());
    for c in v["contacts"].as_array().unwrap() {
        println!("{}", json!({"contact": c["name"], "projection": c["projection"]}));
    }
    Ok(())
}

// ---------------------------------------------------------------------------------------------
// Reference sender: only the export file is read.

fn public33(raw: &[u8]) -> Vec<u8> {
    let mut v = vec![5u8];
    v.extend_from_slice(raw);
    v
}

/// Inverse projection (as signal-text-recipient-oracle.rs does for the receiver): a send-only
/// libsignal session from the 262-byte block. Values not in the block (root key, ratchet private
/// key, SPQR authenticator, receive links) are dummies that a send never reads. The SPQR state is
/// `NoHeaderReceived` at the block's epoch, whose send emits a payload-free message exactly like
/// the MPC kernel (SpqrMessage shape without chunk), keyed by the block's chain link.
fn session_from_block(b: &[u8], remote_registration_id: u32) -> R<SessionRecord> {
    let epoch = u64::from_be_bytes(b[109..117].try_into().unwrap());
    if epoch == 0 {
        return Err("SPQR epoch 0".into());
    }
    let link = pqr::chain::epoch::EpochDirection { ctr: be32(&b[105..109]), next: b[73..105].to_vec(), prev: vec![] };
    let dummy = pqr::chain::epoch::EpochDirection { ctr: 0, next: vec![0; 32], prev: vec![] };
    let pq = pqr::PqRatchetState {
        version_negotiation: None,
        chain: Some(pqr::Chain {
            direction: 0, current_epoch: epoch - 1, send_epoch: epoch - 1,
            links: vec![pqr::chain::Epoch { send: Some(link), recv: Some(dummy) }],
            next_root: vec![0x10; 32], params: Some(pqr::ChainParams::default()),
        }),
        inner: Some(pqr::pq_ratchet_state::Inner::V1(pqr::V1State {
            inner_state: Some(pqr::v1_state::InnerState::NoHeaderReceived(pqr::v1_state::chunked::NoHeaderReceived {
                uc: Some(pqr::v1_state::unchunked::NoHeaderReceived {
                    epoch, auth: Some(pqr::Authenticator { root_key: vec![9; 32], mac_key: vec![10; 32] }),
                }),
                receiving_hdr: Some(pqr::PolynomialDecoder { pts_needed: 48, polys: 16, pts: vec![vec![]; 16], is_complete: false }),
            })),
        })),
    };
    let ratchet = KeyPair::generate(&mut rand::rng()); // private half unused by a send
    let session = storage::SessionStructure {
        session_version: b[0] as u32,
        local_identity_public: public33(&b[118..150]),
        remote_identity_public: public33(&b[150..182]),
        root_key: vec![12; 32],
        previous_counter: be32(&b[5..9]),
        sender_chain: Some(storage::session_structure::Chain {
            sender_ratchet_key: public33(&b[9..41]),
            sender_ratchet_key_private: ratchet.private_key.serialize().to_vec(),
            chain_key: Some(storage::session_structure::chain::ChainKey { index: be32(&b[1..5]), key: b[41..73].to_vec() }),
            message_keys: vec![],
        }),
        remote_registration_id,
        pq_ratchet_state: pq.encode_to_vec(),
        ..Default::default()
    };
    let rec = storage::RecordStructure { current_session: Some(session), ..Default::default() };
    Ok(SessionRecord::deserialize(&rec.encode_to_vec())?)
}

/// PublicRequest.build (PublicServiceController.lean) with the slots filled.
pub fn mpc_request_message(uuid: &str, access_key_b64: &str, device: u64, registration: u64, ts: u64, id: u64, envelope: &[u8]) -> Vec<u8> {
    let json = format!(
        "{{\"messages\":[{{\"content\":\"{}\",\"destinationDeviceId\":{},\"destinationRegistrationId\":{},\"type\":6}}],\"online\":false,\"timestamp\":{},\"urgent\":true}}",
        b64(envelope), padded(device, 3), padded(registration, 10), ts);
    let mut request = pb_field(10, b"PUT");
    request.extend(pb_field(18, format!("/v1/messages/{uuid}?story=false").as_bytes()));
    request.extend(pb_field(26, json.as_bytes()));
    request.push(32);
    request.extend(pb_varint(id));
    request.extend(pb_field(42, b"content-type: application/json"));
    request.extend(pb_field(42, format!("unidentified-access-key: {access_key_b64}").as_bytes()));
    let mut message = vec![8u8, 1];
    message.extend(pb_field(18, &request));
    message
}

/// Send `message` (a serialized WebSocketMessage) and wait for the response with `id`.
pub fn exchange(chat: &mut Chat, message: &[u8], id: u64) -> R<(WebSocketResponseMessage, Vec<u8>)> {
    chat.ws.send(tungstenite::Message::Binary(message.to_vec().into()))?;
    let deadline = Instant::now() + Duration::from_secs(30);
    while Instant::now() < deadline {
        if let Some(r) = chat.poll()? {
            if r.id == Some(id) {
                return Ok((r, chat.last_response_raw.clone()));
            }
        }
    }
    Err("no response".into())
}

pub async fn ref_send(text: &str, save_dir: Option<&str>) -> R<()> {
    let path = export_path();
    let mut v: Value = serde_json::from_str(&std::fs::read_to_string(&path)?)?;
    let sender = &v["sender"];
    let identity_private = PrivateKey::deserialize(&unhex(sender["identity_private_hex"].as_str().ok_or("identity")?)?)?;
    let identity = IdentityKeyPair::new(IdentityKey::new(identity_private.public_key()?), identity_private);
    let slot_cert = unhex(sender["certificate_slot_hex"].as_str().ok_or("certificate")?)?;
    let cert = SenderCertificate::deserialize(&slot_cert)?; // padded slot must parse as-is
    let root = PublicKey::deserialize(&unhex(v["sealed_sender_trust_root_hex"].as_str().unwrap())?)?;
    if !cert.validate(&root, Timestamp::from_epoch_millis(now_ms()))? {
        return Err("slot certificate does not validate".into());
    }
    let sender_uuid = uuid_text(&unhex(sender["aci_hex"].as_str().unwrap())?);
    let local = ProtocolAddress::new(sender_uuid, device1());
    let mut results = vec![];
    let n = v["contacts"].as_array().ok_or("contacts")?.len();
    for i in 0..n {
        let c = v["contacts"][i].clone();
        let rec = unhex(c["conversation_record_hex"].as_str().unwrap())?;
        if rec.len() != RECORD || rec[..CERT_SLOT] != slot_cert[..] {
            return Err("record layout".into());
        }
        let block = rec[CERT_SLOT..CERT_SLOT + SESSION].to_vec();
        let meta = rec[CERT_SLOT + SESSION..].to_vec();
        if block[118..150] != identity.public_key().serialize()[1..] {
            return Err("identity secret does not match session sender identity".into());
        }
        let uuid = uuid_text(&meta[0..16]);
        let access = b64(&meta[16..32]);
        let device = meta[48] as u64;
        let registration = be32(&meta[49..53]) as u64;
        let request_id = u64::from_be_bytes(meta[40..48].try_into().unwrap());
        let remote = ProtocolAddress::new(uuid.clone(), DeviceId::new(device as u8)?);

        let mut store = InMemSignalProtocolStore::new(identity.clone(), 1)?;
        store.store_session(&remote, &session_from_block(&block, registration as u32)?).await?;
        store.save_identity(&remote, &IdentityKey::decode(&public33(&block[150..182]))?).await?;
        let ts = now_ms();
        let ct = message_encrypt(&text_content(text, ts), &remote, &local, &mut store.session_store,
            &mut store.identity_store, SystemTime::now(), &mut rand::rng()).await?;
        let CiphertextMessage::SignalMessage(sm) = &ct else { return Err("not a SignalMessage".into()) };
        let pq_msg = sm.pq_ratchet().to_vec();
        let usmc = UnidentifiedSenderMessageContent::new(CiphertextMessageType::Whisper, cert.clone(),
            ct.serialize().to_vec(), ContentHint::Default, None)?;
        let envelope = sealed_sender_encrypt_from_usmc(&remote, &usmc, &store.identity_store, &mut rand::rng()).await?;
        let message = mpc_request_message(&uuid, &access, device, registration, ts, request_id, &envelope);

        // UNAUTHENTICATED socket: the access key is the only authorization.
        let mut chat = Chat::connect(None)?;
        let (r, response_raw) = exchange(&mut chat, &message, request_id)?;
        if let (Some(d), 0) = (save_dir, i) {
            // Server-originated bytes of this unauthenticated connection: 101 head + the 200 response frame.
            std::fs::create_dir_all(d)?;
            std::fs::write(PathBuf::from(d).join("send-unauthenticated-server-stream.bin"), &*chat.server_bytes.borrow())?;
            std::fs::write(PathBuf::from(d).join("send-response-message.bin"), &response_raw)?;
        }
        let pushes: Vec<String> = chat.inbox.iter().map(|p| p.path.clone()).collect();
        let queue_empty = chat.queue_empty;
        chat.close();
        if r.status != Some(200) {
            return Err(format!("send to {uuid}: status {:?} body {:?}", r.status,
                r.body.as_ref().map(|b| String::from_utf8_lossy(b).to_string())).into());
        }

        // Write the advanced state back into the export, as the MPC client's next record would be.
        let after = storage::RecordStructure::decode(store.load_session(&remote).await?.ok_or("session")?.serialize()?.as_slice())?;
        let s = after.current_session.ok_or("session")?;
        let ck = s.sender_chain.as_ref().unwrap().chain_key.as_ref().unwrap();
        let pq = pqr::PqRatchetState::decode(s.pq_ratchet_state.as_slice())?;
        let link = pq.chain.as_ref().unwrap().links[0].send.as_ref().unwrap().clone();
        let mut next = rec.clone();
        let o = CERT_SLOT;
        next[o + 1..o + 5].copy_from_slice(&ck.index.to_be_bytes());
        next[o + 41..o + 73].copy_from_slice(&ck.key);
        next[o + 73..o + 105].copy_from_slice(&link.next);
        next[o + 105..o + 109].copy_from_slice(&link.ctr.to_be_bytes());
        let m = CERT_SLOT + SESSION;
        next[m + 40..m + 48].copy_from_slice(&(request_id + n as u64).to_be_bytes());
        let mut initial = unhex(c["initial_hex"].as_str().unwrap())?[..32].to_vec();
        initial.extend(&next);
        v["contacts"][i]["conversation_record_hex"] = json!(hex(&next));
        v["contacts"][i]["session_block_hex"] = json!(hex(&next[o..o + SESSION]));
        v["contacts"][i]["metadata_hex"] = json!(hex(&next[m..]));
        v["contacts"][i]["initial_hex"] = json!(hex(&initial));
        v["contacts"][i]["sends_from_export"] = json!(c["sends_from_export"].as_u64().unwrap_or(0) + 1);

        // Keep the conventional sender's real SessionRecord in step (Oracle session_send_projection).
        let name = c["name"].as_str().unwrap_or_default().to_string();
        let sender_name = v["sender"]["name"].clone();
        let real_sync = sync_real_record(&sender_name, &remote, ck.key.clone(), ck.index, &link).await;

        results.push(json!({"contact": name, "status": r.status, "body": r.body.map(|b| String::from_utf8_lossy(&b).to_string()),
            "request_id": request_id.to_string(), "timestamp": ts, "socket": "unauthenticated",
            "spqr_message_hex": hex(&pq_msg), "signal_message_bytes": ct.serialize().len(), "envelope_bytes": envelope.len(),
            "request_bytes": message.len(), "server_pushes": pushes, "queue_empty_seen": queue_empty,
            "real_sender_record_updated": real_sync}));
    }
    std::fs::write(&path, serde_json::to_string_pretty(&v)? + "\n")?;
    for r in results {
        println!("{r}");
    }
    Ok(())
}

/// Apply Oracle's session_send_projection::apply to the conventional sender's stored record, so
/// that conventional sends after a reference/MPC send do not reuse a counter.
async fn sync_real_record(sender_name: &Value, remote: &ProtocolAddress, key: Vec<u8>, index: u32,
    link: &pqr::chain::epoch::EpochDirection) -> String {
    let Some(name) = sender_name.as_str() else { return "no sender name".into() };
    let result: R<()> = async {
        let mut acct = Account::load(name).await?;
        let rec = acct.store.load_session(remote).await?.ok_or("no session")?;
        let pb = storage::RecordStructure::decode(rec.serialize()?.as_slice())?;
        let mut out = vec![255u8];
        out.extend(&key);
        out.extend(index.to_be_bytes());
        out.extend(&link.next);
        out.extend(link.ctr.to_be_bytes());
        out.extend([0u8; 8]);
        let updated = session_send_projection::apply(&pb, &out).map_err(|e| e.to_string())?;
        acct.store.store_session(remote, &SessionRecord::deserialize(&updated.encode_to_vec())?).await?;
        acct.save().await
    }
    .await;
    match result {
        Ok(()) => "yes".into(),
        Err(e) => format!("no: {e}"),
    }
}

// ---------------------------------------------------------------------------------------------
// Socket facts (unauthenticated vs authenticated), with byte samples for testdata/.

fn keepalive_message(id: u64) -> Vec<u8> {
    let mut request = pb_field(10, b"GET");
    request.extend(pb_field(18, b"/v1/keepalive"));
    request.push(32);
    request.extend(pb_varint(id));
    let mut m = vec![8u8, 1];
    m.extend(pb_field(18, &request));
    m
}

pub async fn probe_sockets(out_dir: &str, idle_seconds: u64) -> R<()> {
    let dir = PathBuf::from(out_dir);
    std::fs::create_dir_all(&dir)?;
    let me = Account::load("sender").await?;
    let mut report = serde_json::Map::new();
    for (label, auth) in [("unauthenticated", None), ("authenticated", Some((me.aci.clone(), me.password.clone())))] {
        let mut chat = Chat::connect(auth.as_ref().map(|(u, p)| (u.as_str(), p.as_str())))?;
        let t0 = Instant::now();
        while t0.elapsed() < Duration::from_secs(2) {
            chat.poll()?;
        }
        let id = (1u64 << 63) + 7;
        let req = keepalive_message(id);
        let (r, raw) = exchange(&mut chat, &req, id)?;
        std::fs::write(dir.join(format!("keepalive-{label}-request.bin")), &req)?;
        std::fs::write(dir.join(format!("keepalive-{label}-response.bin")), &raw)?;
        // Idle: no frames from us; record when (if) the server closes.
        let t1 = Instant::now();
        let mut closed = None;
        while t1.elapsed() < Duration::from_secs(idle_seconds) {
            match chat.poll() {
                Ok(_) => {}
                Err(e) => {
                    closed = Some(json!({"after_seconds": t1.elapsed().as_secs_f64(), "error": e.to_string()}));
                    break;
                }
            }
        }
        // Server-originated bytes only (101 head + frames); for the unauthenticated socket also the
        // client's upgrade head, which carries no credentials. Never the authenticated upgrade request.
        std::fs::write(dir.join(format!("{label}-server-stream.bin")), &*chat.server_bytes.borrow())?;
        if auth.is_none() {
            let c = chat.client_bytes.borrow();
            let end = c.windows(4).position(|w| w == b"\r\n\r\n").map(|p| p + 4).unwrap_or(c.len());
            std::fs::write(dir.join("unauthenticated-upgrade-request.bin"), &c[..end])?;
        }
        report.insert(label.into(), json!({
            "queue_empty_after_upgrade": chat.queue_empty,
            "other_server_requests": chat.inbox.iter().map(|p| p.path.clone()).collect::<Vec<_>>(),
            "keepalive": {"status": r.status, "message": r.message, "headers": r.headers,
                "body": r.body.map(|b| String::from_utf8_lossy(&b).to_string()),
                "request_bytes": req.len(), "response_bytes": raw.len()},
            "idle_watch_seconds": idle_seconds, "server_closed_while_idle": closed,
        }));
        if closed.is_none() {
            chat.close();
        }
    }
    println!("{}", serde_json::to_string_pretty(&Value::Object(report))?);
    Ok(())
}
