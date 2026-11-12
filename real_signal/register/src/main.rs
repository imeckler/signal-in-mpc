//! Registers a phone number with the REAL Signal service and saves everything the two-party
//! client will need. A conventional client: it follows secret-shared-db's relay-node
//! (`server/relay-node/src/registration.rs`) and uses the same libsignal connection code.
//!
//! Usage: real-signal-register register PHONE_NUMBER STATE_DIR
//!
//! It asks on the terminal for the captcha token and the verification code. Nothing is sent
//! before the keys and password have been written to STATE_DIR/pending-registration.json, so a
//! crash never loses what the server may already have accepted.
//!
//! Everything is recorded:
//!   STATE_DIR/registration-log.jsonl  one JSON line per step: what was asked, what was sent,
//!                                     what came back, with times (includes secrets; local only)
//!   STATE_DIR/libsignal-trace.log     libsignal's own log at trace level
//! libsignal makes the TLS connection itself, so the record is at the level of its API calls and
//! of the requests this program builds, not of raw bytes on the wire.
use anyhow::{anyhow, Context, Result};
use base64::engine::general_purpose::{STANDARD, URL_SAFE_NO_PAD};
use base64::engine::Engine;
use futures_util::future::BoxFuture;
use futures_util::FutureExt;
use http::{header, HeaderMap, HeaderValue};
use libsignal_core::curve::PublicKey;
use libsignal_net::auth::Auth;
use libsignal_net::chat::ws::{self, ListenerEvent};
use libsignal_net::chat::{
    AuthenticatedChatHeaders, ChatConnection, ChatHeaders, ConnectError, LanguageList, Request,
};
use libsignal_net::connect_state::{
    ConnectState, ConnectionResources, DefaultConnectorFactory, SUGGESTED_CONNECT_CONFIG,
    SUGGESTED_TLS_PRECONNECT_LIFETIME,
};
use libsignal_net::env::constants::CHAT_WEBSOCKET_PATH;
use libsignal_net::env::{UserAgent, PROD};
use libsignal_net::infra::dns::DnsResolver;
use libsignal_net::infra::route::{
    ConnectionProxyRoute, DirectOrProxyProvider, DirectOrProxyRoute, PreconnectingFactory,
    SimpleRoute, TcpRoute, TlsRouteFragment,
};
use libsignal_net::infra::{EnableDomainFronting, EnforceMinimumTls, OverrideNagleAlgorithm};
use libsignal_net_chat::api::registration::*;
use libsignal_net_chat::api::{ChallengeOption, Unauth};
use libsignal_net_chat::registration::{ConnectUnauthChat, RegistrationService};
use libsignal_protocol::{GenericSignedPreKey, IdentityKeyPair, KyberPreKeyRecord, SignedPreKeyRecord};
use rand::{Rng, TryRngCore};
use serde_json::{json, Value};
use std::collections::HashSet;
use std::convert::Infallible;
use std::io::Write;
use std::net::IpAddr;
use std::os::unix::fs::{OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::sync::{LazyLock, Mutex};
use std::time::{Duration, SystemTime, UNIX_EPOCH};
use tokio::sync::oneshot;
use usernames::{create_for_username, NicknameLimits, Username};
use zkgroup::profiles::ProfileKey;

/// The two-party client's password slot is exactly 22 bytes.
const PASSWORD_LEN: usize = 22;
const CLIENT_NAME: &str = "relay-node";

fn now_ms() -> u128 {
    SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_millis()
}

fn private_file(path: &Path, append: bool) -> Result<std::fs::File> {
    let mut options = std::fs::OpenOptions::new();
    options.create(true).mode(0o600);
    if append {
        options.append(true);
    } else {
        options.write(true).truncate(true);
    }
    let file = options.open(path).with_context(|| format!("open {}", path.display()))?;
    file.set_permissions(std::fs::Permissions::from_mode(0o600))?;
    Ok(file)
}

fn write_private(path: &Path, value: &Value) -> Result<()> {
    let mut file = private_file(path, false)?;
    file.write_all(serde_json::to_string_pretty(value)?.as_bytes())?;
    file.write_all(b"\n")?;
    Ok(())
}

/// The step-by-step record.
static RECORD: Mutex<Option<std::fs::File>> = Mutex::new(None);
fn record(step: &str, detail: Value) {
    let line = json!({"time_ms": now_ms().to_string(), "step": step, "detail": detail});
    if let Some(file) = RECORD.lock().unwrap().as_mut() {
        let _ = writeln!(file, "{line}");
        let _ = file.flush();
    }
}

/// libsignal's log, all of it to a file; warnings and errors also to the terminal.
struct TraceLog(Mutex<std::fs::File>);
impl log::Log for TraceLog {
    fn enabled(&self, _: &log::Metadata) -> bool {
        true
    }
    fn log(&self, r: &log::Record) {
        let _ = writeln!(self.0.lock().unwrap(), "{} {:5} {} {}", now_ms(), r.level(), r.target(), r.args());
        if r.level() <= log::Level::Warn {
            eprintln!("[{}] {}", r.level(), r.args());
        }
    }
    fn flush(&self) {
        let _ = self.0.lock().unwrap().flush();
    }
}

fn ask(prompt: &str) -> Result<String> {
    print!("{prompt}");
    std::io::stdout().flush()?;
    let mut input = String::new();
    std::io::stdin().read_line(&mut input)?;
    Ok(input.trim().to_string())
}

// ---- Connections: as in relay-node's chat.rs -------------------------------------------------

static SENDER_THAT_NEVER_SENDS: LazyLock<tokio::sync::watch::Sender<()>> = LazyLock::new(Default::default);
type Routes = PreconnectingFactory<
    SimpleRoute<TlsRouteFragment, DirectOrProxyRoute<TcpRoute<IpAddr>, ConnectionProxyRoute<IpAddr>>>,
    DefaultConnectorFactory,
>;

struct Connector {
    user_agent: UserAgent,
    network_change_event: tokio::sync::watch::Receiver<()>,
    dns_resolver: DnsResolver,
    connect_state: std::sync::Mutex<ConnectState<Routes>>,
}

impl Connector {
    fn new() -> Self {
        let network_change_event = SENDER_THAT_NEVER_SENDS.subscribe();
        Connector {
            user_agent: UserAgent::with_libsignal_version(CLIENT_NAME),
            dns_resolver: DnsResolver::new(&network_change_event),
            network_change_event,
            connect_state: ConnectState::new_with_transport_connector(
                SUGGESTED_CONNECT_CONFIG,
                PreconnectingFactory::new(DefaultConnectorFactory, SUGGESTED_TLS_PRECONNECT_LIFETIME),
            ),
        }
    }

    fn config() -> ws::Config {
        ws::Config {
            local_idle_timeout: Duration::from_secs(60),
            remote_idle_timeout: Duration::from_secs(60),
            initial_request_id: 0,
            post_request_interface_check_timeout: Duration::from_secs(60),
        }
    }

    async fn pending(&self, headers: Option<ChatHeaders>, label: &'static str) -> Result<libsignal_net::chat::PendingChatConnection, ConnectError> {
        let route_provider = DirectOrProxyProvider::direct(PROD.chat_domain_config.connect.route_provider_with_options(
            EnableDomainFronting::No,
            EnforceMinimumTls::No,
            OverrideNagleAlgorithm::UseSystemDefault,
        ));
        let resources = ConnectionResources {
            connect_state: &self.connect_state,
            dns_resolver: &self.dns_resolver,
            network_change_event: &self.network_change_event,
            confirmation_header_name: None,
        };
        ChatConnection::start_connect_with(resources, route_provider, CHAT_WEBSOCKET_PATH, &self.user_agent, Self::config(), headers, label).await
    }

    /// The authenticated connection, for the requests after registration.
    async fn authenticated(&self, username: &str, password: &str) -> Result<ChatConnection> {
        let headers = Some(ChatHeaders::Auth(AuthenticatedChatHeaders {
            auth: Auth { username: username.to_string(), password: password.to_string() },
            receive_stories: false.into(),
            languages: LanguageList::parse(&["en"]).unwrap(),
        }));
        let pending = self.pending(headers, "real-signal-register").await.map_err(|e| anyhow!("authenticated connect failed: {e:?}"))?;
        let listener = move |event: ListenerEvent| match event {
            ListenerEvent::ReceivedMessage(request, responder) => {
                // Nothing is expected for a brand-new account. Record it and do NOT acknowledge,
                // so the server keeps it for the real client.
                record("server-request-on-authenticated-socket", json!({
                    "verb": request.verb, "path": request.path, "headers": request.headers,
                    "body_bytes": request.body.as_ref().map(|b| b.len()), "acknowledged": false}));
                drop(responder);
            }
            ListenerEvent::ReceivedAlerts(alerts) => record("server-alerts", json!({"alerts": alerts})),
            ListenerEvent::Finished(result) => record("authenticated-socket-finished", json!({"result": format!("{result:?}")})),
        };
        let runtime = tokio::runtime::Handle::try_current().expect("tokio runtime");
        Ok(ChatConnection::finish_connect(runtime, pending, Box::new(listener)))
    }
}

impl ConnectUnauthChat for Connector {
    fn connect_chat(&self, on_disconnect: oneshot::Sender<Infallible>) -> BoxFuture<'_, Result<Unauth<ChatConnection>, ConnectError>> {
        record("connect-unauthenticated", json!({}));
        self.pending(None, "registration")
            .map(|pending| {
                pending.map(|pending| {
                    let mut on_disconnect = Some(on_disconnect);
                    let listener = move |event| match event {
                        ListenerEvent::Finished(result) => {
                            record("unauthenticated-socket-finished", json!({"result": format!("{result:?}")}));
                            drop(on_disconnect.take())
                        }
                        ListenerEvent::ReceivedAlerts(_) | ListenerEvent::ReceivedMessage(_, _) => {}
                    };
                    let runtime = tokio::runtime::Handle::try_current().expect("tokio runtime");
                    Unauth(ChatConnection::finish_connect(runtime, pending, Box::new(listener)))
                })
            })
            .boxed()
    }
}
impl std::panic::UnwindSafe for Connector {}

/// One request on the authenticated socket, recorded in full with its response.
async fn send_recorded(chat: &ChatConnection, name: &str, method: http::Method, path: &str, headers: HeaderMap, body: Option<Vec<u8>>) -> Result<(u16, Vec<u8>)> {
    record(&format!("{name}-request"), json!({
        "method": method.as_str(), "path": path,
        "headers": headers.iter().map(|(k, v)| format!("{}: {}", k, v.to_str().unwrap_or("?"))).collect::<Vec<_>>(),
        "body_base64": body.as_ref().map(|b| STANDARD.encode(b))}));
    let response = chat
        .send(Request { method, path: path.parse()?, headers, body: body.map(Into::into) }, Duration::from_secs(20))
        .await;
    match response {
        Ok(response) => {
            let body = response.body.as_ref().map(|b| b.to_vec()).unwrap_or_default();
            record(&format!("{name}-response"), json!({
                "status": response.status.as_u16(), "message": response.message,
                "headers": response.headers.iter().map(|(k, v)| format!("{}: {}", k, v.to_str().unwrap_or("?"))).collect::<Vec<_>>(),
                "body_base64": STANDARD.encode(&body), "body_text": String::from_utf8_lossy(&body)}));
            Ok((response.status.as_u16(), body))
        }
        Err(e) => {
            record(&format!("{name}-error"), json!({"error": format!("{e:?}")}));
            Err(anyhow!("{name}: {e:?}"))
        }
    }
}

// ---- Keys: as in relay-node's registration.rs ------------------------------------------------

struct OwnedAccountKeys {
    identity_key: PublicKey,
    signed_pre_key: SignedPreKeyBody<Box<[u8]>>,
    pq_last_resort_pre_key: SignedPreKeyBody<Box<[u8]>>,
}
impl OwnedAccountKeys {
    fn as_borrowed(&self) -> AccountKeys<'_> {
        AccountKeys {
            identity_key: &self.identity_key,
            signed_pre_key: self.signed_pre_key.as_deref(),
            pq_last_resort_pre_key: self.pq_last_resort_pre_key.as_deref(),
        }
    }
}

struct Generated {
    identity: ForServiceIds<IdentityKeyPair>,
    signed: ForServiceIds<SignedPreKeyRecord>,
    kyber: ForServiceIds<KyberPreKeyRecord>,
    account: ForServiceIds<OwnedAccountKeys>,
}

fn generate_keys<R: rand_core::CryptoRng + rand_core::RngCore>(csprng: &mut R) -> Generated {
    use libsignal_protocol::{KeyPair, Timestamp};
    let stamp = || Timestamp::from_epoch_millis(now_ms() as u64);
    let identity = ForServiceIds::generate(|_| IdentityKeyPair::generate(csprng));
    let signed = ForServiceIds::generate(|kind| {
        let id: u32 = csprng.next_u32() & 0x00FF_FFFF;
        let pair = KeyPair::generate(csprng);
        let signature = identity.get(kind).private_key().calculate_signature(&pair.public_key.serialize(), csprng).unwrap();
        SignedPreKeyRecord::new(id.into(), stamp(), &pair, &signature)
    });
    let kyber = ForServiceIds::generate(|kind| {
        let id: u32 = csprng.next_u32() & 0x00FF_FFFF;
        let pair = libsignal_protocol::kem::KeyPair::generate(libsignal_protocol::kem::KeyType::Kyber1024, csprng);
        let signature = identity.get(kind).private_key().calculate_signature(&pair.public_key.serialize(), csprng).unwrap();
        KyberPreKeyRecord::new(id.into(), stamp(), &pair, &signature)
    });
    let account = ForServiceIds::generate(|kind| {
        let (s, k) = (signed.get(kind), kyber.get(kind));
        OwnedAccountKeys {
            identity_key: identity.get(kind).public_key().clone(),
            signed_pre_key: SignedPreKeyBody {
                key_id: s.id().unwrap().into(),
                public_key: s.public_key().unwrap().serialize().into(),
                signature: s.signature().unwrap().to_vec().into_boxed_slice(),
            },
            pq_last_resort_pre_key: SignedPreKeyBody {
                key_id: k.id().unwrap().into(),
                public_key: k.public_key().unwrap().serialize().into(),
                signature: k.signature().unwrap().to_vec().into_boxed_slice(),
            },
        }
    });
    Generated { identity, signed, kyber, account }
}

fn sample_password<R: rand_core::RngCore>(rng: &mut R, len: usize) -> String {
    const ALPHABET: &[u8] = b"0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz-_";
    let mut buf = vec![0u8; len];
    rng.fill_bytes(&mut buf);
    buf.iter().map(|b| ALPHABET[(*b & 63) as usize] as char).collect()
}

fn session_json(service: &RegistrationService) -> Value {
    let state = service.session_state();
    json!({
        "allowed_to_request_code": state.allowed_to_request_code,
        "verified": state.verified,
        "requested_information": format!("{:?}", state.requested_information),
        "next_sms": format!("{:?}", state.next_sms),
        "next_call": format!("{:?}", state.next_call),
        "next_verification_attempt": format!("{:?}", state.next_verification_attempt),
    })
}

/// Everything about the account, in one JSON value (the layout of lss-provision's account files
/// where the fields coincide, so the same tooling can read it).
#[allow(clippy::too_many_arguments)]
fn account_json(number: &str, aci: &str, pni: &str, password: &str, recovery_password: &[u8; 32], registration_id: u16, pni_registration_id: u16,
    profile_key: &ProfileKey, keys: &Generated, sender_certificate: Option<&[u8]>, username: Option<&str>) -> Result<Value> {
    use libsignal_core::ServiceIdKind::{Aci, Pni};
    let record_of = |r: &SignedPreKeyRecord| -> Result<Value> { Ok(json!({u32::from(r.id()?).to_string(): STANDARD.encode(r.serialize()?)})) };
    let kyber_of = |r: &KyberPreKeyRecord| -> Result<Value> { Ok(json!({u32::from(r.id()?).to_string(): STANDARD.encode(r.serialize()?)})) };
    Ok(json!({
        "WARNING": "REAL Signal account. Contains private keys and the account password. Never commit or share.",
        "environment": "production",
        "name": "sender", "number": number, "aci": aci, "pni": pni, "device_id": 1, "username": username,
        "password": password, "recovery_password": STANDARD.encode(recovery_password),
        "registration_id": registration_id, "pni_registration_id": pni_registration_id,
        "profile_key": STANDARD.encode(profile_key.get_bytes()),
        "access_key": STANDARD.encode(profile_key.derive_access_key()),
        "unrestricted_unidentified_access": true,
        "aci_identity_key_pair": STANDARD.encode(keys.identity.get(Aci).serialize()),
        "aci_identity_key": STANDARD.encode(keys.identity.get(Aci).identity_key().serialize()),
        "pni_identity_key_pair": STANDARD.encode(keys.identity.get(Pni).serialize()),
        "sender_certificate": sender_certificate.map(|c| STANDARD.encode(c)),
        "prekeys": {},
        "signed_prekeys": record_of(keys.signed.get(Aci))?, "kyber_prekeys": kyber_of(keys.kyber.get(Aci))?,
        "pni_signed_prekeys": record_of(keys.signed.get(Pni))?, "pni_kyber_prekeys": kyber_of(keys.kyber.get(Pni))?,
        "peers": [], "sessions": {}, "identities": {},
    }))
}

async fn register(number: &str, state: &Path) -> Result<()> {
    let account_path = state.join("account.json");
    if account_path.exists() {
        return Err(anyhow!("{} already exists: this number was registered from here. Move it away first if you really mean to register again.", account_path.display()));
    }
    let mut rng = rand::rng();
    let keys = generate_keys(&mut rng);
    let password = sample_password(&mut rng, PASSWORD_LEN);
    let mut recovery_password = [0u8; 32];
    rng.try_fill_bytes(&mut recovery_password).unwrap();
    let profile_key = {
        let mut randomness = [0u8; 32];
        rng.try_fill_bytes(&mut randomness).unwrap();
        ProfileKey::generate(randomness)
    };
    let registration_id = rng.random::<u16>() & 0x3FFF;
    let pni_registration_id = rng.random::<u16>() & 0x3FFF;

    // Before anything is sent: what the server may come to know is already on disk.
    let pending_path = state.join("pending-registration.json");
    write_private(&pending_path, &account_json(number, "", "", &password, &recovery_password, registration_id, pni_registration_id, &profile_key, &keys, None, None)?)?;
    record("keys-generated-and-saved", json!({"file": pending_path.display().to_string(), "registration_id": registration_id, "pni_registration_id": pni_registration_id, "password_length": password.len()}));

    let connector = Connector::new();
    record("create-session", json!({"number": number}));
    let mut service = RegistrationService::create_session(CreateSession { number: number.to_string(), ..Default::default() }, Box::new(connector))
        .await
        .map_err(|e| { record("create-session-error", json!({"error": format!("{e:?}")})); anyhow!("create_session failed: {e:?}") })?;
    record("session-created", session_json(&service));

    if service.session_state().requested_information.contains(&ChallengeOption::Captcha) {
        println!("\nA captcha is required.");
        println!("  1. Open https://signalcaptchas.org/registration/generate in a browser and solve it.");
        println!("  2. Copy the address of the \"Open Signal\" link (it starts with signalcaptcha://).");
        // The token is longer than the terminal's 1024-character line limit, so it cannot be
        // pasted at a prompt (the terminal stops accepting input and Enter does nothing). It is
        // read from the clipboard, or from STATE_DIR/captcha.txt if that file exists.
        let captcha_file = state.join("captcha.txt");
        println!("  3. With the link still on the clipboard, press Enter here. Do NOT paste it.");
        println!("     (Or save it in {} and press Enter.)", captcha_file.display());
        let pasted = loop {
            ask("  Press Enter when ready: ")?;
            let text = if captcha_file.exists() {
                std::fs::read_to_string(&captcha_file)?
            } else {
                String::from_utf8_lossy(&std::process::Command::new("/usr/bin/pbpaste").output()?.stdout).to_string()
            };
            let text = text.trim().to_string();
            if text.contains("signal-hcaptcha") || text.starts_with("signalcaptcha://") {
                println!("  Got a captcha token of {} characters.", text.len());
                break text;
            }
            println!("  That does not look like a captcha link ({} characters, should start with signalcaptcha://). Copy it again.", text.len());
        };
        let captcha = pasted.strip_prefix("signalcaptcha://").unwrap_or(&pasted).to_string();
        record("submit-captcha", json!({"captcha": captcha}));
        service.submit_captcha(&captcha).await
            .map_err(|e| { record("submit-captcha-error", json!({"error": format!("{e:?}")})); anyhow!("submit_captcha failed: {e:?}") })?;
        record("captcha-accepted", session_json(&service));
    } else {
        println!("No captcha was requested.");
        record("no-captcha-requested", session_json(&service));
    }

    if !(service.session_state().allowed_to_request_code || service.session_state().next_sms.is_some()) {
        record("not-allowed-to-request-code", session_json(&service));
        return Err(anyhow!("the server does not allow requesting a code for this session (see the log)"));
    }
    record("request-verification-code", json!({"transport": "sms", "client": "relay-node-registration", "languages": ["en"]}));
    service.request_verification_code(VerificationTransport::Sms, "relay-node-registration", LanguageList::parse(&["en"])?).await
        .map_err(|e| { record("request-verification-code-error", json!({"error": format!("{e:?}")})); anyhow!("request_verification_code failed: {e:?}") })?;
    record("verification-code-requested", session_json(&service));

    let code = ask("\nEnter the verification code sent by SMS (digits only): ")?;
    let code: String = code.chars().filter(|c| c.is_ascii_digit()).collect();
    record("submit-verification-code", json!({"code": code}));
    service.submit_verification_code(&code).await
        .map_err(|e| { record("submit-verification-code-error", json!({"error": format!("{e:?}")})); anyhow!("submit_verification_code failed: {e:?}") })?;
    record("verification-code-submitted", session_json(&service));
    if !service.session_state().verified {
        return Err(anyhow!("the server did not mark the session verified (wrong code?). Nothing was registered."));
    }

    record("register-account", json!({
        "notification": "will fetch messages", "registration_id": registration_id, "pni_registration_id": pni_registration_id,
        "unrestricted_unidentified_access": true, "capabilities": ["spqr"], "discoverable_by_phone_number": false, "skip_device_transfer": true,
        "aci_identity_key": STANDARD.encode(keys.identity.get(libsignal_core::ServiceIdKind::Aci).identity_key().serialize())}));
    let access_key = profile_key.derive_access_key();
    let result = service
        .register_account(
            NewMessageNotification::WillFetchMessages,
            ProvidedAccountAttributes {
                recovery_password: &recovery_password,
                registration_id,
                pni_registration_id,
                name: None,
                registration_lock: None,
                unidentified_access_key: &access_key,
                unrestricted_unidentified_access: true,
                capabilities: HashSet::from(["spqr"]),
                discoverable_by_phone_number: false,
            },
            Some(SkipDeviceTransfer),
            ForServiceIds::generate(|k| keys.account.get(k).as_borrowed()),
            &password,
        )
        .await
        .map_err(|e| { record("register-account-error", json!({"error": format!("{e:?}")})); anyhow!("register_account failed: {e:?}") })?;
    let (aci, pni) = (result.aci.service_id_string(), result.pni.service_id_string());
    record("registered", json!({"aci": aci, "pni": pni, "number": result.number}));
    write_private(&account_path, &account_json(&result.number, &aci, &pni, &password, &recovery_password, registration_id, pni_registration_id, &profile_key, &keys, None, None)?)?;
    println!("\nRegistered. Account id {aci}. Saved to {}", account_path.display());

    // After registration, on the authenticated socket: the sender certificate (needed to send
    // sealed-sender messages) and, optionally, a username so that people can find the account
    // (it is not discoverable by phone number).
    let connector = Connector::new();
    record("connect-authenticated", json!({"username": aci}));
    let chat = connector.authenticated(&aci, &password).await?;
    let mut certificate: Option<Vec<u8>> = None;
    match send_recorded(&chat, "sender-certificate", http::Method::GET, "/v1/certificate/delivery?includeE164=false", HeaderMap::new(), None).await {
        Ok((200, body)) => {
            let parsed: Value = serde_json::from_slice(&body).unwrap_or(Value::Null);
            certificate = parsed["certificate"].as_str().and_then(|c| STANDARD.decode(c).ok());
            if certificate.is_none() {
                eprintln!("The certificate response could not be read; see the log.");
            }
        }
        Ok((status, _)) => eprintln!("Sender certificate request answered {status}; see the log."),
        Err(e) => eprintln!("Sender certificate request failed: {e}"),
    }
    write_private(&account_path, &account_json(&result.number, &aci, &pni, &password, &recovery_password, registration_id, pni_registration_id, &profile_key, &keys, certificate.as_deref(), None)?)?;

    let nickname = ask("\nUsername nickname so a Signal user can find this account (letters, digits, underscore; empty to skip): ")?;
    let mut username: Option<String> = None;
    if !nickname.is_empty() {
        match set_username(&chat, &nickname).await {
            Ok(name) => {
                println!("Username set: {name}");
                username = Some(name);
            }
            Err(e) => eprintln!("Setting the username failed (the account is registered all the same): {e}"),
        }
    }
    write_private(&account_path, &account_json(&result.number, &aci, &pni, &password, &recovery_password, registration_id, pni_registration_id, &profile_key, &keys, certificate.as_deref(), username.as_deref())?)?;
    record("finished", json!({"account_file": account_path.display().to_string(), "has_sender_certificate": certificate.is_some(), "username": username}));
    let _ = std::fs::remove_file(&pending_path);
    chat.disconnect().await;
    println!("\nDone. Everything is in {}", state.display());
    Ok(())
}

/// Reserve and confirm a username, as relay-node does.
async fn set_username(chat: &ChatConnection, nickname: &str) -> Result<String> {
    let mut rng = rand::rng();
    let candidates = Username::candidates_from(&mut rng, nickname, NicknameLimits::default()).map_err(|e| anyhow!("username candidates: {e:?}"))?;
    let usernames: Vec<Username> = candidates.iter().map(|c| Username::new(c)).collect::<Result<Vec<_>, _>>().map_err(|e| anyhow!("username candidate: {e:?}"))?;
    let hashes: Vec<[u8; 32]> = usernames.iter().map(|u| u.hash()).collect();
    let json_header = HeaderMap::from_iter([(header::CONTENT_TYPE, HeaderValue::from_static("application/json"))]);
    let reserve = json!({"usernameHashes": hashes.iter().map(|h| URL_SAFE_NO_PAD.encode(h)).collect::<Vec<_>>()});
    record("username-candidates", json!({"candidates": candidates}));
    let (status, body) = send_recorded(chat, "username-reserve", http::Method::PUT, "/v1/accounts/username_hash/reserve", json_header.clone(), Some(serde_json::to_vec(&reserve)?)).await?;
    if status != 200 {
        return Err(anyhow!("reserve answered {status}"));
    }
    let reserved: Value = serde_json::from_slice(&body)?;
    let reserved_hash = URL_SAFE_NO_PAD.decode(reserved["usernameHash"].as_str().ok_or_else(|| anyhow!("no usernameHash in the reserve response"))?)?;
    let (chosen, _) = usernames.iter().zip(hashes.iter()).find(|(_, h)| h.as_slice() == reserved_hash.as_slice()).ok_or_else(|| anyhow!("the reserved hash matches no candidate"))?;
    let mut randomness = [0u8; 32];
    rng.try_fill_bytes(&mut randomness).unwrap();
    let proof = chosen.proof(&randomness).map_err(|e| anyhow!("username proof: {e:?}"))?;
    let (_entropy, encrypted) = create_for_username(&mut rng, chosen.to_string(), None).map_err(|e| anyhow!("username link: {e:?}"))?;
    let confirm = json!({"usernameHash": URL_SAFE_NO_PAD.encode(&reserved_hash), "zkProof": URL_SAFE_NO_PAD.encode(&proof), "encryptedUsername": URL_SAFE_NO_PAD.encode(&encrypted)});
    let (status, _) = send_recorded(chat, "username-confirm", http::Method::PUT, "/v1/accounts/username_hash/confirm", json_header, Some(serde_json::to_vec(&confirm)?)).await?;
    if status != 200 {
        return Err(anyhow!("confirm answered {status}"));
    }
    Ok(chosen.to_string())
}

#[tokio::main]
async fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (number, state) = match args.as_slice() {
        [command, number, state] if command == "register" => (number.clone(), PathBuf::from(state)),
        _ => return Err(anyhow!("usage: real-signal-register register PHONE_NUMBER STATE_DIR")),
    };
    if !number.starts_with('+') || !number[1..].chars().all(|c| c.is_ascii_digit()) {
        return Err(anyhow!("the phone number must look like +15551234567"));
    }
    std::fs::create_dir_all(&state)?;
    std::fs::set_permissions(&state, std::fs::Permissions::from_mode(0o700))?;
    *RECORD.lock().unwrap() = Some(private_file(&state.join("registration-log.jsonl"), true)?);
    let trace = private_file(&state.join("libsignal-trace.log"), true)?;
    log::set_boxed_logger(Box::new(TraceLog(Mutex::new(trace)))).map_err(|e| anyhow!("logger: {e}"))?;
    log::set_max_level(log::LevelFilter::Trace);
    record("start", json!({"program": "real-signal-register", "client_name": CLIENT_NAME, "environment": "production", "number": number, "state": state.display().to_string()}));
    println!("This registers {number} with the REAL Signal service.");
    println!("Every step is recorded in {}", state.join("registration-log.jsonl").display());
    if ask("Type YES to continue: ")? != "YES" {
        record("cancelled-before-any-request", json!({}));
        println!("Nothing was sent.");
        return Ok(());
    }
    let outcome = register(&number, &state).await;
    if let Err(error) = &outcome {
        record("failed", json!({"error": format!("{error:#}")}));
        eprintln!("\nFailed: {error:#}\nThe record is in {}", state.display());
    }
    log::logger().flush();
    outcome
}
