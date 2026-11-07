#include "Networking/ssl_sockets.h"
#include <iostream>
#include <memory>

#ifndef TLS_MPC_REFRESH_TRANSPORT_POLICY
#error "Build with the refresh-only mandatory-peer-certificate TLS policy"
#endif
#if TLS_MPC_REFRESH_TRANSPORT_POLICY < 2
#error "Peer-certificate pinning is required"
#endif

struct ForgedRole
{
    std::shared_ptr<X509> certificate;
    std::shared_ptr<EVP_PKEY> key;
};

ForgedRole peer_issued_role_certificate()
{
    // Local development fixtures only. Nothing is written or printed: P2's
    // development CA key signs a certificate claiming the different role P1.
    std::unique_ptr<BIO, decltype(&BIO_free)> key_file(
            BIO_new_file((std::string(SSL_DIR) + "P2.key").c_str(), "r"), BIO_free);
    std::unique_ptr<BIO, decltype(&BIO_free)> cert_file(
            BIO_new_file((std::string(SSL_DIR) + "P2.pem").c_str(), "r"), BIO_free);
    if (!key_file || !cert_file) throw std::runtime_error("missing development TLS fixtures");
    std::shared_ptr<EVP_PKEY> key(
            PEM_read_bio_PrivateKey(key_file.get(), nullptr, nullptr, nullptr), EVP_PKEY_free);
    std::shared_ptr<X509> issuer(
            PEM_read_bio_X509(cert_file.get(), nullptr, nullptr, nullptr), X509_free);
    std::shared_ptr<X509> forged(X509_new(), X509_free);
    if (!key || !issuer || !forged ||
        X509_set_version(forged.get(), 2) != 1 ||
        ASN1_INTEGER_set(X509_get_serialNumber(forged.get()), 12345) != 1 ||
        !X509_gmtime_adj(X509_getm_notBefore(forged.get()), -60) ||
        !X509_gmtime_adj(X509_getm_notAfter(forged.get()), 3600) ||
        X509_NAME_add_entry_by_txt(X509_get_subject_name(forged.get()), "CN", MBSTRING_ASC,
                reinterpret_cast<const unsigned char*>("P1"), -1, -1, 0) != 1 ||
        X509_set_issuer_name(forged.get(), X509_get_subject_name(issuer.get())) != 1 ||
        X509_set_pubkey(forged.get(), key.get()) != 1 ||
        X509_sign(forged.get(), key.get(), EVP_sha256()) <= 0)
        throw std::runtime_error("cannot create development role-confusion fixture");
    return {forged, key};
}

// A memory BIO pair carries the handshake. No socket is opened or connected.
bool handshake(bool client_certificate, const std::string& expected_server,
        const ForgedRole* forged = nullptr, bool pin_server_peer = true)
{
    ssl_service service;
    ssl_ctx server_context("P0"), authenticated_client_context("P1");
    boost::asio::ssl::context anonymous_client_context(boost::asio::ssl::context::tlsv13);
    anonymous_client_context.add_verify_path(SSL_DIR);
    auto& client_context = client_certificate ?
        static_cast<boost::asio::ssl::context&>(authenticated_client_context) : anonymous_client_context;
    if (forged &&
        (SSL_CTX_use_certificate(client_context.native_handle(), forged->certificate.get()) != 1 ||
         SSL_CTX_use_PrivateKey(client_context.native_handle(), forged->key.get()) != 1))
        throw std::runtime_error("cannot install development role-confusion fixture");
    boost::asio::ssl::stream<boost::asio::ip::tcp::socket>
        client(service, client_context), server(service, server_context);
    refresh_verify_peer(client, expected_server);
    if (pin_server_peer) refresh_verify_peer(server, "P1");
    else
    {
        server.set_verify_mode(boost::asio::ssl::verify_peer |
                boost::asio::ssl::verify_fail_if_no_peer_cert);
        server.set_verify_callback(boost::asio::ssl::host_name_verification("P1"));
    }
    if (SSL_CTX_get_num_tickets(server_context.native_handle()) != 0 ||
        SSL_CTX_get_session_cache_mode(server_context.native_handle()) != SSL_SESS_CACHE_OFF)
        throw std::runtime_error("resumption was not disabled");
    BIO *client_bio = nullptr, *server_bio = nullptr;
    if (BIO_new_bio_pair(&client_bio, 0, &server_bio, 0) != 1)
        throw std::runtime_error("memory BIO allocation failed");
    SSL_set_bio(client.native_handle(), client_bio, client_bio);
    SSL_set_bio(server.native_handle(), server_bio, server_bio);
    SSL_set_connect_state(client.native_handle());
    SSL_set_accept_state(server.native_handle());
    bool client_done = false, server_done = false;
    for (int step = 0; step < 1000; ++step)
    {
        for (auto [stream, done] : {std::pair{client.native_handle(), &client_done},
                                   std::pair{server.native_handle(), &server_done}})
        {
            if (*done) continue;
            int result = SSL_do_handshake(stream);
            if (result == 1) *done = true;
            else
            {
                int error = SSL_get_error(stream, result);
                if (error != SSL_ERROR_WANT_READ && error != SSL_ERROR_WANT_WRITE)
                {
                    ERR_clear_error();
                    return false;
                }
            }
        }
        if (client_done && server_done)
            return SSL_version(client.native_handle()) == TLS1_3_VERSION &&
                SSL_version(server.native_handle()) == TLS1_3_VERSION;
    }
    throw std::runtime_error("memory BIO handshake stalled");
}

int main()
{
    try
    {
        if (!handshake(true, "P0")) throw std::runtime_error("valid mutual TLS failed");
        if (handshake(false, "P0")) throw std::runtime_error("missing client certificate accepted");
        if (handshake(true, "P4")) throw std::runtime_error("wrong peer role accepted");
        auto forged = peer_issued_role_certificate();
        if (!handshake(true, "P0", &forged, false))
            throw std::runtime_error("fixture did not exercise unpinned CA role confusion");
        if (handshake(true, "P0", &forged))
            throw std::runtime_error("peer-issued role certificate bypassed pinning");
        std::cout << "{\"status\":\"passed\",\"transport\":\"TLS1.3 mutual pinned certificates, no resumption\","
            << "\"missing_client_certificate_rejected\":true,\"wrong_role_rejected\":true,"
            << "\"peer_issued_role_certificate_rejected\":true,"
            << "\"sockets_used\":false}\n";
    }
    catch (const std::exception& error)
    {
        std::cerr << "TLS policy check failed: " << error.what() << '\n';
        return 1;
    }
}
