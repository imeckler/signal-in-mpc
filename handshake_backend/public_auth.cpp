// Unverified OpenSSL boundary for PUBLIC server authentication metadata only.
// No TLS client private scalar, shared secret or traffic key enters this tool.
#include <openssl/evp.h>
#include <openssl/err.h>
#include <openssl/pem.h>
#include <openssl/rsa.h>
#include <openssl/x509.h>
#include <openssl/x509v3.h>
#include <cstdint>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <string>
#include <vector>

using Bytes = std::vector<unsigned char>;
static Bytes unhex(const std::string& s) {
    if (s.size() % 2 || s.size() > 2 * 1048576) throw std::runtime_error("invalid hex length");
    Bytes out;
    auto digit = [](char c) -> unsigned { if(c >= '0' && c <= '9') return c-'0';
        if(c >= 'a' && c <= 'f') return c-'a'+10; throw std::runtime_error("invalid hex"); };
    for (size_t i=0;i<s.size();i+=2) out.push_back((digit(s[i]) << 4) | digit(s[i+1]));
    return out;
}

int main(int argc, char** argv) {
    try {
        // HOST CA_FILE SCHEME TRANSCRIPT_SHA256 SIGNATURE CERT_DER [CHAIN_DER...]
        if (argc < 7 || argc > 18) throw std::runtime_error("invalid public-auth arguments");
        const std::string hostname=argv[1], ca=argv[2];
        if (hostname.empty() || hostname.size()>253 || hostname.find_first_of("\r\n\t /\\")!=std::string::npos)
            throw std::runtime_error("invalid hostname");
        size_t consumed=0;
        unsigned scheme=std::stoul(argv[3], &consumed);
        if (consumed != std::string(argv[3]).size()) throw std::runtime_error("invalid scheme");
        Bytes transcript=unhex(argv[4]), signature=unhex(argv[5]);
        if (transcript.size()!=32 || signature.empty() || signature.size()>16384)
            throw std::runtime_error("invalid authentication input length");
        std::vector<std::unique_ptr<X509,decltype(&X509_free)>> certs;
        for (int i=6;i<argc;i++) {
            Bytes der=unhex(argv[i]); const unsigned char* cursor=der.data();
            X509* parsed=d2i_X509(nullptr,&cursor,der.size());
            if (!parsed || cursor!=der.data()+der.size()) { X509_free(parsed); throw std::runtime_error("invalid DER certificate"); }
            certs.emplace_back(parsed,X509_free);
        }
        std::unique_ptr<X509_STORE,decltype(&X509_STORE_free)> store(X509_STORE_new(),X509_STORE_free);
        if (!store || (ca=="system" ? X509_STORE_set_default_paths(store.get()) :
                X509_STORE_load_locations(store.get(),ca.c_str(),nullptr)) != 1)
            throw std::runtime_error("cannot load configured trust anchors");
        STACK_OF(X509)* chain=sk_X509_new_null();
        if (!chain) throw std::runtime_error("chain allocation failed");
        std::unique_ptr<STACK_OF(X509),void(*)(STACK_OF(X509)*)> chainOwner(chain,[](STACK_OF(X509)* p){sk_X509_free(p);});
        for(size_t i=1;i<certs.size();i++) sk_X509_push(chain,certs[i].get());
        std::unique_ptr<X509_STORE_CTX,decltype(&X509_STORE_CTX_free)> ctx(X509_STORE_CTX_new(),X509_STORE_CTX_free);
        if (!ctx || X509_STORE_CTX_init(ctx.get(),store.get(),certs[0].get(),chain)!=1)
            throw std::runtime_error("verification setup failed");
        X509_VERIFY_PARAM* param=X509_STORE_CTX_get0_param(ctx.get());
        X509_VERIFY_PARAM_set_hostflags(param,X509_CHECK_FLAG_NO_PARTIAL_WILDCARDS | X509_CHECK_FLAG_NEVER_CHECK_SUBJECT);
        X509_VERIFY_PARAM_set_depth(param,10);
        X509_VERIFY_PARAM_set_auth_level(param,2);
        if (X509_VERIFY_PARAM_set1_host(param,hostname.c_str(),hostname.size())!=1 ||
                X509_STORE_CTX_set_purpose(ctx.get(),X509_PURPOSE_SSL_SERVER)!=1 || X509_verify_cert(ctx.get())!=1)
            throw std::runtime_error("certificate chain, time, usage or hostname validation failed");
        std::unique_ptr<EVP_PKEY,decltype(&EVP_PKEY_free)> key(X509_get_pubkey(certs[0].get()),EVP_PKEY_free);
        if (!key) throw std::runtime_error("certificate has no public key");
        const EVP_MD* digest=nullptr; bool pss=false;
        switch(scheme) {
        case 0x0804: case 0x0805: case 0x0806:
            if (EVP_PKEY_id(key.get())!=EVP_PKEY_RSA) throw std::runtime_error("RSAE signature/key mismatch");
            digest=scheme==0x0804?EVP_sha256():scheme==0x0805?EVP_sha384():EVP_sha512(); pss=true; break;
        case 0x0809: case 0x080a: case 0x080b:
            if (EVP_PKEY_id(key.get())!=EVP_PKEY_RSA_PSS) throw std::runtime_error("PSS signature/key mismatch");
            digest=scheme==0x0809?EVP_sha256():scheme==0x080a?EVP_sha384():EVP_sha512(); pss=true; break;
        case 0x0403: case 0x0503: case 0x0603: {
            char group[80]; size_t size=0;
            if (EVP_PKEY_id(key.get())!=EVP_PKEY_EC || EVP_PKEY_get_group_name(key.get(),group,sizeof(group),&size)!=1)
                throw std::runtime_error("ECDSA signature/key mismatch");
            std::string expected=scheme==0x0403?"prime256v1":scheme==0x0503?"secp384r1":"secp521r1";
            if (group!=expected) throw std::runtime_error("ECDSA scheme/curve mismatch");
            digest=scheme==0x0403?EVP_sha256():scheme==0x0503?EVP_sha384():EVP_sha512(); break; }
        case 0x0807: if(EVP_PKEY_id(key.get())!=EVP_PKEY_ED25519) throw std::runtime_error("Ed25519 mismatch"); break;
        case 0x0808: if(EVP_PKEY_id(key.get())!=EVP_PKEY_ED448) throw std::runtime_error("Ed448 mismatch"); break;
        default: throw std::runtime_error("forbidden TLS1.3 CertificateVerify scheme");
        }
        Bytes signedData(64,32);
        std::string context="TLS 1.3, server CertificateVerify";
        signedData.insert(signedData.end(),context.begin(),context.end()); signedData.push_back(0);
        signedData.insert(signedData.end(),transcript.begin(),transcript.end());
        std::unique_ptr<EVP_MD_CTX,decltype(&EVP_MD_CTX_free)> md(EVP_MD_CTX_new(),EVP_MD_CTX_free);
        EVP_PKEY_CTX* pctx=nullptr;
        if (!md || EVP_DigestVerifyInit(md.get(),&pctx,digest,nullptr,key.get())!=1)
            throw std::runtime_error("signature setup failed");
        if(pss && (EVP_PKEY_CTX_set_rsa_padding(pctx,RSA_PKCS1_PSS_PADDING)!=1 ||
                EVP_PKEY_CTX_set_rsa_pss_saltlen(pctx,EVP_MD_get_size(digest))!=1 ||
                EVP_PKEY_CTX_set_rsa_mgf1_md(pctx,digest)!=1)) throw std::runtime_error("PSS parameter setup failed");
        if(EVP_DigestVerify(md.get(),signature.data(),signature.size(),signedData.data(),signedData.size())!=1)
            throw std::runtime_error("CertificateVerify signature failed");
        std::cout << "authenticated\n";
        return 0;
    } catch(const std::exception& error) {
        std::cerr << error.what() << '\n'; return 1;
    }
}
