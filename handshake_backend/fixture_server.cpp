// PUBLIC-FIXTURE TEST SERVER ONLY. Real OpenSSL handshakes over memory BIOs.
#include <openssl/ssl.h>
#include <openssl/err.h>
#include <iostream>
#include <string>
#include <vector>
#include <stdexcept>

static std::vector<unsigned char> unhex(const std::string& s) {
    if(s=="-") return {};
    if(s.size()%2) throw std::runtime_error("odd hex");
    std::vector<unsigned char> out;
    for(size_t i=0;i<s.size();i+=2) out.push_back(std::stoul(s.substr(i,2),nullptr,16));
    return out;
}
static std::string hex(const std::vector<unsigned char>& bytes) {
    const char* digits="0123456789abcdef"; std::string out;
    for(unsigned b:bytes) {out+=digits[b>>4];out+=digits[b&15];} return out.empty()?"-":out;
}
static int alpn(SSL*, const unsigned char** out,unsigned char* length,const unsigned char* in,unsigned size,void* argument) {
    static const unsigned char h1[]={8,'h','t','t','p','/','1','.','1'};
    static const unsigned char h2[]={2,'h','2'};
    const bool use_h2=argument && std::string(static_cast<const char*>(argument))=="h2";
    return SSL_select_next_proto(const_cast<unsigned char**>(out),length,use_h2?h2:h1,use_h2?sizeof(h2):sizeof(h1),in,size)==OPENSSL_NPN_NEGOTIATED?
        SSL_TLSEXT_ERR_OK:SSL_TLSEXT_ERR_ALERT_FATAL;
}
int main(int argc,char** argv) {
    try {
        if(argc!=5 && argc!=6) throw std::runtime_error("CERT KEY FRAGMENT REQUEST_CERT [ALPN]");
        SSL_CTX* ctx=SSL_CTX_new(TLS_server_method());
        if(!ctx || SSL_CTX_set_min_proto_version(ctx,TLS1_3_VERSION)!=1 || SSL_CTX_set_max_proto_version(ctx,TLS1_3_VERSION)!=1 ||
            SSL_CTX_set_ciphersuites(ctx,"TLS_AES_128_GCM_SHA256")!=1 || SSL_CTX_set1_groups_list(ctx,"X25519")!=1 ||
            SSL_CTX_use_certificate_chain_file(ctx,argv[1])!=1 || SSL_CTX_use_PrivateKey_file(ctx,argv[2],SSL_FILETYPE_PEM)!=1)
            throw std::runtime_error("OpenSSL fixture setup failed");
        SSL_CTX_set_num_tickets(ctx,0);
        SSL_CTX_set_alpn_select_cb(ctx,alpn,argc==6?argv[5]:nullptr);
        if(std::stoul(argv[3]) && SSL_CTX_set_max_send_fragment(ctx,std::stoul(argv[3]))!=1)
            throw std::runtime_error("invalid fixture record fragment limit");
        if(std::string(argv[4])=="yes") SSL_CTX_set_verify(ctx,SSL_VERIFY_PEER,nullptr);
        SSL* ssl=SSL_new(ctx); BIO* input=BIO_new(BIO_s_mem()); BIO* output=BIO_new(BIO_s_mem());
        BIO_set_mem_eof_return(input,-1); SSL_set_bio(ssl,input,output); SSL_set_accept_state(ssl);
        bool sent=false; std::string line;
        std::vector<unsigned char> previous;
        while(std::getline(std::cin,line)) {
            if(line=="quit") break;
            const bool command=line=="update" || line=="update-request" || line=="emit" ||
                line=="emit-corrupt" || line=="close" || line=="replay";
            if(command && !sent) throw std::runtime_error("post-handshake command before handshake");
            if(line=="update" || line=="update-request") {
                if(SSL_key_update(ssl,line=="update-request"?SSL_KEY_UPDATE_REQUESTED:SSL_KEY_UPDATE_NOT_REQUESTED)!=1 ||
                    SSL_do_handshake(ssl)!=1) throw std::runtime_error("server key update failed");
            } else if(line=="emit" || line=="emit-corrupt") {
                const std::string message="server application fixture";
                if(SSL_write(ssl,message.data(),message.size())!=static_cast<int>(message.size()))
                    throw std::runtime_error("server application write failed");
            } else if(line=="close") {
                const int result=SSL_shutdown(ssl);
                if(result<0 && SSL_get_error(ssl,result)!=SSL_ERROR_WANT_READ)
                    throw std::runtime_error("server shutdown failed");
            } else if(line!="replay") {
                auto bytes=unhex(line);
                if(!bytes.empty() && BIO_write(input,bytes.data(),bytes.size())!=static_cast<int>(bytes.size()))
                    throw std::runtime_error("fixture input write failed");
                if(!sent) {
                    int result=SSL_do_handshake(ssl);
                    if(result!=1) { int error=SSL_get_error(ssl,result);
                        if(error!=SSL_ERROR_WANT_READ && error!=SSL_ERROR_WANT_WRITE) throw std::runtime_error("OpenSSL handshake failed"); }
                    if(SSL_is_init_finished(ssl)) { const char message[]="server application fixture";
                        if(SSL_write(ssl,message,sizeof(message)-1)<=0) throw std::runtime_error("server application write failed"); sent=true; }
                } else {
                    // SSL_read processes incoming updates/alerts. Its next write
                    // automatically answers a requested update before the data.
                    unsigned char plaintext[16384];
                    for(;;) {
                        const int count=SSL_read(ssl,plaintext,sizeof(plaintext));
                        if(count>0) {
                            const std::string echo="echo:"+std::string(reinterpret_cast<char*>(plaintext),count);
                            if(SSL_write(ssl,echo.data(),echo.size())!=static_cast<int>(echo.size()))
                                throw std::runtime_error("server echo failed");
                        } else {
                            const int error=SSL_get_error(ssl,count);
                            if(error!=SSL_ERROR_WANT_READ && error!=SSL_ERROR_WANT_WRITE && error!=SSL_ERROR_ZERO_RETURN)
                                throw std::runtime_error("server application read failed");
                            break;
                        }
                    }
                }
            }
            std::vector<unsigned char> wire; unsigned char buffer[4096]; int count;
            while((count=BIO_read(output,buffer,sizeof(buffer)))>0) wire.insert(wire.end(),buffer,buffer+count);
            if(line=="emit-corrupt" && !wire.empty()) wire.back()^=1;
            if(line=="replay") wire=previous;
            else if(!wire.empty()) previous=wire;
            std::cout<<(SSL_is_init_finished(ssl)?"ready ":"waiting ")<<hex(wire)<<std::endl;
        }
        SSL_free(ssl); SSL_CTX_free(ctx); return 0;
    } catch(const std::exception& error) { std::cerr<<error.what()<<'\n'; ERR_print_errors_fp(stderr); return 1; }
}
