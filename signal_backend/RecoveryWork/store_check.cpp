// PUBLIC synthetic own evaluations; only authenticated CIPHERTEXT reaches disk.
#include "CiphertextStore.h"
#include "OwnShareBox.h"
#include <filesystem>
#include <fstream>
#include <sys/wait.h>
#include <iostream>
using namespace signal_mpc::recovery;
size_t checks=0;void check(bool b){require(b,"cipher store check failed");++checks;}
template<class F>void rejects(F&& f){try{f();}catch(const std::exception&){++checks;return;}throw std::runtime_error("cipher store rejection missing");}
int main(){try{
 char temporary[]="/tmp/signal-own-archive-store-XXXXXX";auto raw=::mkdtemp(temporary);require(raw,"store fixture directory failed");std::filesystem::path dir(raw);
 struct Remove{std::filesystem::path p;~Remove(){std::filesystem::remove_all(p);}}remove{dir};
 std::array<unsigned char,64> key;key.fill(33);OwnShareBox box(key);ShareDomain d{};d.party=0;d.epoch=1;d.slot=2;d.bit_count=8;
 SecretBytes bytes(128);for(size_t i=0;i<128;++i)bytes.data()[i]=i;QuarantinedEvaluations local(std::move(bytes));auto cipher=box.seal(d,local);auto digest=hash(cipher);
 auto child=::fork();require(child>=0,"store fixture fork failed");if(child==0){try{CiphertextStore store(dir.string());check(store.put(cipher)==digest);::_exit(0);}catch(...){::_exit(1);}}
 int code=0;check(::waitpid(child,&code,0)==child&&WIFEXITED(code)&&WEXITSTATUS(code)==0);
 CiphertextStore store(dir.string());check(store.get(digest,cipher.size())==cipher);check(store.put(cipher)==digest);auto opened=box.open_quarantined(d,store.get(digest,cipher.size()));check(CRYPTO_memcmp(opened.local_bytes().data(),local.local_bytes().data(),128)==0);
 auto names=std::vector<std::filesystem::path>();for(auto& f:std::filesystem::directory_iterator(dir))names.push_back(f.path());check(names.size()==1);
 rejects([&]{store.get(digest,cipher.size()-1);});auto wrong=digest;wrong[0]^=1;rejects([&]{store.get(wrong,cipher.size());});rejects([&]{store.put({});});
 auto file=names.front();{std::fstream f(file,std::ios::in|std::ios::out|std::ios::binary);char c;f.read(&c,1);c^=1;f.seekp(0);f.write(&c,1);}
 rejects([&]{store.get(digest,cipher.size());});rejects([&]{store.put(cipher);}); // never overwrite a conflicting immutable object.
 std::filesystem::remove(file);std::filesystem::create_symlink(dir/"missing",file);rejects([&]{store.get(digest,cipher.size());});rejects([&]{store.put(cipher);});
 std::cout<<checks<<" encrypted own-share persistence checks passed\n";return 0;
 }catch(const std::exception& e){std::cerr<<e.what()<<'\n';return 1;}}
