#include "NativeProvider.h"
#include "NativeTextInput.h"
#include "NativeChatMux.h"
#include "NativeConversation.h"
#include "PrivateMuxRegistry.h"
#include "NativeWebSocketMux.h"
#include <type_traits>
static_assert(std::is_base_of_v<tls_mpc_worker::ProviderRegistry::Provider,tls_mpc_worker::NativeProvider>);
static_assert(std::is_base_of_v<tls_mpc_worker::PrivateInputBuilder,tls_mpc_worker::NativeTextInput>);
// Compile the real OwnedBits template boundary without executing a protocol.
static void mux_api(tls_mpc_worker::Worker& worker,const tls_mpc_worker::PinnedPrograms& pinned) {
    using tls_mpc_worker::PublicBytes;
    using Owned=tls_mpc_worker::Bits;
    auto share=[](const PublicBytes&)->Owned{return {};};
    auto release=[](Owned)->PublicBytes{return {};};
    tls_mpc_worker::NativeChatMux mux(worker,pinned,share);
    mux.admit(0,Owned{},Owned{},share,release);
    mux.step(Owned{},Owned{},Owned{},Owned{});
    mux.finish_chunk(release,share);
}
static void registry_api(tls_mpc_worker::PrivateMuxRegistry<tls_mpc_worker::Bits,tls_mpc_worker::NativeConversation>& registry) {
    registry.produce(1,1);registry.authenticated_response_complete(0);
}
static void websocket_mux_api(tls_mpc_worker::Worker& worker,const tls_mpc_worker::PinnedPrograms& pinned,tls_mpc_worker::PrivatePayload chunk) {
    using Owned=tls_mpc_worker::Bits;using tls_mpc_worker::PublicBytes;
    auto share=[](const PublicBytes&)->Owned{return {};};auto release=[](Owned)->PublicBytes{return {};};
    tls_mpc_worker::NativeWebSocketMux websocket(worker,pinned,PublicBytes{},share);
    websocket.expect(0,Owned{},Owned{},share,release);
    websocket.feed(std::move(chunk),release,share);
}
int main(){return 0;}
