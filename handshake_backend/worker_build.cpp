// Compile/link check only: explicit instantiation checks the persistent adapter
// against the pinned runtime. Does not start MPC parties or open any sockets.
#include "NativeDispatch.h"
static_assert(sizeof(tls_mpc_worker::Field) >= 32);
int main() { return 0; }
// Force all adapter methods to be type-checked and emitted by the compiler.
auto begin_method = &tls_mpc_worker::Worker::begin;
auto agreement_method = &tls_mpc_worker::Worker::agreement;
auto binary_method = &tls_mpc_worker::Worker::binary;

auto session_begin = &tls_mpc_worker::Session::begin;
auto session_derive = &tls_mpc_worker::Session::derive;
auto session_open = &tls_mpc_worker::Session::open_handshake;
auto session_verify = &tls_mpc_worker::Session::verify_finished;
auto session_finish = &tls_mpc_worker::Session::finish;

auto dispatch_method = &tls_mpc_worker::Dispatch::call;
