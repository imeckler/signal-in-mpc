#include "NativeProvider.h"
#include <type_traits>
static_assert(std::is_base_of_v<tls_mpc_worker::ProviderRegistry::Provider,tls_mpc_worker::NativeProvider>);
int main(){return 0;}
