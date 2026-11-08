#include "ProviderCoordinator.h"
namespace tls_mpc_worker {
// Standalone embedding deliberately has no provider or share/plaintext importer.
ProviderFactory make_provider_factory(){return {};}
}
