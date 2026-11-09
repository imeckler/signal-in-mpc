#pragma once
#include "../../signal_backend/RecoveryWork/AccountAdmission.h"
namespace tls_mpc_worker {
// Link-selected trusted embedding. No argv/RPC decoder can construct an
// AuthorizedRestoredAccount. The default is absent and the restore profile fails.
signal_mpc::recovery::AccountRecoveryResolver make_account_recovery_resolver();
}
