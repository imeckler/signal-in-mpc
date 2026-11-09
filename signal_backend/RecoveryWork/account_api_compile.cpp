#include "AccountAdmission.h"
#include "NativeAccountReadmit.h"
#include "NativeAccountOutbox.h"
#include "AccountDurableOwnerV1.h"
#include "AccountRecoveryEngineV1.h"
#include "AccountCheckpointCoordinator.h"
#include <type_traits>
static_assert(!std::is_copy_constructible_v<signal_mpc::recovery::AuthorizedRestoredAccount>);
static_assert(!std::is_default_constructible_v<signal_mpc::recovery::AuthorizedRestoredAccount>);
void types(signal_mpc::recovery::AccountRecoveryResolver resolver){(void)resolver;}
