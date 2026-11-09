#pragma once
#include "NativeProvider.h"
#include "../RestoreAdmissionWork/CoordinatedConversation.h"
namespace tls_mpc_worker {
using DurableConversationHooks=DurableConversationHooksT<Bits>;
using NativeConversation=CoordinatedConversation<Bits,Session,Collective>;
}
