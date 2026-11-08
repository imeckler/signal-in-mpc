#pragma once
#include "ProviderCoordinator.h"
#include "../../signal_backend/TextNotificationWork/TextNotificationInput.h"
namespace tls_mpc_worker {
// Deferred stateless serialization of already shared text. The factory only
// moves this input; evaluation occurs after collective admission readiness.
class NativeTextInput final : public PrivateInputBuilder {
    Bits input,upstream;
public:
    NativeTextInput(Bits text_input,Bits computed_validity):input(std::move(text_input)),upstream(std::move(computed_validity)){validate_public_shape();}
    void validate_public_shape() const override {
        public_require(input.size()==472&&upstream.size()==8,"invalid private text input dimensions");
    }
    ProviderInput evaluate(Session& session) override {
        validate_public_shape();auto built=signal_mpc::split_text_notification(session.evaluate_text_notification(std::move(input)));
        auto valid=session.combine_private_validity(std::move(built.validity),std::move(upstream));
        return{std::move(built.payload),std::move(built.timestamp),std::move(valid)};
    }
};
}
