include CONFIG
ACCOUNT_WORK ?= ../../../signal_backend/RecoveryWork
ACCOUNT_OUTPUT ?= ../signal-account-capture-fixture
-include $(ACCOUNT_OUTPUT).d
$(ACCOUNT_OUTPUT): $(ACCOUNT_WORK)/AccountCaptureWork/fixture.cpp $(ACCOUNT_WORK)/AccountCaptureWork/Makefile $(ACCOUNT_WORK)/AccountCaptureWork/PublicAccountFixture.h $(wildcard $(ACCOUNT_WORK)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -MMD -MP -MF $(ACCOUNT_OUTPUT).d -std=c++20 -I. -I$(ACCOUNT_WORK) -I$(ACCOUNT_WORK)/../../handshake_backend $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
