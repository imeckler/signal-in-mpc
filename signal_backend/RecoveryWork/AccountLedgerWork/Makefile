include CONFIG
ACCOUNT_WORK ?= ../../../signal_backend/RecoveryWork
ACCOUNT_OUTPUT ?= ../signal-account-ledger-fixture
$(ACCOUNT_OUTPUT): $(ACCOUNT_WORK)/AccountLedgerWork/fixture.cpp $(wildcard $(ACCOUNT_WORK)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -std=c++20 -I. -I$(ACCOUNT_WORK) -I$(ACCOUNT_WORK)/../../handshake_backend $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
