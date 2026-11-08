include CONFIG
SIGNAL_WORK ?= ../../../signal_backend/VariableServiceWork
SIGNAL_OUTPUT ?= ../private-variable-fixture
$(SIGNAL_OUTPUT): $(SIGNAL_WORK)/native_fixture.cpp $(wildcard $(SIGNAL_WORK)/*.h) $(SIGNAL_WORK)/../../handshake_backend/NativeWorker.h libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(SIGNAL_WORK) -I$(SIGNAL_WORK)/../../handshake_backend $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
