include CONFIG
SIGNAL_WORK ?= ../../../signal_backend/SealedSenderWork
SIGNAL_OUTPUT ?= ../private-service-fixture
$(SIGNAL_OUTPUT): $(SIGNAL_WORK)/native_fixture.cpp $(wildcard $(SIGNAL_WORK)/*.h) $(SIGNAL_WORK)/../../handshake_backend/NativeWorker.h libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(SIGNAL_WORK) -I$(SIGNAL_WORK)/../../handshake_backend $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
ADAPTER_OUTPUT ?= ../private-service-adapters-probe
$(ADAPTER_OUTPUT): $(SIGNAL_WORK)/adapters_probe.cpp $(wildcard $(SIGNAL_WORK)/*.h) $(SIGNAL_WORK)/../../handshake_backend/NativeWorker.h libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(SIGNAL_WORK) -I$(SIGNAL_WORK)/../../handshake_backend $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
