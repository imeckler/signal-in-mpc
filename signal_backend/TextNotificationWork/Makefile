include CONFIG
TEXT_WORK ?= ../../../signal_backend/TextNotificationWork
TEXT_OUTPUT ?= ../private-text-adapters-probe
$(TEXT_OUTPUT): $(TEXT_WORK)/adapters_probe.cpp $(wildcard $(TEXT_WORK)/*.h) $(TEXT_WORK)/../../handshake_backend/NativeWorker.h libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TEXT_WORK) -I$(TEXT_WORK)/../../handshake_backend $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
