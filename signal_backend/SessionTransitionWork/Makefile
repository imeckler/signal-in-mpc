include CONFIG
TRANSITION_WORK ?= ../../../signal_backend/SessionTransitionWork
TRANSITION_OUTPUT ?= ../private-session-transition-adapters-probe
$(TRANSITION_OUTPUT): $(TRANSITION_WORK)/adapters_probe.cpp $(wildcard $(TRANSITION_WORK)/*.h) $(TRANSITION_WORK)/../../handshake_backend/NativeWorker.h libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TRANSITION_WORK) -I$(TRANSITION_WORK)/../../handshake_backend $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
