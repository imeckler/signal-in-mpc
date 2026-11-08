include CONFIG
TRANSITION_WORK ?= ../../../signal_backend/SessionTransitionWork
TRANSITION_OUTPUT ?= ../private-session-transition-adapters-probe
$(TRANSITION_OUTPUT): $(TRANSITION_WORK)/adapters_probe.cpp $(wildcard $(TRANSITION_WORK)/*.h) $(TRANSITION_WORK)/../../handshake_backend/NativeWorker.h libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TRANSITION_WORK) -I$(TRANSITION_WORK)/../../handshake_backend $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
TRANSITION_FIXTURE ?= ../private-session-transition-fixture
$(TRANSITION_FIXTURE): $(TRANSITION_WORK)/native_fixture.cpp $(wildcard $(TRANSITION_WORK)/*.h) $(TRANSITION_WORK)/../../handshake_backend/NativeWorker.h libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TRANSITION_WORK) -I$(TRANSITION_WORK)/../../handshake_backend $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@

NEW_DH_FIXTURE ?= ../private-new-dh-transition-fixture
$(NEW_DH_FIXTURE): $(TRANSITION_WORK)/new_dh_native_fixture.cpp $(wildcard $(TRANSITION_WORK)/*.h) $(TRANSITION_WORK)/../../handshake_backend/NativeWorker.h libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TRANSITION_WORK) -I$(TRANSITION_WORK)/../../handshake_backend $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
