# Invoke inside the pinned isolated MP-SPDZ tree.
include CONFIG
TLS_ROOT ?= ../../../handshake_backend
TLS_BUILD ?= ..
SESSION_DEPENDENCIES := $(wildcard $(TLS_ROOT)/WebSocketWork/*.h) $(wildcard $(TLS_ROOT)/PayloadWork/*.h) $(wildcard $(TLS_ROOT)/../signal_backend/SealedSenderWork/*.h) $(wildcard $(TLS_ROOT)/../signal_backend/VariableServiceWork/*.h)
$(TLS_BUILD)/tls-worker-build $(TLS_BUILD)/tls-worker: $(SESSION_DEPENDENCIES)
$(TLS_BUILD)/tls-worker-build: $(TLS_ROOT)/worker_build.cpp $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-pinned-probe: $(TLS_ROOT)/pinned_program_probe.cpp $(TLS_ROOT)/PinnedPrograms.h $(TLS_ROOT)/PublicProtocol.h libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-worker: $(TLS_ROOT)/worker_main.cpp $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-strong-profile-checks: $(TLS_ROOT)/strong_profile_checks.cpp $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-shape-probe: $(TLS_ROOT)/shape_compiler_probe.cpp $(TLS_ROOT)/ShapeCompiler.h $(TLS_ROOT)/KernelShape.h $(TLS_ROOT)/PinnedPrograms.h libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-application-shape-fixture: $(TLS_ROOT)/application_shape_fixture.cpp $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
