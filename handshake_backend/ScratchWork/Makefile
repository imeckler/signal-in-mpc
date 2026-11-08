# Invoke inside the separate patched tree after building its own libSPDZ.so.
include CONFIG
TLS_ROOT ?= ../../../handshake_backend
TLS_BUILD ?= ..
$(TLS_BUILD)/tls-scratch-fixture: $(TLS_ROOT)/ScratchWork/scratch_fixture.cpp $(TLS_ROOT)/ScratchWork/VmScratch.h $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-stacked-checks: $(TLS_ROOT)/ScratchWork/stacked_checks.cpp $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -fsanitize=address,undefined -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
