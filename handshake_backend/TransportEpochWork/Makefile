include $(TLS_ROOT)/LifecycleWork/Makefile
$(TLS_BUILD)/tls-transport-epoch-fixture: $(TLS_ROOT)/TransportEpochWork/transport_fixture.cpp $(TLS_ROOT)/LifecycleWork/SecureGmp.h $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-erased-host-checks: $(TLS_ROOT)/TransportEpochWork/host_checks.cpp $(TLS_ROOT)/TransportEpochWork/ErasedHostCall.h libSPDZ.so
	$(CXX) $(CFLAGS) -fsanitize=address,undefined -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
