include $(TLS_ROOT)/TransportEpochWork/Makefile
$(TLS_BUILD)/tls-worker: $(TLS_ROOT)/SessionWork/worker_main.cpp $(TLS_ROOT)/SessionWork/NativeLifecycle.h $(TLS_ROOT)/SessionWork/ErasedHostCall.h $(TLS_ROOT)/LifecycleWork/SecureGmp.h $(wildcard $(TLS_ROOT)/*.h) $(TLS_ROOT)/../signal_backend/SendShape.h libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-session-host-checks: $(TLS_ROOT)/SessionWork/host_checks.cpp $(TLS_ROOT)/SessionWork/ErasedHostCall.h libSPDZ.so
	$(CXX) $(CFLAGS) -fsanitize=address,undefined -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
