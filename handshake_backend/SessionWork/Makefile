include $(TLS_ROOT)/TransportEpochWork/Makefile
PAYLOAD_HEADERS := $(wildcard $(TLS_ROOT)/WebSocketWork/*.h) $(wildcard $(TLS_ROOT)/../signal_backend/VariableServiceWork/*.h) $(wildcard $(TLS_ROOT)/PayloadWork/*.h) $(wildcard $(TLS_ROOT)/../signal_backend/SealedSenderWork/*.h)
$(TLS_BUILD)/tls-websocket-upgrade-fixture: $(TLS_ROOT)/WebSocketWork/native_fixture.cpp $(wildcard $(TLS_ROOT)/WebSocketWork/*.h) $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-worker $(TLS_BUILD)/tls-private-application-worker: $(PAYLOAD_HEADERS)
$(TLS_BUILD)/tls-private-payload-fixture: $(TLS_ROOT)/PayloadWork/native_fixture.cpp $(PAYLOAD_HEADERS) $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-worker: $(TLS_ROOT)/SessionWork/worker_main.cpp $(TLS_ROOT)/SessionWork/NativeLifecycle.h $(TLS_ROOT)/SessionWork/ErasedHostCall.h $(TLS_ROOT)/LifecycleWork/SecureGmp.h $(wildcard $(TLS_ROOT)/*.h) $(TLS_ROOT)/../signal_backend/SendShape.h libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-session-host-checks: $(TLS_ROOT)/SessionWork/host_checks.cpp $(TLS_ROOT)/SessionWork/ErasedHostCall.h libSPDZ.so
	$(CXX) $(CFLAGS) -fsanitize=address,undefined -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-private-application-worker: $(TLS_ROOT)/SessionWork/worker_main.cpp $(TLS_ROOT)/SessionWork/NativeLifecycle.h $(TLS_ROOT)/SessionWork/ErasedHostCall.h $(TLS_ROOT)/LifecycleWork/SecureGmp.h $(wildcard $(TLS_ROOT)/*.h) $(wildcard $(TLS_ROOT)/../signal_backend/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -DTLS_PRIVATE_PRODUCER_FIXTURE -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
