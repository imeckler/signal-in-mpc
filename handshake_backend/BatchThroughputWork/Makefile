include $(TLS_ROOT)/WebSocketWork/Makefile
$(TLS_BUILD)/tls-native-batch-fixture: $(TLS_ROOT)/BatchThroughputWork/native_batch_fixture.cpp $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-native-batch-mixed-fixture: $(TLS_ROOT)/BatchThroughputWork/native_batch_fixture.cpp $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-batch-service-api-probe: $(TLS_ROOT)/BatchThroughputWork/service_api_probe.cpp $(wildcard $(TLS_ROOT)/BatchThroughputWork/*.h) $(wildcard $(TLS_ROOT)/WebSocketWork/*.h) $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) -I$(TLS_ROOT)/WebSocketWork $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-text-throughput-fixture-worker: $(TLS_ROOT)/WebSocketWork/mux_worker_main.cpp $(TLS_ROOT)/BatchThroughputWork/TextExtendedMuxFixtureFactory.cpp $(wildcard $(TLS_ROOT)/BatchThroughputWork/*.h) $(wildcard $(TLS_ROOT)/WebSocketWork/*.h) $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -DTLS_DIAGNOSTIC_V4_PROFILE -I. -I$(TLS_ROOT) -I$(TLS_ROOT)/WebSocketWork $< $(TLS_ROOT)/BatchThroughputWork/TextExtendedMuxFixtureFactory.cpp $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
