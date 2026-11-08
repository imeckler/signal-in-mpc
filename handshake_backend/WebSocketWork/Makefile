include $(TLS_ROOT)/SessionWork/Makefile
$(TLS_BUILD)/tls-websocket-worker: $(TLS_ROOT)/WebSocketWork/worker_main.cpp $(PAYLOAD_HEADERS) $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-chat-response-fixture: $(TLS_ROOT)/WebSocketWork/chat_native_fixture.cpp $(wildcard $(TLS_ROOT)/WebSocketWork/*.h) $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-websocket-frame-fixture: $(TLS_ROOT)/WebSocketWork/frame_native_fixture.cpp $(wildcard $(TLS_ROOT)/WebSocketWork/*.h) $(wildcard $(TLS_ROOT)/PayloadWork/*.h) $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-provider-api-probe: $(TLS_ROOT)/WebSocketWork/provider_api_probe.cpp $(PAYLOAD_HEADERS) $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) -I$(TLS_ROOT)/WebSocketWork $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
TLS_PROVIDER_FACTORY ?= $(TLS_ROOT)/WebSocketWork/NoProvider.cpp
$(TLS_BUILD)/tls-lifecycle-websocket-worker: $(TLS_ROOT)/WebSocketWork/lifecycle_worker_main.cpp $(TLS_PROVIDER_FACTORY) $(PAYLOAD_HEADERS) $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) -I$(TLS_ROOT)/WebSocketWork $< $(TLS_PROVIDER_FACTORY) $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-lifecycle-websocket-fixture-worker: $(TLS_ROOT)/WebSocketWork/lifecycle_worker_main.cpp $(TLS_ROOT)/WebSocketWork/FixtureProviderFactory.cpp $(PAYLOAD_HEADERS) $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) -I$(TLS_ROOT)/WebSocketWork $< $(TLS_ROOT)/WebSocketWork/FixtureProviderFactory.cpp $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-readiness-negative-fixture: $(TLS_ROOT)/WebSocketWork/readiness_native_fixture.cpp $(PAYLOAD_HEADERS) $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
