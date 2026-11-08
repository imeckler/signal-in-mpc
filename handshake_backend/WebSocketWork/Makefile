include $(TLS_ROOT)/SessionWork/Makefile
$(TLS_BUILD)/tls-websocket-worker: $(TLS_ROOT)/WebSocketWork/worker_main.cpp $(PAYLOAD_HEADERS) $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-chat-response-fixture: $(TLS_ROOT)/WebSocketWork/chat_native_fixture.cpp $(wildcard $(TLS_ROOT)/WebSocketWork/*.h) $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-websocket-frame-fixture: $(TLS_ROOT)/WebSocketWork/frame_native_fixture.cpp $(wildcard $(TLS_ROOT)/WebSocketWork/*.h) $(wildcard $(TLS_ROOT)/PayloadWork/*.h) $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
