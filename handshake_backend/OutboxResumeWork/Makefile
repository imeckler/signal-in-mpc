include $(TLS_ROOT)/WebSocketWork/Makefile
$(TLS_BUILD)/tls-native-outbox-remask-fixture: $(TLS_ROOT)/OutboxResumeWork/native_fixture.cpp $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
