include $(TLS_ROOT)/WebSocketWork/Makefile
$(TLS_BUILD)/tls-native-batch-fixture: $(TLS_ROOT)/BatchThroughputWork/native_batch_fixture.cpp $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
