include $(TLS_ROOT)/WebSocketWork/Makefile
$(TLS_BUILD)/tls-native-public-cache-fixture: $(TLS_ROOT)/PublicProgramCacheWork/native_cache_fixture.cpp $(wildcard $(TLS_ROOT)/PublicProgramCacheWork/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) -I$(TLS_ROOT)/PublicProgramCacheWork $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
