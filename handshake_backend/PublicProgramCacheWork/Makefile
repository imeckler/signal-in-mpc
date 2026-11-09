include $(TLS_ROOT)/WebSocketWork/Makefile
$(TLS_BUILD)/tls-native-public-cache-fixture: $(TLS_ROOT)/PublicProgramCacheWork/native_cache_fixture.cpp $(wildcard $(TLS_ROOT)/PublicProgramCacheWork/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) -I$(TLS_ROOT)/PublicProgramCacheWork $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-public-producer-parse-probe: $(TLS_ROOT)/PublicProgramCacheWork/producer_parse_probe.cpp $(wildcard $(TLS_ROOT)/PublicProgramCacheWork/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-public-working-set-probe: $(TLS_ROOT)/PublicProgramCacheWork/working_set_probe.cpp $(wildcard $(TLS_ROOT)/PublicProgramCacheWork/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-native-cached-producer-fixture: $(TLS_ROOT)/PublicProgramCacheWork/cached_producer_fixture.cpp $(wildcard $(TLS_ROOT)/PublicProgramCacheWork/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) -I$(TLS_ROOT)/PublicProgramCacheWork $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
