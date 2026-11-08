include $(TLS_ROOT)/ByteBufferWork/Makefile
$(TLS_BUILD)/tls-epoch-fixture: $(TLS_ROOT)/EpochWork/epoch_fixture.cpp $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-prng-lifetime-checks: $(TLS_ROOT)/EpochWork/prng_checks.cpp Tools/random.cpp libSPDZ.so
	$(CXX) $(CFLAGS) -fsanitize=address,undefined -I. -I$(TLS_ROOT) $< Tools/random.cpp $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-epoch-buffer-checks: $(TLS_ROOT)/EpochWork/buffer_checks.cpp Tools/octetStream.cpp libSPDZ.so
	$(CXX) $(CFLAGS) -fsanitize=address,undefined -I. -I$(TLS_ROOT) $< Tools/octetStream.cpp $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
