include $(TLS_ROOT)/EpochWork/Makefile
$(TLS_BUILD)/tls-lifecycle-fixture: $(TLS_ROOT)/LifecycleWork/lifecycle_fixture.cpp $(TLS_ROOT)/LifecycleWork/SecureGmp.h $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-owned-storage-checks: $(TLS_ROOT)/LifecycleWork/storage_checks.cpp $(TLS_ROOT)/LifecycleWork/SecureGmp.h libSPDZ.so
	$(CXX) $(CFLAGS) -fsanitize=address,undefined -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-lifecycle-buffer-checks: $(TLS_ROOT)/LifecycleWork/buffer_checks.cpp Tools/octetStream.cpp libSPDZ.so
	$(CXX) $(CFLAGS) -fsanitize=address,undefined -I. -I$(TLS_ROOT) $< Tools/octetStream.cpp $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
