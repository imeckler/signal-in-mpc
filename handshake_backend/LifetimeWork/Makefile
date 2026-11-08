include $(TLS_ROOT)/ScratchWork/Makefile
$(TLS_BUILD)/tls-lifetime-checks: $(TLS_ROOT)/LifetimeWork/lifetime_checks.cpp $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -fsanitize=address,undefined -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
