TLS_PACKING_WORK ?= /Users/izzy/repos/tls-mpc/handshake_backend/BackendPackingWork
../tls-tinier-width-checks: $(TLS_PACKING_WORK)/tinier_mac_width_checks.cpp libSPDZ.so
	$(CXX) $(CFLAGS) -fsanitize=address,undefined -I. $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
