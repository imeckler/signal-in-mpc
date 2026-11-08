# Invoke with -f Makefile -f /absolute/path/to/fixture.mk inside candidate runtime.
TLS_EXCEPTION_WORK ?= /Users/izzy/repos/tls-mpc/handshake_backend/ExceptionWork
../tls-caught-failure-fixture: $(TLS_EXCEPTION_WORK)/caught_failure_fixture.cpp libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_EXCEPTION_WORK)/.. $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
