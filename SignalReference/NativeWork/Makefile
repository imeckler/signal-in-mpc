# Invoke from the unmodified generic pinned MP-SPDZ tree.
include CONFIG
SIGNAL_ROOT ?= ../../SignalReference/NativeWork
SIGNAL_BUILD ?= ../signal-native
TLS_HEADERS ?= ../../handshake_backend
$(SIGNAL_BUILD)/signal-ccd128: $(SIGNAL_ROOT)/ccd128.cpp $(TLS_HEADERS)/LongFieldBit.h libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_HEADERS) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
