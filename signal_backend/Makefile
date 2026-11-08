# Invoke in the isolated pinned MP-SPDZ runtime tree.
include CONFIG
SIGNAL_ROOT ?= ../../../signal_backend
SIGNAL_OUTPUT ?= ../signal-native-store-fixture
$(SIGNAL_OUTPUT): $(SIGNAL_ROOT)/native_store_fixture.cpp $(wildcard $(SIGNAL_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(SIGNAL_ROOT) -I$(SIGNAL_ROOT)/../handshake_backend $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
