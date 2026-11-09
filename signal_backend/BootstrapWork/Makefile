include CONFIG
BOOTSTRAP_WORK ?= ../../../signal_backend/BootstrapWork
BOOTSTRAP_PROBE ?= ../signal-bootstrap-adapter-probe
$(BOOTSTRAP_PROBE): $(BOOTSTRAP_WORK)/adapter_probe.cpp $(BOOTSTRAP_WORK)/NativeKyber1024.h $(BOOTSTRAP_WORK)/NativeBootstrapDh.h libSPDZ.so
	$(CXX) $(CFLAGS) -MMD -MP -MF $(BOOTSTRAP_PROBE).d -I. -I$(BOOTSTRAP_WORK) -I$(BOOTSTRAP_WORK)/../../handshake_backend $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
