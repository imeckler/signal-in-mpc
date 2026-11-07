include CONFIG
SIGNAL_TINIER_SOURCE ?= ../../../SignalReference/TinierWork
signal-tinier-type-probe: $(SIGNAL_TINIER_SOURCE)/type_probe.cpp libSPDZ.so
	$(CXX) $(CFLAGS) -I. $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
