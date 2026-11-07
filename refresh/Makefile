# Invoke from the pinned MP-SPDZ directory; never change its CONFIG or sources.
include CONFIG
REFRESH_ROOT ?= ../../refresh
REFRESH_BUILD ?= ../sharing-refresh

.PHONY: all
all: $(REFRESH_BUILD)/refresh-party $(REFRESH_BUILD)/refresh-local-checks $(REFRESH_BUILD)/refresh-tls-checks $(REFRESH_BUILD)/refresh-przs-party $(REFRESH_BUILD)/refresh-przs-checks

$(REFRESH_BUILD):
	mkdir -p $@

$(REFRESH_BUILD)/refresh-%: $(REFRESH_ROOT)/refresh_%.cpp $(REFRESH_ROOT)/NativeRefresh.h $(REFRESH_ROOT)/NativeSnapshot.h $(REFRESH_ROOT)/NativePrzs.h libSPDZ.so | $(REFRESH_BUILD)
	$(CXX) $(CFLAGS) -I$(REFRESH_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
