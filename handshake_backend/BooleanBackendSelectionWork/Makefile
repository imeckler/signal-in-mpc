include $(TLS_ROOT)/WebSocketWork/Makefile
$(TLS_BUILD)/tls-small-field-guard: $(TLS_ROOT)/BooleanBackendSelectionWork/field_guard.cpp libSPDZ.so
	$(CXX) $(CFLAGS) -I. $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-rep3-stat40-benchmark: $(TLS_ROOT)/BooleanBackendSelectionWork/rep3_stat40.cpp libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
