include $(TLS_ROOT)/WebSocketWork/Makefile
$(TLS_BUILD)/tls-small-field-guard: $(TLS_ROOT)/BooleanBackendSelectionWork/field_guard.cpp libSPDZ.so
	$(CXX) $(CFLAGS) -I. $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
