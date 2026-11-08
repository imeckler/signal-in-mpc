include $(TLS_ROOT)/WebSocketWork/Makefile
$(TLS_BUILD)/tls-backend-serialize-fixture: $(TLS_ROOT)/BackendPackingWork/serialize_fixture.cpp libSPDZ.so
	$(CXX) $(CFLAGS) -I. $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-diagnostic-api-probe: $(TLS_ROOT)/BackendPackingWork/diagnostic_api_probe.cpp $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-ccd-diagnostic-fixture: $(TLS_ROOT)/BackendPackingWork/ccd_micro_fixture.cpp $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
