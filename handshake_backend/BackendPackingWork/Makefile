include $(TLS_ROOT)/WebSocketWork/Makefile
$(TLS_BUILD)/tls-backend-serialize-fixture: $(TLS_ROOT)/BackendPackingWork/serialize_fixture.cpp libSPDZ.so
	$(CXX) $(CFLAGS) -I. $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-diagnostic-api-probe: $(TLS_ROOT)/BackendPackingWork/diagnostic_api_probe.cpp $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-ccd-diagnostic-fixture: $(TLS_ROOT)/BackendPackingWork/ccd_micro_fixture.cpp $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-sacrifice-security-guard: $(TLS_ROOT)/BackendPackingWork/sacrifice_security_guard.cpp $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-ccd128-component: $(TLS_ROOT)/BackendPackingWork/ccd128_component_main.cpp $(TLS_ROOT)/BackendPackingWork/emit_backend_totals.h libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) -I$(TLS_ROOT)/BackendPackingWork $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
BMR_DIAGNOSTIC_OBJECTS := $(patsubst %.cpp,%.o,$(wildcard BMR/*.cpp BMR/network/*.cpp))
$(TLS_BUILD)/tls-bmr128-component: $(TLS_ROOT)/BackendPackingWork/bmr128_component_main.cpp $(TLS_ROOT)/BackendPackingWork/emit_backend_totals.h $(BMR_DIAGNOSTIC_OBJECTS) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT)/BackendPackingWork $< $(BMR_DIAGNOSTIC_OBJECTS) $(CURDIR)/libSPDZ.so $(LDLIBS) -lboost_thread -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-ccd-epoch-policy-fixture: $(TLS_ROOT)/BackendPackingWork/ccd_epoch_policy_fixture.cpp $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
