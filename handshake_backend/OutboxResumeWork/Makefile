include $(TLS_ROOT)/WebSocketWork/Makefile
$(TLS_BUILD)/tls-native-outbox-remask-fixture: $(TLS_ROOT)/OutboxResumeWork/native_fixture.cpp $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-public-constant-shape-check: $(TLS_ROOT)/RestoreAdmissionWork/constant_shape_checks.cpp $(wildcard $(TLS_ROOT)/*.h) $(wildcard $(TLS_ROOT)/../signal_backend/RecoveryWork/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(TLS_BUILD)/tls-public-constant-native-fixture: $(TLS_ROOT)/RestoreAdmissionWork/constant_native_fixture.cpp $(wildcard $(TLS_ROOT)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(TLS_ROOT) $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
