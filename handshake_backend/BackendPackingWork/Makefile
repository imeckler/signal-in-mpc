include $(TLS_ROOT)/WebSocketWork/Makefile
$(TLS_BUILD)/tls-backend-serialize-fixture: $(TLS_ROOT)/BackendPackingWork/serialize_fixture.cpp libSPDZ.so
	$(CXX) $(CFLAGS) -I. $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
