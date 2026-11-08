include $(TLS_ROOT)/LifetimeWork/Makefile
$(TLS_BUILD)/tls-byte-buffer-checks: $(TLS_ROOT)/ByteBufferWork/buffer_checks.cpp Tools/octetStream.cpp libSPDZ.so
	$(CXX) $(CFLAGS) -fsanitize=address,undefined -I. -I$(TLS_ROOT) $< Tools/octetStream.cpp $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
