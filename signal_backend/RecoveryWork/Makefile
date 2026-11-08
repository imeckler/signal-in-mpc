include CONFIG
RECOVERY_WORK ?= ../../../signal_backend/RecoveryWork
RECOVERY_CODEC ?= ../signal-native-own-share-codec-check
$(RECOVERY_CODEC): $(RECOVERY_WORK)/native_codec_check.cpp $(wildcard $(RECOVERY_WORK)/*.h) $(RECOVERY_WORK)/../../handshake_backend/NativeWorker.h libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(RECOVERY_WORK) -I$(RECOVERY_WORK)/../../handshake_backend $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
RECOVERY_IMPORT_PROBE ?= ../signal-raw-field-import-probe
$(RECOVERY_IMPORT_PROBE): $(RECOVERY_WORK)/readmit_probe.cpp $(wildcard $(RECOVERY_WORK)/*.h) $(RECOVERY_WORK)/../../handshake_backend/NativeWorker.h libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(RECOVERY_WORK) -I$(RECOVERY_WORK)/../../handshake_backend $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
RECOVERY_IMPORT_FIXTURE ?= ../signal-raw-field-import-fixture
$(RECOVERY_IMPORT_FIXTURE): $(RECOVERY_WORK)/readmit_fixture.cpp $(wildcard $(RECOVERY_WORK)/*.h) $(RECOVERY_WORK)/../../handshake_backend/NativeWorker.h libSPDZ.so
	$(CXX) $(CFLAGS) -I. -I$(RECOVERY_WORK) -I$(RECOVERY_WORK)/../../handshake_backend $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
