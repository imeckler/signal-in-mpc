include CONFIG
SHARD_WORK ?= ../../../signal_backend/RecoveryWork/ShardedAccountWork
SHARD_OUTPUT ?= ../signal-sharded-account-fixture
-include $(SHARD_OUTPUT).d
$(SHARD_OUTPUT): $(SHARD_WORK)/fixture.cpp $(SHARD_WORK)/Makefile $(wildcard $(SHARD_WORK)/*.h) $(SHARD_WORK)/../AccountCheckpointCoordinator.h libSPDZ.so
	$(CXX) $(CFLAGS) -MMD -MP -MF $(SHARD_OUTPUT).d -std=c++20 -I. -I$(SHARD_WORK) -I$(SHARD_WORK)/../../../handshake_backend $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
SHARD_HEADER_OUTPUT ?= ../signal-sharded-header-probe
$(SHARD_HEADER_OUTPUT): $(SHARD_WORK)/header_probe.cpp $(wildcard $(SHARD_WORK)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -std=c++20 -I. -I$(SHARD_WORK) -I$(SHARD_WORK)/../../../handshake_backend $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
SHARD_FACTORY_OUTPUT ?= ../signal-sharded-factory-probe
$(SHARD_FACTORY_OUTPUT): $(SHARD_WORK)/header_probe.cpp $(SHARD_WORK)/FreshProviderFactory.cpp $(SHARD_WORK)/RestoredProviderFactory.cpp $(wildcard $(SHARD_WORK)/*.h) libSPDZ.so
	$(CXX) $(CFLAGS) -std=c++20 -I. -I$(SHARD_WORK) -I$(SHARD_WORK)/../../../handshake_backend $< $(SHARD_WORK)/FreshProviderFactory.cpp $(SHARD_WORK)/RestoredProviderFactory.cpp $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
SHARD_TLS_ROOT ?= $(SHARD_WORK)/../../../handshake_backend
SHARD_TLS_BUILD ?= ../tls-sharded-account-native/v1-candidate-1
-include $(SHARD_TLS_BUILD)/.fresh-main.d $(SHARD_TLS_BUILD)/.fresh-factory.d $(SHARD_TLS_BUILD)/.restored-main.d $(SHARD_TLS_BUILD)/.restored-factory.d
$(SHARD_TLS_BUILD)/.fresh-main.o: $(SHARD_TLS_ROOT)/WebSocketWork/mux_worker_main.cpp
	$(CXX) $(CFLAGS) -MMD -MP -MF $(SHARD_TLS_BUILD)/.fresh-main.d -I. -I$(SHARD_TLS_ROOT) -I$(SHARD_TLS_ROOT)/WebSocketWork -c $< -o $@
$(SHARD_TLS_BUILD)/.fresh-factory.o: $(SHARD_WORK)/FreshProviderFactory.cpp
	$(CXX) $(CFLAGS) -MMD -MP -MF $(SHARD_TLS_BUILD)/.fresh-factory.d -I. -I$(SHARD_TLS_ROOT) -I$(SHARD_TLS_ROOT)/WebSocketWork -c $< -o $@
$(SHARD_TLS_BUILD)/.restored-main.o: $(SHARD_TLS_ROOT)/WebSocketWork/mux_worker_main.cpp
	$(CXX) $(CFLAGS) -DTLS_ACCOUNT_RESTORE_PROFILE -MMD -MP -MF $(SHARD_TLS_BUILD)/.restored-main.d -I. -I$(SHARD_TLS_ROOT) -I$(SHARD_TLS_ROOT)/WebSocketWork -c $< -o $@
$(SHARD_TLS_BUILD)/.restored-factory.o: $(SHARD_WORK)/RestoredProviderFactory.cpp
	$(CXX) $(CFLAGS) -DTLS_ACCOUNT_RESTORE_PROFILE -MMD -MP -MF $(SHARD_TLS_BUILD)/.restored-factory.d -I. -I$(SHARD_TLS_ROOT) -I$(SHARD_TLS_ROOT)/WebSocketWork -c $< -o $@
$(SHARD_TLS_BUILD)/tls-sharded-fresh-worker: $(SHARD_TLS_BUILD)/.fresh-main.o $(SHARD_TLS_BUILD)/.fresh-factory.o libSPDZ.so
	$(CXX) $(CFLAGS) $(filter %.o,$^) $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
$(SHARD_TLS_BUILD)/tls-sharded-restored-worker: $(SHARD_TLS_BUILD)/.restored-main.o $(SHARD_TLS_BUILD)/.restored-factory.o libSPDZ.so
	$(CXX) $(CFLAGS) $(filter %.o,$^) $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
