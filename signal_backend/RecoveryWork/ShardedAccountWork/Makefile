include CONFIG
SHARD_WORK ?= ../../../signal_backend/RecoveryWork/ShardedAccountWork
SHARD_OUTPUT ?= ../signal-sharded-account-fixture
-include $(SHARD_OUTPUT).d
$(SHARD_OUTPUT): $(SHARD_WORK)/fixture.cpp $(SHARD_WORK)/Makefile $(wildcard $(SHARD_WORK)/*.h) $(SHARD_WORK)/../AccountCheckpointCoordinator.h libSPDZ.so
	$(CXX) $(CFLAGS) -MMD -MP -MF $(SHARD_OUTPUT).d -std=c++20 -I. -I$(SHARD_WORK) -I$(SHARD_WORK)/../../../handshake_backend $< $(CURDIR)/libSPDZ.so $(LDLIBS) -Wl,-rpath,$(CURDIR) -o $@
