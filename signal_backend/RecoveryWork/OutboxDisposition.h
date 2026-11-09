#pragma once
namespace signal_mpc::recovery {
// Encoding constants only. The actual value is shared/private in the archive;
// never decode it through a host branch. ServerAccepted is not recipient delivery.
enum class OutboxDisposition : unsigned char {
 Absent=0,CommittedUnsent=1,TransportAttempted=2,
 ObservedServerAccepted=3,ObservedServerRejected=4,Uncertain=5
};
}
