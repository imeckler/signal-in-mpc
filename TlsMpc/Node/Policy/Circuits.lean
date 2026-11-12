/-!
# Which connection (Tor circuit) each contact is sent on (pure)

Moved unchanged (names kept) from the controller
(`handshake_backend/EmpHybridWork/PublicServiceController.lean`, which imports this module) in
REORGANIZATION_PLAN.md stage S2. No emitter imports this module.
-/

/-! ---- Several Tor circuits in one send session (PRODUCT_TODO.md section 8).

Assignment: the session's distinct contact ids in ascending order; the contact of rank r is sent
on connection r mod N. Public, and computed identically by both controllers. A contact keeps its
connection for the whole session (every broadcast in it), and the connections' contact counts
differ by at most one. It depends only on the set of ids, so a broadcast to the same set is split
the same way in every session: across sessions the server sees the same groups again (through
other exits), not new pairs that would eventually join everyone.

What the server can still link: the recipients on one connection (one TLS session, one circuit);
and by timing, the whole broadcast: the N connections are opened together, each with a full
handshake, and the sends alternate between them one response at a time, with no delay or
shuffling. Request ids count per connection (from 2^63, as on a single connection), so they do
not interleave across connections; ids of a device refresh's own requests are still one counter
for the session. The receive socket is a connection of its own, on its own circuit, but it is
authenticated and names the account. -/
namespace Circuits

def assign (contacts : List Nat) (count : Nat) (contact : Nat) : Nat :=
  let sorted := contacts.eraseDups.mergeSort (fun a b => decide (a ≤ b))
  ((sorted.findIdx? (· == contact)).getD 0) % max count 1

/-- SOCKS5 credentials of connection `index` (`none`: the receive socket). The username is fresh
per session (from its id), so Tor never reuses a circuit of another session for it; the password
names the connection and the count. Both are agreed between the parties with the connect request. -/
def labels (session : String) (count : Nat) (index : Option Nat) : String × String :=
  (s!"tls-mpc-{String.ofList (session.toList.take 16)}",
    match index with
    | some i => s!"send-{i}-of-{count}"
    | none => "receive")

end Circuits
