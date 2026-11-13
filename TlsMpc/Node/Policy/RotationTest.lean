import TlsMpc.Node.Policy.Rotation

/-!
# X2's property test: rotation plans for many counts, configurations and seeds

New file; pure (no I/O). Nothing imports it yet (no emitter may). `checks ()` returns named
results like `ReceiveTest.checks`; every entry is `true` when the plans behave as the theorems of
`Policy/Rotation.lean` say. Run it by evaluating `RotationTest.failures ()` (expected `[]`) from
any Lean file that imports this module; `stats ()` reports the connection counts and cost figures
quoted in ROTATION.md.

For every configuration in `configs`, every count in `counts` and several seeds (SHA-256, the
deployed hash), the plan is checked for:
* acceptance by the executor model (`accepts`), and the state after every action: at most
  `poolSize` connections open;
* the order is a permutation of `0 … n-1`, the sends follow it (each position once);
* the generations are `base, base+1, …`;
* every connection carried between 1 and `maxLen` messages, the counts sum to `n`, one per
  generation, and `k ≤ n ≤ k·maxLen`;
* the order's draws (`decode`) are valid and `encode` gives the order back;
* T15: two different input lists of the same length give the same erased actions and the same
  carriers as the skeleton, and the sends are the inputs in the shuffled order;
* `drive` yields the actions;
* the hold window on generated arrival times: `arrival ≤ planned ≤ arrival + hold`, identity for
  `hold = 0`.
-/

namespace RotationTest

open Rotation

def seedOf (i : Nat) : Bytes := TlsMpc.TlsWire.uint 32 (i * 2654435761 + 12345)

def configs : List Config :=
  [ {},
    { mean := 1, poolSize := 1 },
    { mean := 2, poolSize := 3 },
    { mean := 3, poolSize := 16 },
    { mean := 10, poolSize := 1 },
    { mean := 10, poolSize := 4, length := .geometric 40 },
    { mean := 5, poolSize := 2, length := .geometric 5 },
    { mean := 1, poolSize := 4, length := .geometric 1 } ]

def counts : List Nat := [0, 1, 2, 3, 4, 7, 10, 19, 20, 48, 100]

/-- The monitor's states after each action; `none` when one is refused. -/
def scan (maxLen : Nat) : Mon → List (Action Nat) → List Mon → Option (List Mon)
  | _, [], acc => some acc.reverse
  | m, a :: as, acc =>
    match m.step maxLen a with
    | some m' => scan maxLen m' as (m' :: acc)
    | none => none

def validB : Nat → List Nat → Bool
  | 0, [] => true
  | k + 1, d :: ds => d < k + 1 && validB k ds
  | _, _ => false

/-- The names of the properties a plan fails. -/
def checkPlan (H : Bytes → Bytes) (seed : Bytes) (n : Nat) (cfg : Config) (base : Nat) : List String :=
  let p := plan H seed n cfg base
  let acts := p.actions
  let opens := opensOf acts
  let k := opens.length
  let final := Mon.run cfg.maxLen (Mon.init cfg.poolSize base) acts
  let countsOk := match final with
    | some m => m.closed.sum == n && m.closed.all (fun c => 1 ≤ c && c ≤ cfg.maxLen) &&
        m.closed.length == k && m.sends == n
    | none => false
  let prefixOk := match scan cfg.maxLen (Mon.init cfg.poolSize base) acts [] with
    | some ms => ms.all (fun m => openCount m.slots ≤ cfg.poolSize)
    | none => false
  let draws := decode (List.range n) p.order
  let xs := (List.range n).map (fun i => i * 7919 + 13)
  let ys := (List.range n).reverse.map (fun i => 2 ^ 100 + i)
  let cx := compose H seed cfg base xs 0
  let cy := compose H seed cfg base ys 1
  let sk := skeleton H seed n cfg base
  let results : List (String × Bool) :=
    [ ("accepted by the executor model", accepts cfg base acts),
      ("at most poolSize open after every action", prefixOk),
      ("order is a permutation of the positions", p.order.mergeSort (fun a b => decide (a ≤ b)) == List.range n),
      ("sends follow the order", sendsOf acts == p.order),
      ("generations base, base+1, ...", opens == List.range' base k),
      ("counts in [1, maxLen], sum n, one per generation", countsOk),
      ("k <= n <= k * maxLen", k ≤ n && n ≤ k * cfg.maxLen),
      ("decode gives valid draws", validB n draws),
      ("encode (decode order) = order", encode (List.range n) draws == p.order),
      ("plan = skeleton relabelled", acts == sk.map (Action.map (fun i => p.order.getD i 0))),
      ("T15: erased actions independent of the inputs", cx.map Action.erase == cy.map Action.erase),
      ("T15: carriers are the skeleton's", carriers cfg.poolSize cx == carriers cfg.poolSize sk &&
        carriers cfg.poolSize cy == carriers cfg.poolSize sk),
      ("T15: the i-th send is input order[i]", sendsOf cx == p.order.map (fun q => xs.getD q 0)),
      ("drive yields the actions", drive acts.length (PlanState.ofPlan p) == acts) ]
  results.filterMap fun (name, ok) =>
    if ok then none else some s!"{name} (n={n}, mean={cfg.mean}, pool={cfg.poolSize}, base={base})"

/-- Every configuration, count and seed. -/
def planFailures (seeds : Nat) : List String := Id.run do
  let mut out : List String := []
  for cfg in configs do
    for n in counts do
      for i in [0:seeds] do
        out := out ++ checkPlan sha256 (seedOf (i + 1000 * n)) n cfg (7 * i)
  return out

/-! ### The hold window -/

def lcg (x : Nat) : Nat := (x * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- `count` arrival times (ms), increments of 0..2000 ms, sometimes equal; from `seed`. -/
def arrivals (seed count : Nat) : List Nat := Id.run do
  let mut x := seed
  let mut t := 0
  let mut out : List Nat := []
  for _ in [0:count] do
    x := lcg x
    t := t + (x / 2 ^ 33) % 2001 * ((x / 2 ^ 20) % 2)
    out := out ++ [t]
  return out

def holdOk (seeds : Nat) : Bool := Id.run do
  let mut ok := true
  for i in [0:seeds] do
    let ts := arrivals (i + 1) 40
    for hold in [0, 1, 250, 1000, 5000] do
      let ps := plannedAt hold none ts
      ok := ok && ps.length == ts.length && (ts.zip ps).all (fun (t, d) => t ≤ d && d ≤ t + hold)
    ok := ok && plannedAt 0 none ts == ts
  return ok

/-! ### Uniformity sanity check: the 6 permutations of 3 positions over many seeds -/

def permCounts (samples : Nat) : List (List Nat × Nat) := Id.run do
  let perms : List (List Nat) := [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]
  let mut c : List Nat := [0, 0, 0, 0, 0, 0]
  for i in [0:samples] do
    let o := (plan sha256 (seedOf (i + 77)) 3 {} 0).order
    match perms.findIdx? (· == o) with
    | some j => c := c.set j (c.getD j 0 + 1)
    | none => pure ()
  return perms.zip c

/-! ### The checks -/

set_option compiler.extract_closed false in
def checks (_ : Unit) : List (String × Bool) :=
  let failed := planFailures 3
  let pc := permCounts 600
  [ ("every plan property, all configurations, counts and seeds", failed.isEmpty),
    ("hold window: arrival <= planned <= arrival + hold; identity at 0", holdOk 20),
    ("all 6 permutations of 3 occur, each 60..140 times in 600", pc.all (fun (_, k) => 60 ≤ k && k ≤ 140)),
    ("invalid configuration refused (pool 0)", !({ poolSize := 0 } : Config).valid),
    ("invalid configuration refused (mean 0)", !({ mean := 0 } : Config).valid),
    ("default configuration valid", ({} : Config).valid) ]

def failures (_ : Unit) : List String := (checks ()).filterMap fun (name, ok) => if ok then none else some name

/-- The first failing plan properties, for diagnosis. -/
def failedPlans (_ : Unit) : List String := (planFailures 3).take 10

/-! ### Statistics (ROTATION.md, cost) -/

/-- Over `samples` seeds: (total connections, min, max) for `n` messages. -/
def connectionStats (n samples : Nat) (cfg : Config) : Nat × Nat × Nat := Id.run do
  let mut total := 0
  let mut lo := n + 1
  let mut hi := 0
  for i in [0:samples] do
    let k := (opensOf (plan sha256 (seedOf (i + 5000)) n cfg 0).actions).length
    total := total + k
    lo := min lo k
    hi := max hi k
  return (total, lo, hi)

/-- The sizes of all connections (closed counts) for `n` messages, one seed. -/
def sizes (n : Nat) (cfg : Config) (seed : Nat) : List Nat :=
  match Mon.run cfg.maxLen (Mon.init cfg.poolSize 0) (plan sha256 (seedOf seed) n cfg 0).actions with
  | some m => m.closed
  | none => []

end RotationTest
