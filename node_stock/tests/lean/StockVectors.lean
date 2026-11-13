import TlsMpc.Node.Stock.Use
import TlsMpc.Sha256

/-!
Test vectors for the Rust store (node_stock), computed by the Lean model itself
(TlsMpc/Node/Stock/Format.lean and Use.lean). Not part of the library; nothing imports it.

Regenerate (one Lean job, from the repository root):
    python3 .deps/lowering-scratch/x1_vectors.py
which runs `lake env lean --run node_stock/tests/lean/StockVectors.lean` and writes its output to
node_stock/tests/stock_vectors.txt. node_stock/src/vectors.rs reads that file.

Format (one item per line):
  sha256-abc HEX                      SHA-256("abc") as computed here
  shape HEX                           ShapeId.enc of the fixed shape
  header HEX                          encHeader of the fixed header
  item I HEX                          encItem of item I's head and a fixed sealed byte string
  aad I HEX                           itemAad of the fixed header and item I's head
  jrec STOCKID W HEX                  one journal record (watermark W) of the stock
  jparse STOCKID N FILEHEX ENTRIES    parse of the first N bytes of the journal file
  chain SEED I CHAIN KEY              chainAt and itemKey at I from SEED
  claim none|N HEX                    encClaim
  stockuse I HEX                      encStockUse of the fixed shape, index I, agreed hash
  schedule K / end                    a schedule of operations on one node (production barriers)
    op NAME ARGS | OUTCOME | NEXT     an operation, its outcome (first refusal, `handed J`, `cut`
                                      or `ok`) and the next index after it (`-`: unusable)
    handed J,J,...                    the indices handed to the engine, in order
    nodup yes|no                      whether that list has no repetition (T14: yes unless the
                                      schedule restores both the disk and boot memory)
Operations (Rust: node_stock/src/vectors.rs):
  create            Store::create                       (Lean newStock)
  put K             K x Store::put                      (extend K)
  take J            Store::take                         (start J; sync; decrypt; hand)
  cut J STEP KEEP   Store::take cut after STEP (0 appended, 1 synced, 2 key erased), then a crash
                    keeping KEEP unsynced journal bytes (start J; [sync; [decrypt;]] crash KEEP)
  skip J            Store::skip_to                      (skip J)
  crash KEEP        drop and reopen                     (crash KEEP)
  reboot KEEP       new BootMemory, reopen              (reboot KEEP)
  snapdisk / restoredisk I / snapboot / restoreboot I   copies of the files / of the boot memory
-/

open TlsMpc.Node.Engine
open TlsMpc.Node.Stock

namespace X1V

def digit (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'
def hexByte (b : UInt8) : String := String.ofList [digit (b.toNat / 16), digit (b.toNat % 16)]
def hex (bs : Bytes) : String := String.join (bs.map hexByte)

def sha256 (m : Bytes) : Bytes :=
  (TlsMpc.Sha256.hash TlsMpc.Sha256.concrete (m.map fun b => BitVec.ofNat 8 b.toNat)).map
    fun b => UInt8.ofNat b.toNat

def bytesFrom (start : Nat) (n : Nat) : Bytes := (List.range n).map fun i => UInt8.ofNat (start + i)

def shapeA : ShapeId := ⟨ascii "signal-seal-official", 3, ascii "official"⟩

def hdrA : Header := ⟨shapeA, bytesFrom 0 32, bytesFrom 100 32, bytesFrom 200 32, 40⟩

def headOf (i : Nat) : ItemHead := ⟨i, 40, bytesFrom (i * 3) 32⟩

def natsStr (l : List Nat) : String := ",".intercalate (l.map toString)

def formatLines : List String :=
  let stock := bytesFrom 50 32
  let entries := [0, 1, 5, 6, 2 ^ 40]
  let tag := journalTag sha256 stock
  let file := encAll tag entries
  [s!"sha256-abc {hex (sha256 (ascii "abc"))}",
   s!"shape {hex shapeA.enc}",
   s!"header {hex (encHeader hdrA)}"] ++
  ([0, 1, 7, 2 ^ 33].map fun i => s!"item {i} {hex (encItem (headOf i) (bytesFrom 9 56))}") ++
  ([0, 1, 7, 2 ^ 33].map fun i => s!"aad {i} {hex (itemAad hdrA (headOf i))}") ++
  ([0, 1, 255, 256, 2 ^ 40].map fun w => s!"jrec {hex stock} {w} {hex (encRec tag w)}") ++
  ([0, 1, 15, 16, 17, 31, 32, 33, 47, 48, 70, 79, 80, 81].map fun n =>
    match parse tag (file.take n) with
    | some es => s!"jparse {hex stock} {n} {hex file} {if es.isEmpty then "-" else natsStr es}"
    | none => s!"jparse {hex stock} {n} {hex file} corrupt") ++
  ([0, 1, 2, 10].map fun i =>
    let c := chainAt sha256 (bytesFrom 77 32) i
    s!"chain {hex (bytesFrom 77 32)} {i} {hex c} {hex (itemKey sha256 c)}") ++
  [s!"claim none {hex (encClaim none)}", s!"claim 0 {hex (encClaim (some 0))}",
   s!"claim 300 {hex (encClaim (some 300))}"] ++
  ([0, 5].map fun i => s!"stockuse {i} {hex (encStockUse ⟨shapeA, i, bytesFrom 1 32⟩)}")

/-! ## Schedules -/

inductive Op where
  | create
  | put (k : Nat)
  | take (j : Nat)
  | cut (j step keep : Nat)
  | skip (j : Nat)
  | crash (keep : Nat)
  | reboot (keep : Nat)
  | snapDisk
  | restoreDisk (i : Nat)
  | snapBoot
  | restoreBoot (i : Nat)

def Op.events : Op → List Ev
  | .create => [.newStock]
  | .put k => [.extend k]
  | .take j => [.start j, .sync, .decrypt, .hand]
  | .cut j 0 keep => [.start j, .crash keep]
  | .cut j 1 keep => [.start j, .sync, .crash keep]
  | .cut j _ keep => [.start j, .sync, .decrypt, .crash keep]
  | .skip j => [.skip j]
  | .crash keep => [.crash keep]
  | .reboot keep => [.reboot keep]
  | .snapDisk => [.snapDisk]
  | .restoreDisk i => [.restoreDisk i]
  | .snapBoot => [.snapBoot]
  | .restoreBoot i => [.restoreBoot i]

def Op.show : Op → String
  | .create => "create"
  | .put k => s!"put {k}"
  | .take j => s!"take {j}"
  | .cut j s k => s!"cut {j} {s} {k}"
  | .skip j => s!"skip {j}"
  | .crash k => s!"crash {k}"
  | .reboot k => s!"reboot {k}"
  | .snapDisk => "snapdisk"
  | .restoreDisk i => s!"restoredisk {i}"
  | .snapBoot => "snapboot"
  | .restoreBoot i => s!"restoreboot {i}"

def refusalStr : Refusal → String
  | .busy => "busy"
  | .unusable => "unusable"
  | .behind => "behind"
  | .absent => "absent"
  | .erased => "erased"
  | .nothing => "nothing"
  | .exhausted => "exhausted"

def runOuts (n : NodeState) : List Ev → NodeState × List Outcome
  | [] => (n, [])
  | e :: es =>
    let r := step production n e
    let rest := runOuts r.1 es
    (rest.1, r.2 :: rest.2)

def isRefused : Outcome → Bool
  | .refused _ => true
  | _ => false

def summary (op : Op) (outs : List Outcome) : String :=
  match outs.find? isRefused with
  | some (.refused r) => s!"refused {refusalStr r}"
  | _ =>
    match op with
    | .take _ =>
      match outs.getLast? with
      | some (.handed j) => s!"handed {j}"
      | _ => "error"
    | .cut .. => "cut"
    | _ => "ok"

def nextStr (n : NodeState) : String :=
  match n.usable with
  | some _ => toString (n.next production)
  | none => "-"

def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- A number below `m` and the next seed. -/
def pick (s m : Nat) : Nat × Nat :=
  let s' := lcg s
  ((s' / 65536) % m, s')

/-- Choose the next operation from the state. -/
def chooseOp (n : NodeState) (s : Nat) : Op × Nat :=
  let (r, s) := pick s 100
  let nx := n.next production
  let (d, s) := pick s 9
  -- an index near the next one: behind, at, a little ahead (a peer ahead), far ahead (a lying peer)
  let j := match d with
    | 0 => nx - 2 | 1 => nx - 1 | 2 => nx | 3 => nx | 4 => nx | 5 => nx + 1 | 6 => nx + 2
    | 7 => nx + 5 | _ => nx + 1000
  let (k, s) := pick s 21
  if r < 30 then (.take j, s)
  else if r < 42 then
    let (st, s) := pick s 3
    (.cut j st k, s)
  else if r < 50 then (.skip j, s)
  else if r < 57 then (.crash k, s)
  else if r < 60 then (.reboot k, s)
  else if r < 65 then (.create, s)
  else if r < 77 then
    let (m, s) := pick s 4
    (.put (m + 1), s)
  else if r < 82 then (.snapDisk, s)
  else if r < 88 then
    if n.diskSnaps.isEmpty then (.snapDisk, s)
    else let (i, s) := pick s n.diskSnaps.length; (.restoreDisk i, s)
  else if r < 93 then (.snapBoot, s)
  else
    if n.bootSnaps.isEmpty then (.snapBoot, s)
    else let (i, s) := pick s n.bootSnaps.length; (.restoreBoot i, s)

def opLine (op : Op) (n : NodeState) : NodeState × String :=
  let r := runOuts n op.events
  (r.1, s!"op {op.show} | {summary op r.2} | {nextStr r.1}")

def runOps (n : NodeState) : List Op → NodeState × List String
  | [] => (n, [])
  | op :: ops =>
    let r := opLine op n
    let rest := runOps r.1 ops
    (rest.1, r.2 :: rest.2)

def genOps (n : NodeState) (s : Nat) : Nat → List Op
  | 0 => []
  | fuel + 1 =>
    let (op, s) := chooseOp n s
    op :: genOps (runOuts n op.events).1 s fuel

def schedule (k : Nat) : List String :=
  let start := [Op.create, Op.put 4]
  let n0 := (runOps init start).1
  let ops := start ++ genOps n0 (k * 7919 + 13) (20 + k % 15)
  let r := runOps init ops
  let handed := r.1.handed.map (fun e => e.2.2)
  [s!"schedule {k}"] ++ r.2 ++
    [s!"handed {if handed.isEmpty then "-" else natsStr handed}",
     s!"nodup {if decide r.1.handed.Nodup then "yes" else "no"}", "end"]

/-- Hand-written schedules: the traces of Use.lean, and crashes at every step. -/
def fixed : List (List Op) :=
  [[.create, .put 2, .take 0, .crash 0, .take 0, .take 1],
   [.create, .put 2, .snapDisk, .take 0, .restoreDisk 0, .take 0, .take 1],
   [.create, .put 2, .snapBoot, .take 0, .restoreBoot 0, .take 0, .take 1],
   [.create, .put 2, .snapDisk, .snapBoot, .take 0, .restoreDisk 0, .restoreBoot 0, .take 0],
   [.create, .put 3, .take 0, .reboot 0, .take 1, .create, .put 1, .take 0],
   [.create, .put 3, .cut 0 0 0, .take 0, .take 1],
   [.create, .put 3, .cut 0 0 7, .take 0, .take 1],
   [.create, .put 3, .cut 0 0 16, .take 0, .take 1],
   [.create, .put 3, .cut 0 1 0, .take 0, .take 1],
   [.create, .put 3, .cut 0 2 0, .take 0, .take 1],
   [.create, .put 3, .skip 2, .take 1, .take 2, .skip 1],
   [.create, .put 2, .skip 50, .put 1, .take 50, .create, .put 1, .take 0]]

def fixedLines : List String :=
  ((List.range fixed.length).zip fixed).flatMap fun (k, ops) =>
    let r := runOps init ops
    let handed := r.1.handed.map (fun e => e.2.2)
    [s!"schedule f{k}"] ++ r.2 ++
      [s!"handed {if handed.isEmpty then "-" else natsStr handed}",
       s!"nodup {if decide r.1.handed.Nodup then "yes" else "no"}", "end"]

def allLines : List String :=
  formatLines ++ fixedLines ++ (List.range 300).flatMap schedule

end X1V

def main : IO Unit := do
  for l in X1V.allLines do
    IO.println l
