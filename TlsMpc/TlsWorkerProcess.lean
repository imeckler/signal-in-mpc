import TlsMpc.TlsWorkerPipe

/-! Native worker process launcher. Every process retains its own native shares;
this Lean process receives only public RPC responses. The caller supplies public
TLS transport and certificate validation. Kill/wait is process cleanup, not a
claim of secure physical-memory erasure or mobile-adversary safety.
-/
namespace TlsMpc.TlsWorkerProcess
open TlsWire TlsClient TlsWorker

structure Config where
  executable : String
  workingDirectory : String
  party : Nat
  hostsFile : String
  port : Nat
  manifestFile : String
  sessionId : Bytes

def hex (bytes : Bytes) : String := String.ofList (bytes.flatMap fun byte =>
  let digits := "0123456789abcdef".toList.toArray
  [digits[byte.toNat / 16]!, digits[byte.toNat % 16]!])

structure Running where
  rpc : Rpc
  /-- Explicit process teardown; not an erasure receipt. -/
  stop : IO Unit

def spawn (cfg : Config)
    (authenticate : String → List Bytes → Nat → Bytes → Bytes → M Bool) : IO Running := do
  unless cfg.party < 5 && 1024 < cfg.port && cfg.port < 65530 && cfg.sessionId.length == 32 do
    throw (IO.userError "invalid native worker configuration")
  let child ← IO.Process.spawn {
    cmd := cfg.executable
    cwd := some cfg.workingDirectory
    args := #[toString cfg.party, cfg.hostsFile, toString cfg.port, cfg.manifestFile, hex cfg.sessionId]
    stdin := .piped, stdout := .piped, stderr := .inherit }
  let rpc ← TlsWorkerPipe.make (IO.FS.Stream.ofHandle child.stdout) (IO.FS.Stream.ofHandle child.stdin) authenticate
  return { rpc, stop := do
    try child.kill catch _ => pure ()
    let _ ← child.wait
    pure () }

end TlsMpc.TlsWorkerProcess
