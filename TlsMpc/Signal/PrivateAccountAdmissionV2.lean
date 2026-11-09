import TlsMpc.Signal.PrivateRecordAdmissionV1
namespace TlsMpc.Signal.PrivateAccountAdmissionV2
def slice (raw : List B) (offset count : Nat) := (raw.drop offset).take count
def all (a : ByteAuth.Ops B) (values : List B) := values.foldl a.and (a.const 255)
def oneOf (a : ByteAuth.Ops B) (value : B) (allowed : List Nat) :=
 allowed.foldl (fun old n => a.xor old (ByteAuth.eqMask a value (a.const n))) (a.const 0)
def canonicalPayload (a : ByteAuth.Ops B) (capacity : Nat) (raw : List B) :=
 let parsed := PrivateBuffer.fromWire a capacity raw
 a.and (ByteAuth.eqMask a parsed.valid (a.const 255)) (ByteAuth.equalMask a (PrivateBuffer.output a parsed) raw)

def globalBytes : Nat := 8306
def conversationBytes : Nat := 12579
def validate (n : Nat) (s : Sha256.Ops B W) (o : Word64.Ops B V) (a : ByteAuth.Ops B) (raw : List B) : List B :=
 let identity := slice raw 38 65
 let global := canonicalPayload a 8192 (slice raw 103 8195)
 let cursor := slice raw 8298 8
 let cursorValid := a.and (a.maskBit (OpenResult.get a cursor 0) 7)
   (a.not (ByteAuth.equalMask a cursor (List.replicate 8 (a.const 255))))
 let conversations := (List.range n).map fun index =>
   let base := globalBytes+index*conversationBytes
   let binding := slice raw base 69
   let record := slice raw (base+69) 5550
   let service := slice raw (base+5619) 611
   let selected := slice raw (base+6230) 525
   let intent := slice raw (base+6755) 612
   let queue := slice raw (base+7367) 5208
   let dispositions := slice raw (base+12575) 4
   let intentPresent := OpenResult.get a intent 0
   let intentValid := a.xor (a.and (ByteAuth.eqMask a intentPresent (a.const 0))
       (ByteAuth.equalMask a (intent.drop 1) (List.replicate 611 (a.const 0))))
     (ByteAuth.eqMask a intentPresent (a.const 255))
   let outboxes := (List.range 4).map fun slot =>
     let entry := slice queue (slot*1302) 1302
     let present := OpenResult.get a entry 0
     let disposition := OpenResult.get a dispositions slot
     let absent := all a [ByteAuth.eqMask a present (a.const 0),ByteAuth.eqMask a disposition (a.const 0),
       ByteAuth.equalMask a (entry.drop 1) (List.replicate 1301 (a.const 0))]
     let active := all a [ByteAuth.eqMask a present (a.const 255),oneOf a disposition [1,2,3,4,5],
       canonicalPayload a 1290 (slice entry 1 1293)]
     a.xor absent active
   all a [OpenResult.get a (PrivateRecordAdmissionV1.validate s o a (record++selected++service)) 0,
     ByteAuth.equalMask a (slice identity 0 32) (slice service 0 32),
     ByteAuth.equalMask a (slice identity 33 32) (slice service 410 32),
     ByteAuth.eqMask a (OpenResult.get a identity 32) (a.const 5),
     ByteAuth.equalMask a (slice binding 0 16) (slice service 554 16),
     ByteAuth.equalMask a (slice binding 16 4) (slice service 603 4),
     ByteAuth.eqMask a (OpenResult.get a service 602) (a.const 1),
     ByteAuth.eqMask a (OpenResult.get a binding 20) (a.const 5),
     ByteAuth.equalMask a (slice binding 21 32) (slice service 442 32),
     ByteAuth.equalMask a (slice binding 53 16) (slice service 570 16),intentValid,all a outboxes]
 [if 1<=n ∧ n<=4 ∧ raw.length=globalBytes+n*conversationBytes then all a (global::cursorValid::conversations) else a.const 0]
end TlsMpc.Signal.PrivateAccountAdmissionV2
