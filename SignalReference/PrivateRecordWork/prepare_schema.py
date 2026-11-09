#!/usr/bin/env python3
"""Generate public capacity constants, never inspect an account/secret record."""
import hashlib,json
from pathlib import Path
from check import record
HERE=Path(__file__).resolve().parent
# These are public supported-domain bounds. No fixture presence/value enters.
def nodes(schema):
 return [dict(tag=tag,kind=kind,capacity=arg if kind!='m' else None,children=nodes(arg)if kind=='m'else None)for tag,kind,arg,count in schema for _ in range(count)]
def size(ns):return sum(1+(size(n['children'])if n['kind']=='m'else 4 if n['kind']=='s'else 3+n['capacity'])for n in ns)
def emit(ns):
 chunks=[]
 for n in ns:
  tag=n['tag'];k=n['kind']
  if k=='m':s=f'.message {tag} (a.const 0) '+emit(n['children'])
  elif k=='s':s=f'.scalar {tag} (a.const 0) false (List.replicate 4 (a.const 0))'
  else:s=f'.bytes {tag} (a.const 0) '+('true'if k=='o'else'false')+f' (PrivateBuffer.zero a {n["capacity"]})'
  chunks.append(s)
 return '['+',\n'.join(chunks)+']'
def main():
 ns=nodes(record);descriptor=json.dumps(ns,sort_keys=True,separators=(',',':'));digest=hashlib.sha256(descriptor.encode()).hexdigest()
 source='import TlsMpc.Signal.PrivateRecordSnapshotV1\nnamespace TlsMpc.Signal.PrivateRecordSchemaV1\nopen PrivateRecordEncodingV1\n'
 source+=f'def byteCount : Nat := {size(ns)}\ndef digest : String := "{digest}"\n'
 source+='def schema (a : ByteAuth.Ops B) : List (Node B) :=\n'+emit(ns)+'\nend TlsMpc.Signal.PrivateRecordSchemaV1\n'
 target=HERE.parents[1]/'TlsMpc/Signal/PrivateRecordSchemaV1.lean';target.write_text(source)
 (HERE/'schema-report.json').write_text(json.dumps(dict(public_capacity_schema_only=True,no_live_record_inspected=True,byte_count=size(ns),descriptor_sha256=digest,generator_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),source_sha256=hashlib.sha256(source.encode()).hexdigest()),indent=2)+'\n')
 print(size(ns),digest)
if __name__=='__main__':main()
