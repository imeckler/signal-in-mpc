#!/usr/bin/env python3
"""Authored standard-container bindings; never edits generated Funs/Types."""
import argparse,pathlib,re
parser=argparse.ArgumentParser();parser.add_argument('--folder',default='CurrentModelViewsV1');parser.add_argument('--namespace',default='CtrCurrentV1');args=parser.parse_args();assert args.folder.replace('_','').isalnum() and args.namespace.isidentifier()
HERE=pathlib.Path(__file__).resolve().parent;folder=HERE/'Generated'/args.folder;template=(folder/'FunsExternal_Template.lean').read_text();types=(folder/'Types.lean').read_text()
def one(pattern):
 values=re.findall(pattern,types,re.S);assert len(values)==1,(pattern,values);return values[0]
R=one(r'structure (core\.ops\.range\.Range\.specialized_Type_\w+)\s')
O=one(r'inductive (core\.option\.Option\.specialized_Type_\w+)\s')
seen=[]
def replace(match):
 name,signature=match.group(1),match.group(2);seen.append(name)
 if name.endswith('.CoreIterTraitsIteratorIterator.next'):
  body='''fun range => do
    let (choice,next) ← Aeneas.Std.core.iter.range.IteratorRange.next
      (Aeneas.Std.core.iter.range.UScalarStep .Usize Aeneas.Std.core.clone.CloneUsize Aeneas.Std.core.cmp.PartialOrdUsize)
      {start:=range.start, «end»:=range.end}
    pure ((match choice with | none => '''+O+'''.None | some value => '''+O+'''.Some value),
      {start:=next.start, «end»:=next.end})'''
 elif name.endswith('.CoreIterTraitsCollectIntoIterator.into_iter'):body='fun range => .ok range'
 elif name=='core.num.U32.to_ne_bytes':body='fun value => .ok (Aeneas.Std.core.num.U32.to_le_bytes value)'
 elif name=='SliceU32.Insts.CoreOpsIndexIndexUsize.index':body='fun value index => Aeneas.Std.Slice.index_usize value index'
 elif name.startswith('SliceU8.Insts.CoreOpsIndexIndexMut'):
  suffix='RangeFrom'if'RangeFrom'in signature else'RangeTo';field='start'if suffix=='RangeFrom'else'«end»'
  body=f'fun value range => Aeneas.Std.core.slice.index.SliceIndex{suffix}UsizeSlice.index_mut {{{field}:=range.{field}}} value'
 elif name.startswith('core.slice.SliceU8.copy_from_slice'):body='fun destination source => Aeneas.Std.core.slice.Slice.copy_from_slice Aeneas.Std.core.marker.CopyU8 destination source'
 elif '.as_mut_slice.'in name:body='fun value => .ok (Aeneas.Std.Array.to_slice_mut value)'
 elif '.as_slice.'in name:body='fun value => .ok (Aeneas.Std.Array.to_slice value)'
 elif name.endswith('.CoreDefaultDefault.default'):body='Aeneas.Std.core.default.DefaultArray.default 16#usize Aeneas.Std.core.default.DefaultU8'
 else:raise AssertionError(name)
 return 'def '+name+' : '+signature.strip()+' :=\n  '+body+'\n'
text=re.sub(r'axiom\s+([\w.]+)\s*:\s*(.*?)(?=\n/--|\Z)',replace,template,flags=re.S);assert len(seen)==10,len(seen);text=text.replace('open '+args.namespace,'namespace '+args.namespace)+'\nend '+args.namespace+'\n';text=text.replace('-- This is a template file: rename it to "FunsExternal.lean" and fill the holes.','-- Authored bindings: official Aeneas scalar/range/slice/array models.\n-- Hybrid raw-pointer views/default map to valid fixed-array contents; memory\n-- address/layout/Drop are outside this functional scope. Native endian is\n-- little-endian for the pinned aarch64 target; zero nonce is endian-independent.')
(folder/'FunsExternal.lean').write_text(text)
