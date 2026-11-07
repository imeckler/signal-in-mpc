import ProtoParseWork.KeyReferenceWork.Replayed.SliceBridge
import ProtoParseWork.KeyReferenceWork.Replayed.BufModel

/-! The frozen exact slice proof is replayed against the full wrapper's
unchanged generated slice body. See slice-proof-replay.json. Importing both
original generated Types modules directly fails because their discriminant
attributes create identically named global instances. No computational
source or generated definition is patched by this proof-only replay. -/
