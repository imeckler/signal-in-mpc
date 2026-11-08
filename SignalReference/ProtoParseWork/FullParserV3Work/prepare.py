#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parent;S=H.parent/'SkipTranslatorWork';T=H.parent/'TopFieldWork/Modules/TopFieldWork'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
modules=[]
def write(path,content):
 if not path.exists() or path.read_text()!=content:path.write_text(content)
names=['BufModel','SliceReference','SliceBridge','SliceAdapter','SlowReference','StateBridge','WrapperReference','ArtifactBridge','Consumption']
items=[('Skip.Replayed.'+n,S/'Modules/SkipTranslatorWork/Replayed'/(n+'.lean')) for n in names]
items += [('Skip.'+n,S/'Modules/SkipTranslatorWork'/(n+'.lean')) for n in ['KeyValue','KeyReference','SkipLeaf','SkipGroup','SkipSemantics']]
for module,src in items:
 before=src.read_text();after=before.replace('SkipTranslatorWork.Generated.skip','ProtoParseWork.DispatcherIntegrationWork.SkipReplay')
 for n in names:after=after.replace('SkipTranslatorWork.Replayed.'+n,'ProtoParseWork.FullParserV3Work.Skip.Replayed.'+n)
 for n in ['KeyValue','KeyReference','SkipLeaf','SkipGroup','SkipSemantics']:after=after.replace('SkipTranslatorWork.'+n,'ProtoParseWork.FullParserV3Work.Skip.'+n)
 target=H/Path(*module.split('.')).with_suffix('.lean');target.parent.mkdir(parents=True,exist_ok=True);write(target,after)
 modules.append({'module':module,'original':str(src),'original_sha256':sha(src),'replayed_sha256':sha(target),'changes':'Import substitutions only, recompiled under v2.'})
# Table lookup/absolute decoder proofs do not depend on the old plan/applyPlan.
# Replace their broad transitive import by only the unchanged numeric equality lemma.
source=H.parent/'SkipPlanWork/Modules/SkipPlanWork/KeyCircuit.lean'
write(H/'KeyCircuit.lean',source.read_text().replace('import SkipTranslatorWork.KeyReference','import ProtoParseWork.FullParserV3Work.Skip.KeyReference'))
modules.append({'module':'KeyCircuit','original':str(source),'original_sha256':sha(source),'replayed_sha256':sha(H/'KeyCircuit.lean'),'changes':'Import substitution only; unchanged key checks.'})
for name in ['Table','DecoderTable']:
 src=T/(name+'.lean');before=src.read_text();after=before.replace('import TopFieldWork.TopPlan','import ProtoParseWork.FullParserV3Work.KeyCircuit').replace('import TopFieldWork.Scan','import ProtoParseWork.FullParserV3Work.Table')
 write(H/(name+'.lean'),after)
 modules.append({'module':name,'original':str(src),'original_sha256':sha(src),'replayed_sha256':sha(H/(name+'.lean')),'changes':'Narrowed imports; no theorem/body change.'})

# Revalidate unchanged scalar/group plan lemmas against v2. The one affected
# initialization proof receives the explicit new zero-enable identity.
for name in ['Fixed','Group','Stack','Reference','GroupReference']:
 src=H.parent/'SkipPlanWork/Modules/SkipPlanWork'/(name+'.lean')
 before=src.read_text();after=before
 for dep in ['KeyCircuit','Fixed','Group','Stack']:
  after=after.replace('import SkipPlanWork.'+dep,'import ProtoParseWork.FullParserV3Work.'+('KeyCircuit' if dep=='KeyCircuit' else 'Numeric.'+dep))
 for dep in ['SkipLeaf','SkipGroup']:
  after=after.replace('import SkipTranslatorWork.'+dep,'import ProtoParseWork.FullParserV3Work.Skip.'+dep)
 if name=='Group':
  after=after.replace('import ProtoParseWork.FullParserV3Work.Numeric.Fixed','import ProtoParseWork.FullParserV3Work.Numeric.Fixed\nimport ProtoParseWork.FullParserV3Work.SuccessScan')
  after=after.replace('ht,hz,write_fields_zero]','ht,hz,write_fields_zero,ParserErrorStateV2.initialize_zero]')
 target=H/'Numeric'/(name+'.lean');target.parent.mkdir(parents=True,exist_ok=True);write(target,after)
 modules.append({'module':'Numeric.'+name,'original':str(src),'original_sha256':sha(src),'replayed_sha256':sha(target),'changes':'Import substitutions; Group adds v2 disabled initialization identity.'})

(H/'replay.json').write_text(json.dumps(modules,indent=2)+'\n')
