#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess,sys
H=Path(__file__).resolve().parent;ROOT=H.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
profile=sys.argv[1] if len(sys.argv)>1 else 'dispatch'
if profile in ('dispatch','validation'):
 S=ROOT/'SignalReference/ProtoParseWork/MessageReferenceWork/FnItemCandidate';receiptfile=S/'build-report.json';receipt=json.loads(receiptfile.read_text());binary=ROOT/receipt['binary_path']
 assert sha(binary)==receipt['binary_sha256']
elif profile in ('status','status_mono'):
 S=H/'TranslatorCandidate';receiptfile=S/'build-report.json';receipt=json.loads(receiptfile.read_text());binary=S/'Bin/candidate';assert sha(binary)==receipt['binary_sha256']
else:
 receiptfile=ROOT/'SignalReference/pins.json';pins=json.loads(receiptfile.read_text());binary=(ROOT/'SignalReference'/pins['aeneas']['directory']/'aeneas').resolve()
 assert pins['aeneas']['release'] in subprocess.check_output([str(binary),'-version'],text=True)
source=H/'Artifacts'/profile/('metadata-lowered.llbc' if '--lowered' in sys.argv else 'chat.llbc');dest={'validation':'GeneratedValidation','dispatch':'Generated','string':'GeneratedString','uint64':'GeneratedUint64','status':'GeneratedStatus','status_mono':'GeneratedStatusMono','string_precise':'GeneratedStringPrecise','utf8':'GeneratedUtf8','metadata_positive':'GeneratedMetadataPositive','metadata_negative':'GeneratedMetadataNegative','string_drop':'GeneratedStringDrop'}[profile]
command=[str(binary),'-backend','lean',str(source),'-dest',str(ROOT/'SignalReference'),'-subdir','/ChatResponseReferenceWork/'+dest,'-namespace','ActualChatResponse'+profile.capitalize(),'-split-files','-warnings-as-errors','-no-progress-bar','-sequential']
for name in ['Funs.lean','Types.lean','TypesExternal_Template.lean','FunsExternal_Template.lean']:(H/dest/name).unlink(missing_ok=True)
with (H/(profile+'-translate.log')).open('w') as log:r=subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,timeout=180)
report={'candidate_only':True,'profile':profile,'exit_code':r.returncode,'binary_sha256':sha(binary),'llbc_sha256':sha(source),'manual_generated_body_edits':False,'slice_metadata_lowering':'--lowered' in sys.argv,'translator_candidate_unaccepted':profile in ('dispatch','validation','status','status_mono'),'translator_receipt_sha256':sha(receiptfile),'command':command,'generated_sha256':{p.name:sha(p) for p in (H/dest).glob('*.lean') if p.name not in ['FunsExternal.lean','TypesExternal.lean']}}
(H/(profile+'-translation.json')).write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'profile':profile,'exit_code':r.returncode}));sys.exit(r.returncode)
