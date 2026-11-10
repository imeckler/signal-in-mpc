"""Isolated zero-AND carry-mask correction; frozen vendor source stays untouched."""
import difflib,hashlib,json,pathlib,tarfile
ROOT=pathlib.Path(__file__).resolve().parents[2];BASE=ROOT/'.deps/two-party-comparison';HERE=pathlib.Path(__file__).resolve().parent
receipt=json.loads((BASE/'modern-build.json').read_text());archive=BASE/'emp-ag2pc-modern.tar.gz';sha=lambda b:hashlib.sha256(b).hexdigest()
if sha(archive.read_bytes())!=receipt['pins']['emp-ag2pc'][1]:raise ValueError('archive pin')
source=BASE/('emp-ag2pc-'+receipt['pins']['emp-ag2pc'][0]);target=BASE/'emp-ag2pc-linear-mask-v1';target.mkdir(exist_ok=True)
files={};before=None;after=None
with tarfile.open(archive) as t:
 for m in t:
  parts=pathlib.PurePosixPath(m.name).parts[1:]
  if not m.isfile() or not parts or parts[0]!='emp-ag2pc':continue
  data=t.extractfile(m).read();relative=pathlib.Path(*parts);key='/'.join(parts[1:])
  if key in receipt['compatibility_namespace_qualification']:
   data=(source/relative).read_bytes()
   if sha(data)!=receipt['compatibility_namespace_qualification'][key]['overlay_sha256']:raise ValueError('namespace overlay drift')
  if key=='backend/engine.h':
   before=data.decode();old='''      AG2PCGammaCheckPass pp(st);
      ag2pc_detail::run_pass(pp, source);
'''
   if before.count(old)!=1:raise ValueError('engine patch boundary')
   after=before.replace(old,'').replace('''      char D2[Hash::DIGEST_SIZE];''','''    }
    // Gamma pass also propagates masked-bit Lambda through XOR/NOT. A
    // zero-AND chunk still needs that state for subsequent nonlinear calls.
    AG2PCGammaCheckPass pp(st);
    ag2pc_detail::run_pass(pp, source);
    if (st.num_ands > 0) {
      char D2[Hash::DIGEST_SIZE];''',1)
   data=after.encode()
  dest=target/relative;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data);files[str(relative)]=sha(data)
if before is None:raise ValueError('missing engine')
(HERE/'linear-mask.patch').write_text(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/emp-ag2pc/backend/engine.h',tofile='b/emp-ag2pc/backend/engine.h')))
report=dict(source_revision=receipt['pins']['emp-ag2pc'][0],archive_sha256=sha(archive.read_bytes()),original_engine_sha256=sha(before.encode()),candidate_engine_sha256=sha(after.encode()),target=str(target),files=files,scope='Always propagate garbler masks after zero-AND chunks. Nonlinear c_gamma digest, Lambda receipt and COT checks remain unchanged. Unvalidated candidate until native regression.')
(BASE/'linear-mask-overlay.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(target=str(target),engine=report['candidate_engine_sha256'])))
