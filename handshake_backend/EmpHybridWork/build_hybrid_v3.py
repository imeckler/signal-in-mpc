"""Build the mixed EMP/native-field fixtures against the validated-v3 EMP tree.

Same sources and native field objects as the earlier candidate builds; only the
EMP include tree changes. Outputs carry a -v3 suffix so earlier receipts stay
reproducible.
"""
import hashlib,json,pathlib,re,subprocess,sys,time
ROOT=pathlib.Path(__file__).resolve().parents[2];BASE=ROOT/'.deps/two-party-comparison';HERE=pathlib.Path(__file__).resolve().parent
EMP=BASE/'emp-ag2pc-validated-v3';INSTALL=BASE/'modern-install'
targets=INSTALL/'lib/cmake/emp-tool/emp-toolTargets.cmake'
match=re.search(r'INTERFACE_COMPILE_OPTIONS "([^"\n]+)"',targets.read_text())
if not match:raise ValueError('missing EMP compile options')
options=match[1].split(';')
if options!=['-Wno-ignored-attributes','-mcpu=native']:raise ValueError('unreviewed EMP compile options')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# Lean-exported circuits: pins header and directory (lower_word_circuits.py).
WORDS=ROOT/'.deps/emp-hybrid-word-v1'
WORD=['-I'+str(ROOT/'.deps/emp-hybrid-curve-v1'),'-I'+str(WORDS),'-DEMP_WORD_CIRCUIT_DIR="'+str(WORDS)+'"']
FIXTURES={'word-roundtrip':('word_roundtrip_fixture',[]),'curve':('curve_fixture',['-I'+str(ROOT/'.deps/emp-hybrid-curve-v1')]),'pool-conversion-v2':('pool_conversion_v2_fixture',[]),'curve-v2':('curve_fixture_v2',WORD),
    'curve-v2-64':('curve_fixture_v2',WORD+['-DEMP_WORD_BATCH=64']),
    'curve-v2-bits':('curve_fixture_v2',WORD+['-DEMP_SCALAR_BOOLEAN=1']),
    'curve-kdf':('curve_kdf_fixture',WORD),
    'curve-ratchet':('curve_kdf_fixture',WORD+['-DEMP_KDF_SIGNAL=1']),
    'dyn-run':('dyn_run_fixture',WORD),
    'tls-worker':('tls_worker_v3',WORD),
    # Explicit honest-but-curious builds (names end in -sh): same sources, the
    # semi-honest Boolean session and the semi-honest field engine object.
    'tls-worker-sh':('tls_worker_v3',WORD+['-DEMP_HYBRID_SEMI_HONEST=1']),
    'dyn-run-sh':('dyn_run_fixture',WORD+['-DEMP_HYBRID_SEMI_HONEST=1']),
    # Field engine with a supplied MAC key share and imported authenticated shares.
    'field-import':('field_import_fixture',[]),
    'field-import-sh':('field_import_fixture',['-DEMP_HYBRID_SEMI_HONEST=1'])}
# Generic Lean-circuit runner: one binary per pinned circuit profile, since
# the typed wire values need their widths at compile time.
for profile in sorted(WORDS.glob('*.json')):
    spec=json.loads(profile.read_text())
    if 'circuit_sha256' in spec:FIXTURES['run-'+profile.stem]=('lean_run_fixture',WORD+['-DEMP_RUN_INPUT_BITS=%d'%spec['input_bits'],'-DEMP_RUN_OUTPUT_BITS=%d'%spec['output_bits']])
names=sys.argv[1:] or list(FIXTURES);reports={}
field=json.loads((BASE/'field-build.json').read_text())
# Native field owner rebuilt with the 128 profile; same recorded command otherwise.
engine_obj=BASE/'field_engine-v3.o';engine_cmd=[str(engine_obj) if x==str(BASE/'field_engine.o') else str(BASE/'field_engine-v3.d') if x==str(BASE/'field_engine.d') else x for x in field['commands'][0]]
engine_cmd.insert(engine_cmd.index('-DEMP_HYBRID_TEST_FAULTS=1'),'-DEMP_HYBRID_NATIVE_SECURITY=128')
with open(BASE/'field-engine-v3-build.log','w') as log:subprocess.run(engine_cmd,stdout=log,stderr=subprocess.STDOUT,check=True)
sh_obj=BASE/'field_engine-sh.o'
if any(n.endswith('-sh') for n in names):
    sh_cmd=[str(sh_obj) if x==str(engine_obj) else str(BASE/'field_engine-sh.d') if x==str(BASE/'field_engine-v3.d') else x for x in engine_cmd]
    sh_cmd.insert(sh_cmd.index('-DEMP_HYBRID_TEST_FAULTS=1'),'-DEMP_HYBRID_SEMI_HONEST=1')
    with open(BASE/'field-engine-sh-build.log','w') as log:subprocess.run(sh_cmd,stdout=log,stderr=subprocess.STDOUT,check=True)
for name in names:
    stem,extra=FIXTURES[name];start=time.monotonic();commands=[]
    obj=BASE/(name+'-v3.o');dep=BASE/(name+'-v3.d');binary=BASE/(name+'-fixture-v3')
    with open(BASE/(name+'-v3-build.log'),'w') as log:
        command=['c++','-std=c++20','-O3','-DNDEBUG',*options,'-DEMP_CONTEXT_CHECKS=1','-DEMP_HYBRID_STATISTICAL=128',*extra,'-I'+str(EMP),'-I'+str(INSTALL/'include'),'-I/opt/homebrew/opt/openssl@3.5/include','-idirafter','/opt/homebrew/include','-MMD','-MF',str(dep),'-c',str(HERE/(stem+'.cpp')),'-o',str(obj)];commands.append(command);subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,check=True)
        command=field['commands'][-1]
        command=[str(binary) if x==str(BASE/'native-field-fixture') else str(obj) if x==str(BASE/'field_engine_fixture.o') else str(sh_obj if name.endswith('-sh') else engine_obj) if x==str(BASE/'field_engine.o') else x for x in command]
        command+=['-L'+str(INSTALL/'lib'),'-lemp-ot','-lemp-tool'];commands.append(command);subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,check=True)
    dependencies={}
    for item in dep.read_text().replace('\\\n',' ').split(':',1)[1].split():
        d=pathlib.Path(item)
        if d.is_file():dependencies[str(d)]=sha(d)
    reports[name]=dict(seconds=time.monotonic()-start,commands=commands,dependencies=dependencies,binary=str(binary),binary_sha256=sha(binary),source_sha256=sha(HERE/(stem+'.cpp')))
out=BASE/'hybrid-v3-build.json';prior=json.loads(out.read_text()) if out.exists() else {}
prior.update(reports);prior['emp_source']=json.loads((BASE/'validation-v3-build-source.json').read_text())['variants']['emp-ag2pc-validated-v3'];prior['field_build']=field;prior['field_engine_v3']=dict(command=engine_cmd,object_sha256=sha(engine_obj),source_sha256=sha(HERE/'field_engine.cpp'))
out.write_text(json.dumps(prior,indent=2)+'\n');print(json.dumps({k:round(v['seconds'],1) for k,v in reports.items()}))
