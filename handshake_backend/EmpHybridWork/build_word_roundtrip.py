"""Candidate mixed executable: EMP and field implementation stay separate TUs."""
import hashlib,json,pathlib,re,subprocess,time
ROOT=pathlib.Path(__file__).resolve().parents[2];BASE=ROOT/'.deps/two-party-comparison';HERE=pathlib.Path(__file__).resolve().parent
MP=BASE/'data61-MP-SPDZ-113c4e4';EMP=BASE/'emp-ag2pc-linear-mask-v1';INSTALL=BASE/'modern-install'
# Match the pinned imported CMake target's architecture options. Omitting
# these produced false honest c_gamma rejection against the compiled library.
targets=INSTALL/'lib/cmake/emp-tool/emp-toolTargets.cmake'
match=re.search(r'INTERFACE_COMPILE_OPTIONS "([^"\n]+)"',targets.read_text())
if not match:raise ValueError('missing EMP compile options')
options=match[1].split(';')
if options!=['-Wno-ignored-attributes','-mcpu=native']:raise ValueError('unreviewed EMP compile options')
start=time.monotonic();commands=[]
with open(BASE/'word-roundtrip-build.log','w') as log:
    command=['c++','-std=c++20','-O3','-DNDEBUG',*options,'-DEMP_CONTEXT_CHECKS=1','-I'+str(EMP),'-I'+str(INSTALL/'include'),'-I/opt/homebrew/opt/openssl@3.5/include','-MMD','-MF',str(BASE/'word_roundtrip_fixture.d'),'-c',str(HERE/'word_roundtrip_fixture.cpp'),'-o',str(BASE/'word_roundtrip_fixture.o')];commands.append(command);subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,check=True)
    field=json.loads((BASE/'field-build.json').read_text());command=field['commands'][-1]
    command=[str(BASE/'word-roundtrip-fixture') if x==str(BASE/'native-field-fixture') else str(BASE/'word_roundtrip_fixture.o') if x==str(BASE/'field_engine_fixture.o') else x for x in command]
    command+=['-L'+str(INSTALL/'lib'),'-lemp-ot','-lemp-tool'];commands.append(command);subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,check=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
dependencies={}
for item in (BASE/('word_roundtrip_fixture.d')).read_text().replace('\\\n',' ').split(':',1)[1].split():
    dependency=pathlib.Path(item)
    if dependency.is_file():dependencies[str(dependency)]=sha(dependency)
report=dict(passed=True,seconds=time.monotonic()-start,commands=commands,dependencies=dependencies,field_build=field,binary_sha256=sha(BASE/'word-roundtrip-fixture'),emp_build=json.loads((BASE/'modern-build.json').read_text()),source_sha256=sha(HERE/'word_roundtrip_fixture.cpp'),linear_mask_overlay=json.loads((BASE/'linear-mask-overlay.json').read_text()))
(BASE/'word-roundtrip-build.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(passed=True,seconds=report['seconds'])))
