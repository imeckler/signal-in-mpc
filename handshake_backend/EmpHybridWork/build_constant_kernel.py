"""Candidate mixed executable: EMP and field implementation stay separate TUs."""
import hashlib,json,pathlib,re,subprocess,time
ROOT=pathlib.Path(__file__).resolve().parents[2];BASE=ROOT/'.deps/two-party-comparison';HERE=pathlib.Path(__file__).resolve().parent
MP=BASE/'data61-MP-SPDZ-113c4e4';EMP=BASE/'emp-ag2pc-a245ca0f67abaf2d48c711e3c050ce961e60ad29';INSTALL=BASE/'modern-install'
# Match the pinned imported CMake target's architecture options. Omitting
# these produced false honest c_gamma rejection against the compiled library.
targets=INSTALL/'lib/cmake/emp-tool/emp-toolTargets.cmake'
match=re.search(r'INTERFACE_COMPILE_OPTIONS "([^"\n]+)"',targets.read_text())
if not match:raise ValueError('missing EMP compile options')
options=match[1].split(';')
if options!=['-Wno-ignored-attributes','-mcpu=native']:raise ValueError('unreviewed EMP compile options')
start=time.monotonic();commands=[]
with open(BASE/'constant-kernel-build.log','w') as log:
    command=['c++','-std=c++20','-O3','-DNDEBUG',*options,'-DEMP_CONTEXT_CHECKS=1','-I'+str(EMP),'-I'+str(INSTALL/'include'),'-I/opt/homebrew/opt/openssl@3.5/include','-MMD','-MF',str(BASE/'constant_kernel_fixture.d'),'-c',str(HERE/'constant_kernel_fixture.cpp'),'-o',str(BASE/'constant_kernel_fixture.o')];commands.append(command);subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,check=True)
    field=json.loads((BASE/'field-build.json').read_text());command=field['commands'][-1]
    command=[str(BASE/'constant-kernel-fixture') if x==str(BASE/'native-field-fixture') else str(BASE/'constant_kernel_fixture.o') if x==str(BASE/'field_engine_fixture.o') else x for x in command]
    command+=['-L'+str(INSTALL/'lib'),'-lemp-ot','-lemp-tool'];commands.append(command);subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,check=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
dependencies={}
for item in (BASE/('constant_kernel_fixture.d')).read_text().replace('\\\n',' ').split(':',1)[1].split():
    dependency=pathlib.Path(item)
    if dependency.is_file():dependencies[str(dependency)]=sha(dependency)
report=dict(passed=True,seconds=time.monotonic()-start,commands=commands,dependencies=dependencies,field_build=field,binary_sha256=sha(BASE/'constant-kernel-fixture'),emp_build=json.loads((BASE/'modern-build.json').read_text()),source_sha256=sha(HERE/'constant_kernel_fixture.cpp'))
(BASE/'constant-kernel-build.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(passed=True,seconds=report['seconds'])))
