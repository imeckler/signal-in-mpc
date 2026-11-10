"""Build opaque native-field TU against already pinned secure-OT candidate."""
import hashlib,json,pathlib,subprocess,time
ROOT=pathlib.Path(__file__).resolve().parents[2];BASE=ROOT/'.deps/two-party-comparison';MP=BASE/'data61-MP-SPDZ-113c4e4';HERE=pathlib.Path(__file__).resolve().parent
flags=['-std=c++20','-O3','-mcpu=native','-DNO_AVX_OT','-DUSE_GF2N_LONG','-DEMP_HYBRID_TEST_FAULTS=1',*['-I'+str(p) for p in [MP,MP/'deps',MP/'local/include',pathlib.Path('/opt/homebrew/include'),pathlib.Path('/opt/homebrew/opt/openssl@3.5/include')]],'-Wno-deprecated-literal-operator','-Wno-deprecated-declarations']
commands=[];start=time.monotonic()
with open(BASE/'field-engine-build.log','w') as log:
    for name in ['field_engine','field_engine_fixture']:
        command=['c++',*flags,'-MMD','-MF',str(BASE/(name+'.d')),'-c',str(HERE/(name+'.cpp')),'-o',str(BASE/(name+'.o'))];commands.append(command);subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,check=True)
    libs=[MP/'libSPDZ.so',*[MP/'OT'/x for x in ['BaseOT.o','BitDiagonal.o','MascotParams.o','OTExtension.o','OTExtensionWithMatrix.o','OTTripleSetup.o']],MP/'deps/SimplestOT_C/ref10/libSimplestOT.a',*[MP/'local/lib'/x for x in ['liblibOTe.a','libmacoro.a','libcryptoTools.a','libcoproto.a']]]
    command=['c++','-o',str(BASE/'native-field-fixture'),str(BASE/'field_engine.o'),str(BASE/'field_engine_fixture.o'),*map(str,libs),'-L/opt/homebrew/lib','-L/opt/homebrew/opt/openssl@3.5/lib','-lgmpxx','-lgmp','-lsodium','-lssl','-lcrypto','-lboost_filesystem','-lboost_iostreams','-Wl,-rpath,'+str(MP),'-pthread'];commands.append(command);subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,check=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
deps=set()
for name in ['field_engine','field_engine_fixture']:
    text=(BASE/(name+'.d')).read_text().replace('\\\n',' ')
    for item in text.split(':',1)[1].split():
        p=pathlib.Path(item)
        if p.is_file():deps.add(p.resolve())
report=dict(passed=True,seconds=time.monotonic()-start,commands=commands,binary_sha256=sha(BASE/'native-field-fixture'),sources={str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p):sha(p) for p in sorted(deps)},scope='Low-level native authenticated field owner build only; no EMP bridge/security composition evidence.')
(BASE/'field-build.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(passed=True,seconds=report['seconds'])))
