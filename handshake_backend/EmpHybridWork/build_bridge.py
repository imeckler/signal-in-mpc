"""Candidate mixed executable: EMP and field implementation stay separate TUs."""
import hashlib,json,pathlib,subprocess,time
ROOT=pathlib.Path(__file__).resolve().parents[2];BASE=ROOT/'.deps/two-party-comparison';HERE=pathlib.Path(__file__).resolve().parent
MP=BASE/'data61-MP-SPDZ-113c4e4';EMP=BASE/'emp-ag2pc-a245ca0f67abaf2d48c711e3c050ce961e60ad29';INSTALL=BASE/'modern-install'
start=time.monotonic();commands=[]
with open(BASE/'bridge-build.log','w') as log:
    command=['c++','-std=c++20','-O2','-DEMP_CONTEXT_CHECKS=1','-I'+str(EMP),'-I'+str(INSTALL/'include'),'-I/opt/homebrew/opt/openssl@3.5/include','-MMD','-MF',str(BASE/'bridge_coin_fixture.d'),'-c',str(HERE/'bridge_coin_fixture.cpp'),'-o',str(BASE/'bridge_coin_fixture.o')];commands.append(command);subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,check=True)
    field=json.loads((BASE/'field-build.json').read_text());command=field['commands'][-1]
    command=[str(BASE/'bridge-coin-fixture') if x==str(BASE/'native-field-fixture') else str(BASE/'bridge_coin_fixture.o') if x==str(BASE/'field_engine_fixture.o') else x for x in command]
    command+=['-L'+str(INSTALL/'lib'),'-lemp-ot','-lemp-tool'];commands.append(command);subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,check=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
report=dict(passed=True,seconds=time.monotonic()-start,commands=commands,field_build=field,binary_sha256=sha(BASE/'bridge-coin-fixture'),emp_build=json.loads((BASE/'modern-build.json').read_text()),source_sha256=sha(HERE/'bridge_coin_fixture.cpp'))
(BASE/'bridge-build.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(passed=True,seconds=report['seconds'])))
