#!/usr/bin/env python3
"""Build the pinned, already-acquired dependency closure with all fetching disabled."""
import hashlib,json,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1];AREA=ROOT/'.deps/signal-tinier128';BACKEND=AREA/'MP-SPDZ';PREFIX=BACKEND/'local';LOGS=HERE/'build-logs'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    LOGS.mkdir(exist_ok=True);commands=[]
    common=['-DCMAKE_BUILD_TYPE=Release','-DCMAKE_CXX_COMPILER=clang++',f'-DCMAKE_INSTALL_PREFIX={PREFIX}',f'-DCMAKE_PREFIX_PATH={PREFIX};/opt/homebrew','-DCMAKE_INSTALL_LIBDIR=lib','-DBUILD_TESTING=OFF']
    projects=[('function2',AREA/'dependencies/function2',[]),('libdivide',AREA/'dependencies/libdivide',['-DLIBDIVIDE_BUILD_TESTS=OFF']),('macoro',AREA/'dependencies/macoro',['-DMACORO_CPP_VER=20','-DMACORO_PIC=ON','-DMACORO_TESTS=OFF',*['-DMACORO_FETCH_'+x+'=OFF'for x in ['AUTO','OPTIONAL','VARIANT']]]),('coproto',AREA/'dependencies/coproto',['-DCOPROTO_CPP_VER=20','-DCOPROTO_PIC=ON','-DCOPROTO_ENABLE_BOOST=OFF','-DCOPROTO_ENABLE_OPENSSL=OFF',*['-DCOPROTO_FETCH_'+x+'=OFF'for x in ['AUTO','MACORO','FUNCTION2','SPAN','BOOST']]]),('libOTe',BACKEND/'deps/libOTe2',['-DBUILD_SHARED_LIBS=OFF','-DLIBOTE_STD_VER=20','-DENABLE_SOFTSPOKEN_OT=ON','-DENABLE_SILENTOT=ON','-DENABLE_PORTABLE_AES=ON','-DENABLE_AVX=OFF','-DENABLE_SSE=OFF','-DENABLE_PIC=ON','-DENABLE_BITPOLYMUL=OFF',*['-DFETCH_'+x+'=OFF'for x in ['AUTO','COPROTO','BITPOLYMUL','SPAN_LITE','RELIC','SODIUM','BOOST','GMP','LIBDIVIDE']]])]
    for name,source,options in projects:
        assert (source/'CMakeLists.txt').exists(),source
        build=AREA/'dependency-build'/name
        if name=='libOTe':options += [f'-DLIBOTE_BUILD_DIR={build}',f'-DOC_THIRDPARTY_HINT={PREFIX}']
        for phase,command in [('configure',['cmake','-S',str(source),'-B',str(build),*common,*options]),('build',['cmake','--build',str(build),'-j2']),('install',['cmake','--install',str(build)])]:
            log=LOGS/f'{name}-{phase}.log';print(name,phase,flush=True)
            commands.append({'command':command,'log':str(log.relative_to(ROOT))})
            with log.open('w')as out:subprocess.run(command,stdout=out,stderr=subprocess.STDOUT,check=True)
    report={'candidate_only':True,'network_fetch_enabled':False,'commands':commands,'script_sha256':digest(Path(__file__)),'dependency_archive_manifest_sha256':digest(HERE/'dependency-archives.json'),'logs_sha256':{str(p.relative_to(ROOT)):digest(p)for p in LOGS.glob('*.log')},'installed_libraries':{str(p.relative_to(ROOT)):digest(p)for p in sorted((PREFIX/'lib').glob('*.a'))}}
    (HERE/'dependency-build.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
