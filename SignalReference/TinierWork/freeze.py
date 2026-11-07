#!/usr/bin/env python3
"""Freeze isolated candidate build receipts after a local, non-network type check."""
import hashlib,json,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1];BACKEND=ROOT/'.deps/signal-tinier128/MP-SPDZ'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    prep=json.loads((HERE/'preparation.json').read_text())
    for name,sha in prep['source_sha256'].items():assert digest(BACKEND/name)==sha,name
    assert digest(BACKEND/'CONFIG.mine')==prep['config_candidate_sha256']
    probe=subprocess.run([str(BACKEND/'signal-tinier-type-probe')],cwd=BACKEND,capture_output=True,text=True,check=True)
    assert probe.stdout.strip()=='Tinier bit value; GF128 MAC; statistical default 128'
    help=subprocess.run([str(BACKEND/'tinier-party.x'),'--help'],cwd=BACKEND,capture_output=True,text=True)
    assert 'Statistical security parameter (default: 128)'in help.stdout+help.stderr
    inputs=[HERE/x for x in ['prepare.py','build_dependencies.py','dependency-archives.json','dependency-build.json','preparation.json','type_probe.cpp','Probe.mk','REVIEW.txt']]+[Path(__file__),ROOT/'scripts/check_lean_signal_tinier128.py']
    binaries=[BACKEND/'tinier-party.x',BACKEND/'libSPDZ.so',BACKEND/'signal-tinier-type-probe',BACKEND/'deps/SimplestOT_C/ref10/libSimplestOT.a',*sorted((BACKEND/'local/lib').glob('*.a'))]
    report={'candidate_only':True,'native_comparison_executed':False,'build_complete':True,'source_unchanged':True,'five_parties_two_malicious_target':True,'protocol':'Tinier malicious dishonest-majority, binary values with GF128 MACs','statistical_security_parameter':128,'consistent_macros':['LONG_BIT_MAC_KEY','DEFAULT_SECURITY=128'],'local_type_probe':probe.stdout.strip(),'input_sha256':{str(p.relative_to(ROOT)):digest(p)for p in inputs},'binary_sha256':{str(p.relative_to(ROOT)):digest(p)for p in binaries},'build_log_sha256':digest(Path('/tmp/signal-tinier-build.log')),'root_native_command':'python3 scripts/check_lean_signal_tinier128.py --timeout 900 --port 19400','writes':'Only isolated .deps/signal-tinier128/MP-SPDZ runtime/Programs/Player-Data, separate benchmarks/results/raw/signal-tinier128, and lean-signal-tinier128-checks.json. Existing CCD fixtures/artifacts/bytecode read-only.','unclaimed':['production backend migration','StrongShamir/Tinier conversions','mobile refresh','VM erasure','WAN throughput','persistent runtime throughput']}
    (HERE/'build-report.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
