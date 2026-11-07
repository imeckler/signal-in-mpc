#!/usr/bin/env python3
"""Five native malicious-CCD128 parties on public Signal fixtures; no production secrets."""
import argparse,hashlib,json,os,re,subprocess,sys,time
from datetime import datetime,timezone
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from scripts.check_lean_signal_ratchet_step import digest
from test_support.circuit import input_tokens

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--timeout',type=float,default=900);ap.add_argument('--port',type=int,default=19400);ap.add_argument('--send-only',action='store_true');args=ap.parse_args()
    backend=ROOT/'.deps/MP-SPDZ';executable=ROOT/'.deps/signal-native/signal-ccd128'
    profiles=[] if args.send_only else [('receiver-store','signal-receiver-store-lookup-5-2',1),('keccak','signal-keccak-sha3-512-64-64',1)]
    profiles += [(category,name,batch) for category,name in [('chain-send','signal-chain-send-17-5-5-2-present'),('spqr-send','signal-spqr-send-17-5-2-10-5-3-present-present')] for batch in (1,16)]
    results=[];output=ROOT/'benchmarks/results/raw/signal-native';output.mkdir(parents=True,exist_ok=True)
    for category,name,batch in profiles:
        artifact=ROOT/f'.deps/signal-{category}-artifacts/{name}.json';fixture=artifact.with_name(name+'-fixtures.json');rows=json.loads(fixture.read_text())
        if category.endswith('send'):rows=[row for row in rows if bytes.fromhex(row['output'])[0]==255]
        assert rows,(name,'no valid fixtures')
        inputs=[bytes.fromhex(rows[i%len(rows)]['input']) for i in range(batch)];outputs=[bytes.fromhex(rows[i%len(rows)]['output']) for i in range(batch)]
        expected=[int.from_bytes(value[offset:offset+8],'big') for offset in range(0,len(outputs[0]),8) for value in outputs]
        program=f'lean_artifact-{name}-{batch}-5';bytecode=backend/f'Programs/Bytecode/{program}-0.bc';assert bytecode.exists(),program
        run=output/program;run.mkdir(exist_ok=True);prefix=run/'Input'
        for party,tokens in enumerate(input_tokens({'raw':inputs})):(run/f'Input-P{party}-0').write_text('\n'.join(map(str,tokens))+'\n')
        logs=[];processes=[];started=time.monotonic();commands=[]
        try:
            for party in range(5):
                command=[str(executable),'-N','5','-T','2','-S','128','-pn',str(args.port),'-h','127.0.0.1','-IF',str(prefix),'-v',str(party),program]
                commands.append(command);log=(run/f'party-{party}.log').open('wb');logs.append(log)
                processes.append(subprocess.Popen(command,cwd=backend,stdout=log,stderr=subprocess.STDOUT))
            deadline=started+args.timeout
            for process in processes:process.wait(timeout=max(1,deadline-time.monotonic()))
            elapsed=time.monotonic()-started
            for log in logs:log.flush()
            codes=[p.returncode for p in processes]
            if codes!=[0]*5:raise RuntimeError((program,codes,[p.read_text()[-2000:] for p in sorted(run.glob('party-*.log'))]))
            text=(run/'party-0.log').read_text()
            values=[int(v,16) for v in re.findall(r'Reg\[\d+\]\s*=\s*0x([0-9a-fA-F]+)',text)]
            if values!=expected:raise AssertionError((program,'native output mismatch',len(values),len(expected),text[-1200:]))
            stats=[]
            for path in sorted(run.glob('party-*.log')):
                text=path.read_text();stats.append({'party_log_sha256':digest(path),'reported_data_sent_mb':re.findall(r'Data sent = ([0-9.eE+-]+) MB',text),'reported_global_data_sent_mb':re.findall(r'Global data sent = ([0-9.eE+-]+) MB',text),'reported_rounds':re.findall(r'(\d+) rounds',text)})
            row={'category':category,'name':name,'batch':batch,'wall_seconds_including_startup_and_live_preprocessing':elapsed,'recipient_encryptions_per_second':batch/elapsed,'all_outputs_match':True,'output_words_checked':len(values),'artifact_sha256':digest(artifact),'fixture_sha256':digest(fixture),'bytecode_sha256':digest(bytecode),'logs':str(run.relative_to(ROOT)),'runtime_stats':stats,'exit_codes':codes};results.append(row);print(json.dumps(row),flush=True)
        finally:
            for process in processes:
                if process.poll() is None:process.kill()
            for process in processes:
                try:process.wait(timeout=10)
                except subprocess.TimeoutExpired:pass
            for log in logs:log.close()
        report={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'complete':len(results)==len(profiles),'native_mpc_executed':True,'parties':5,'threshold':2,'binary_field_degree':128,'statistical_security_parameter':128,'executable_sha256':digest(executable),'source_sha256':{str(p.relative_to(ROOT)):digest(p) for p in [Path(__file__),ROOT/'SignalReference/NativeWork/ccd128.cpp',ROOT/'SignalReference/NativeWork/Makefile',ROOT/'handshake_backend/LongFieldBit.h',ROOT/'programs/lean_artifact.mpc',backend/'Machines/malicious-ccd-party.cpp']},'cases':results,'workload':'public synthetic independent established sessions; batch lanes are distinct recipient encryptions, not sequential messages on one ratchet','tls_h2_included':False,'persistent_session_runtime_tested':False,'refresh_or_vm_erasure_tested':False,'wan_tested':False,'target_logical_messages_per_hour':100000,'target_logical_messages_per_second':100000/3600,'device_fanout_multiplier_not_included':True,'vm_rounds_are_not_network_roundtrips':True}
        (ROOT/'benchmarks/results/lean-signal-native-checks.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
