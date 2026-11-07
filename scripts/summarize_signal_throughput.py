#!/usr/bin/env python3
"""Measured scalar CCD baseline and explicit bandwidth-only target arithmetic."""
import hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    source=ROOT/'benchmarks/results/lean-signal-native-checks.json';baseline=json.loads(source.read_text());assert baseline['complete']
    target=100000/3600;rows=[]
    pattern=r'Spent ([0-9.]+) seconds \(([0-9.]+) MB, (\d+) rounds, .*?\) on the online phase and ([0-9.]+) seconds \(([0-9.]+) MB, (\d+) rounds,'
    for case in baseline['cases']:
        if not case['category'].endswith('send'):continue
        assert case['all_outputs_match'] and case['exit_codes']==[0]*5
        party_times=[]
        for party,stats in enumerate(case['runtime_stats']):
            party_log=ROOT/case['logs']/f'party-{party}.log'
            assert digest(party_log)==stats['party_log_sha256']
            values=re.findall(r'^Time = ([0-9.eE+-]+) seconds',party_log.read_text(),re.M);assert len(values)==1
            party_times.append(float(values[0]))
        runtime=max(party_times)
        log=ROOT/case['logs']/'party-0.log';text=log.read_text();m=re.search(pattern,text);assert m
        online_s,online_mb,online_rounds,offline_s,offline_mb,offline_rounds=map(float,m.groups());batch=case['batch'];total_mb=float(case['runtime_stats'][0]['reported_data_sent_mb'][-1]);wall=case['wall_seconds_including_startup_and_live_preprocessing']
        rows.append({'name':case['name'],'batch':batch,'payload_bytes':17,'wall_seconds':wall,'runtime_online_seconds':online_s,'runtime_preprocessing_seconds':offline_s,'recipient_encryptions_per_hour_wall':batch/wall*3600,'runtime_reported_seconds_by_party':party_times,'runtime_max_reported_seconds':runtime,'recipient_encryptions_per_hour_reported_runtime':batch/runtime*3600,'total_sent_mb_per_party_per_recipient':total_mb/batch,'online_sent_mb_per_party_per_recipient':online_mb/batch,'preprocessing_sent_mb_per_party_per_recipient':offline_mb/batch,'online_runtime_communication_counter':int(online_rounds),'offline_runtime_communication_counter':int(offline_rounds),'target_required_outgoing_gbps_per_party_by_fanout':{str(f):target*f*total_mb/batch*8/1000 for f in(1,2,4,10)},'bandwidth_only_max_logical_messages_per_hour_fanout1':{f'{gbps}Gbps':gbps*1000/8/(total_mb/batch)*3600 for gbps in(1,10,100)},'party_log_sha256':digest(log)})
    realistic=ROOT/'benchmarks/results/lean-signal-steady-send-costs.json'
    result={'target_logical_messages_per_hour':100000,'target_logical_messages_per_second':target,'baseline_meets_target':False,'persistent_runtime_throughput_measured':False,'communication_mb_unit':'decimal MB (bytes/1e6)','protocol':'five-party malicious CCD GF128; scalar boolean adapter; live preprocessing','cases':rows,'realistic_payload_cost_report':str(realistic.relative_to(ROOT)),'source_sha256':{str(p.relative_to(ROOT)):digest(p)for p in[Path(__file__),source,realistic]},'interpretation':['Batch lanes encrypt independent recipient/session messages. Effective device fanout includes recipient devices and sender sync copies.','Wall includes process startup and bytecode loading; runtime rate uses maximum of all five reported Time values including runtime overhead. Online/preprocessing phases shown from party0. Persistent runtime throughput is unmeasured; amortizing startup cannot remove per-send traffic.','Current circuit already reuses prepared HMAC pads within chain derivation and HKDF expansion.','Bandwidth-only ceilings assume the named outgoing link bandwidth is entirely available for reported sent bytes. They are arithmetic bounds, not WAN measurements; RTT, contention, CPU, TLS/H2, and refresh reduce achievable rate.','VM rounds and runtime communication counters are not directly measured WAN roundtrips. No latency estimate multiplies those counters by RTT.','Measured baseline payload is only17B. Realistic256/1024B circuit costs are separate and have no native timing yet.','TLS session reuse amortizes handshake; TLSAESGCM, private H2 framing, ACK/control handling, new sessions, epoch rollover, refresh and erasure remain additional costs.','Tinier128 and packed scheduling are comparison candidates, with no measured speedup included.']}
    output=ROOT/'benchmarks/results/lean-signal-throughput-baseline.json';output.write_text(json.dumps(result,indent=2)+'\n')
    for r in rows:print(r['name'],r['batch'],round(r['recipient_encryptions_per_hour_wall'],1),round(r['target_required_outgoing_gbps_per_party_by_fanout']['1'],1))
if __name__=='__main__':main()
