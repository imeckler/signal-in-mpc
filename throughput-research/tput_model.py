# Throughput model: msg/s = 1 / (R*RTT/N + bytes/B + cpu_s/cores)
# R = sequential rounds per message, N = messages in flight (lanes x instances),
# B = link bytes/s per party, cpu_s = core-seconds per message.
RTT=0.030
B10=1.25e9; B1=0.125e9
CORES=32
# backend: (name, bytes_per_AND, ANDs_per_core_second, rounds_scale, note)
backends=[
 ("CCD 5/2 GF128 (current)",      352,   150e3, 1.0),
 ("Rep3 3/1 (stock, S40)",        2.75,  10e6,  1.0),
 ("Rep4 4/1 (stock, est.)",       0.5,   15e6,  1.0),
 ("Custom 5/2 small-field (est.)",8,     3e6,   1.0),
 ("7-party t<n/3 (est.)",         4,     3e6,   1.0),
 ("BMR 5/2 constant-round",       5140,  20e3,  0.0),  # ~constant rounds
]
circuits=[("today",14e6,130e3),("after circuit fixes",5e6,25e3)]
def tput(bpa,aps,rs,A,R,N,B,cores):
    rounds=R*rs if rs>0 else 30
    return 1/(rounds*RTT/N + A*bpa/B + A/aps/cores)
def need_N(bpa,aps,rs,A,R,B,cores,target=27.78):
    rounds=R*rs if rs>0 else 30
    rest=A*bpa/B + A/aps/cores
    if rest>=1/target: return None
    return rounds*RTT/(1/target-rest)
for cname,A,R in circuits:
    print(f"\n=== {cname}: {A/1e6:.0f}M ANDs, {R/1e3:.0f}k rounds; 30 ms RTT, 10 Gbps/party, 32 cores/party ===")
    print(f"{'backend':32s} {'MB/msg':>8s} {'lat min':>8s} {'N=1k':>7s} {'N=4k':>7s} {'N=32k':>7s} {'N=inf':>7s} {'N for 27.8/s':>13s} {'1Gbps,N=inf':>12s}")
    for name,bpa,aps,rs in backends:
        rounds=R*rs if rs>0 else 30
        lat=rounds*RTT/60
        row=[tput(bpa,aps,rs,A,R,N,B10,CORES) for N in (1024,4096,32768,1e12)]
        n=need_N(bpa,aps,rs,A,R,B10,CORES)
        t1=tput(bpa,aps,rs,A,R,1e12,B1,CORES)
        print(f"{name:32s} {A*bpa/1e6:8.1f} {lat:8.1f} "+" ".join(f"{x:7.2f}" for x in row)+f" {('%.0f'%n) if n else 'unreachable':>13s} {t1:12.2f}")
