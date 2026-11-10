RTT=0.030; T=27.78
backends=[("CCD 5/2 GF128 (current)",352,150e3),("Rep3 3/1 (stock, S40)",2.75,10e6),("Rep4 4/1 (est.)",0.5,15e6),
          ("Custom 5/2 small-field (est.)",8,3e6),("7-party t<n/3 (est.)",4,3e6)]
for cname,A,R in [("today",14e6,130e3),("after circuit fixes",5e6,25e3)]:
    print(f"\n=== {cname} — resources per party to sustain 27.8 msg/s at 30 ms RTT (each bound alone) ===")
    print(f"{'backend':32s} {'Gbps':>8s} {'cores':>7s} {'in-flight N':>12s} {'core-s/msg':>11s}")
    for name,bpa,aps in backends:
        gbps=A*bpa*T*8/1e9; cores=A/aps*T; N=R*RTT*T
        print(f"{name:32s} {gbps:8.1f} {cores:7.0f} {N:12.0f} {A/aps:11.2f}")
print("\nper-conversation serial floor at 30 ms RTT: chain step ~9.6k rounds today -> %.0f s/msg; ~1.8k rounds with prefix adders -> %.0f s/msg"%(9600*RTT,1800*RTT))
