import sys, numpy as np
for d in sys.argv[1:]:
    rows=[l.split() for l in open(d+'/resources.log') if l[0].isdigit()]
    thr=[l.strip() for l in open(d+'/resources.log') if 'THROTTLE' in l]
    if not rows: print(d,'no samples'); continue
    a=np.array([[float(r[2]),float(r[4]),float(r[5]),float(r[8])] for r in rows])
    snap=open(d+'/prerun_snapshot.txt').read().splitlines()
    la=[l for l in snap if l.startswith('loadavg')][0]; mem=[l for l in snap if l.startswith('Mem:')][0].split()
    print(f"{d}: pre-run nproc=8, free -g total={mem[1]}G used={mem[2]}G free={mem[3]}G avail={mem[6]}G, {la.split()[0]} {la.split()[1]}; "
          f"samples={len(a)}: MemAvailable MB min/mean/max={a[:,0].min():.0f}/{a[:,0].mean():.0f}/{a[:,0].max():.0f} "
          f"({a[:,1].min():.1f}/{a[:,1].mean():.1f}/{a[:,1].max():.1f}%), load1 min/mean/max={a[:,2].min():.2f}/{a[:,2].mean():.2f}/{a[:,2].max():.2f}, job CPU% mean={a[:,3].mean():.0f}; throttle events={len(thr)}")
