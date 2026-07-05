import mpmath as mp
mp.mp.dps=35
def Vtr(w,t):
    M=t+2; th=xi=ze=mp.mpf(0)
    for D in range(-t,t+1,2):
        wt=w**(mp.mpf(D*D)/2); th+=wt;xi+=D*D*wt;ze+=D**4*wt
    return (M*M*xi-ze)/(M*M*th-xi)
def D2V2(w,s): return Vtr(w,s)-2*Vtr(w,s+1)+Vtr(w,s+2)+2
# For w in upper region, compute sup over s>=7 of deficit (12/5 - D2V2), and min D2V2
print("w      | min_{s=7..80} D2V2 | max deficit(12/5-D2V2) | worst s")
for wv in [mp.mpf(x) for x in ['0.5','0.6','0.7','0.75','0.8','0.85','0.9','0.95','0.99']]:
    best=mp.mpf('9'); dmax=-mp.mpf('9'); ws=None
    for s in range(7,81):
        v=D2V2(wv,s)
        if v<best: best=v; ws=s
        d=mp.mpf(12)/5-v
        if d>dmax: dmax=d
    print(f"{float(wv):.3f}  |  {mp.nstr(best,7):>10}  |  {mp.nstr(dmax,6):>10}  | s={ws}")
# Is min D2V2 over s>=7 monotone increasing in s near each w? and what's the global min over w in[1/2,1],s>=7?
print("\nGlobal min D2V2 over w in[1/2,1], s>=7 (fine):")
grid=[mp.mpf('0.5')+mp.mpf(i)/4000*mp.mpf('0.5') for i in range(4001)]
gm=mp.mpf('9');ga=None
for s in range(7,60):
    for g in grid:
        v=D2V2(g,s)
        if v<gm: gm=v;ga=(s,float(g))
print(f"  min = {mp.nstr(gm,7)} at (s,w)={ga}   (>0 with margin -> FullRangeFloor holds)")
