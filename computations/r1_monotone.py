import mpmath as mp
mp.mp.dps=45
def V(w,t):
    M=t+2; th=xi=ze=mp.mpf(0)
    for D in range(-t,t+1,2):
        wt=w**(mp.mpf(D*D)/2); th+=wt; xi+=D*D*wt; ze+=D**4*wt
    return (M*M*xi-ze)/(M*M*th-xi)
def sl(w,s): return V(w,s)-2*V(w,s+1)+V(w,s+2)+2
grid=[mp.mpf(i)/2000 for i in range(1,2000)]

print("=== POINTWISE monotone in s? min_w [ (Δ²V(s+2)+2) - (Δ²V(s)+2) ]  (>=0 means monotone up) ===")
for s in range(0,22):
    mn=mp.inf; am=None
    for g in grid:
        d=sl(g,s+2)-sl(g,s)
        if d<mn: mn=d; am=g
    flag="MONO-UP" if mn>=0 else "NOT-mono (dips)"
    print(f" s={s:>2}->{s+2}: min_w[Δ²V(s+2)-Δ²V(s)] = {mp.nstr(mn,6):>12} @w={float(am):.3f}   {flag}")
