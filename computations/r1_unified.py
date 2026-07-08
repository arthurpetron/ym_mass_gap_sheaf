import mpmath as mp
mp.mp.dps=40
def V(w,t):
    M=t+2; th=xi=ze=mp.mpf(0)
    for D in range(-t,t+1,2):
        wt=w**(mp.mpf(D*D)/2); th+=wt; xi+=D*D*wt; ze+=D**4*wt
    return (M*M*xi-ze)/(M*M*th-xi)
def sl(w,s): return V(w,s)-2*V(w,s+1)+V(w,s+2)+2
grid=[mp.mpf(i)/4000 for i in range(1,4000)]
print("=== inf over w of (Δ²V+2)/(w^2(1-w^2)) for ALL s (both parities) ===")
gmin=mp.inf; garg=None
for s in list(range(0,25))+[30,40,60,100,200]:
    r=mp.inf; am=None
    for g in grid:
        v=sl(g,s); f=g*g*(1-g*g)
        val=v/f
        if val<r: r=val; am=g
    if r<gmin: gmin=r; garg=(s,float(am))
    print(f" s={s:>3} ({'E' if s%2==0 else 'O'}): inf (Δ²V+2)/(w^2(1-w^2)) = {mp.nstr(r,7):>12} @w={float(am):.4f}")
print(f"\n GLOBAL inf over tested s,w = {mp.nstr(gmin,8)} at (s,w)={garg}")
print(" => candidate uniform lemma: Δ²V+2 >= 7*w^2*(1-w^2) for ALL s")
