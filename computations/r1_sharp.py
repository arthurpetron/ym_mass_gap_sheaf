import sympy as sp, mpmath as mp
w=sp.symbols('w')
# exact small cases
def coeffW(p): return (p+1)*w**(p*(p+2))
def A(t): return sp.expand(sum(coeffW(p)*coeffW(t-p) for p in range(t+1)))
def N(t): return sp.expand(sum((t-2*p)**2*coeffW(p)*coeffW(t-p) for p in range(t+1)))
def Vex(t): return sp.cancel(N(t)/A(t))
def slex(s): return sp.cancel(Vex(s)-2*Vex(s+1)+Vex(s+2)+2)
print("=== EXACT Δ²V(s)+2 and min of ratio /(w^2(1-w^2)) for small s ===")
for s in range(0,4):
    S=sp.cancel(slex(s)); print(f" s={s}: Δ²V+2 = {S}")
    ratio=sp.cancel(S/(w**2*(1-w**2)))
    # minimize ratio on (0,1)
    dr=sp.together(sp.diff(ratio,w)); numr=sp.numer(dr)
    crit=[r for r in sp.nroots(sp.Poly(numr,w)) if r.is_real and 0<r<1]
    vals=[(sp.nsimplify(ratio.subs(w,r)),complex(r).real) for r in crit]
    if vals:
        mv=min(vals,key=lambda t:float(t[0]))
        print(f"      min ratio = {float(mv[0]):.6f} = {sp.nsimplify(mv[0])} @ w={mv[1]:.4f}")
print(f"\n  144/25 = {144/25}")

# high-precision uniform check
mp.mp.dps=40
def V(w,t):
    M=t+2; th=xi=ze=mp.mpf(0)
    for D in range(-t,t+1,2):
        wt=w**(mp.mpf(D*D)/2); th+=wt; xi+=D*D*wt; ze+=D**4*wt
    return (M*M*xi-ze)/(M*M*th-xi)
def sl(w,s): return V(w,s)-2*V(w,s+1)+V(w,s+2)+2
print("\n=== verify inf_w (Δ²V+2)/(w^2(1-w^2)) >= 144/25 for all s (fine grid) ===")
gmin=mp.inf
for s in list(range(0,30))+[50,100,300]:
    r=min(sl(mp.mpf(i)/8000,s)/((mp.mpf(i)/8000)**2*(1-(mp.mpf(i)/8000)**2)) for i in range(1,8000))
    gmin=min(gmin,r)
    if s<6 or s in (300,):
        print(f" s={s:>3}: inf ratio = {mp.nstr(r,8)}")
print(f" GLOBAL inf ratio over all tested s = {mp.nstr(gmin,10)}   (144/25={mp.nstr(mp.mpf(144)/25,10)})")
print(f" holds >= 144/25 : {gmin>=mp.mpf(144)/25 - mp.mpf('1e-6')}")
