import sympy as sp, mpmath as mp
mp.mp.dps=40
w=sp.symbols('w')
def coeffW(p): return (p+1)*w**(p*(p+2))
def acN(t): return sp.expand(sum(coeffW(p)*coeffW(t-p) for p in range(t+1)))
def dm(t): return sp.expand(sum((t-2*p)**2*coeffW(p)*coeffW(t-p) for p in range(t+1)))
def V(t): return sp.cancel(dm(t)/acN(t))
def d2V2(s): return sp.cancel(V(s)-2*V(s+1)+V(s+2)+2)

# numeric min over w in (0,1) of an expr
def minw(expr):
    f=sp.lambdify(w,expr,'mpmath')
    grid=[mp.mpf(i)/2000 for i in range(1,2000)]
    vals=[(g,f(g)) for g in grid]
    gm,vm=min(vals,key=lambda t:t[1]); return float(vm),float(gm)

print("=== ODD s: min_w(Delta^2 V + 2)   [claim: >= 12/7 ~ 1.7143, min at s=1] ===")
for s in [1,3,5,7,9]:
    vm,gm=minw(d2V2(s)); print(f" s={s}: min_w(D2V+2)={vm:.5f} @w={gm:.3f}   (12/7={12/7:.5f})")

print("\n=== EVEN s: margin  (Delta^2V+2) - (144/25) w^2 (1-w^2)   [claim: >=0, tight only s=0] ===")
env=sp.Rational(144,25)*w**2*(1-w**2)
for s in [0,2,4,6,8]:
    m=sp.cancel(d2V2(s)-env); vm,gm=minw(m)
    print(f" s={s}: min_w[(D2V+2)-env]={vm:.6f} @w={gm:.3f}")

print("\n=== EVEN s: is V(even) BOUNDED so odd-centre term controlled? and V(odd)>=1 exactly? ===")
for t in [1,3,5]:
    # V(odd) >= 1 ? min over w
    vm,gm=minw(V(t)); print(f" V(odd t={t}) min_w={vm:.5f} (>=1?)")
for t in [0,2,4]:
    vm,gm=minw(sp.cancel(1-V(t))); print(f" 1 - V(even t={t}) min_w={vm:.5f}  (V(even)<=1 fails where negative)")

print("\n=== KEY: does the ENVELOPE inequality reduce to nonneg Bernstein/ Polya of a CLEANER poly? ===")
for s in [0,2]:
    m=sp.together(sp.cancel(d2V2(s)-env)); num,den=sp.fraction(m)
    Pn=sp.Poly(sp.expand(num),w); k=min(mm for (mm,) in Pn.monoms())
    B=sp.Poly(sp.expand(sp.expand(num)/w**k),w)
    nr=int(B.count_roots(0,1))
    print(f" even s={s}: envelope-margin numerator: w^{k}*B, deg B={B.degree()}, roots in(0,1)={nr}, B(0)={int(B.eval(0))}")
