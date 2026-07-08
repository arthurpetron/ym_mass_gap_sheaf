import sympy as sp, mpmath as mp
mp.mp.dps=50
w = sp.symbols('w', positive=True)
def coeffW(p): return (p+1)*w**(p*(p+2))
def acNfull(t): return sp.expand(sum(coeffW(p)*coeffW(t-p) for p in range(t+1)))
def dmomNfull(t): return sp.expand(sum((t-2*p)**2*coeffW(p)*coeffW(t-p) for p in range(t+1)))
def slack(s):
    aS,a1,a2=acNfull(s),acNfull(s+1),acNfull(s+2)
    dS,d1,d2=dmomNfull(s),dmomNfull(s+1),dmomNfull(s+2)
    return sp.expand(dS*(a1*a2)+d2*(aS*a1)+2*(aS*(a1*a2)) - 2*(d1*(aS*a2)))

print(f"{'s':>2} {'k':>4} {'degB':>5} {'B(0)':>10} {'B(1)':>14} {'min_B(0,1)':>16} {'@w':>7} {'#roots(0,1)':>11}")
for s in range(0,15):
    S=slack(s); P=sp.Poly(S,w)
    k=min(m for (m,) in P.monoms())
    Bexpr=sp.expand(S/w**k); B=sp.Poly(Bexpr,w)
    b0=int(B.eval(0)); b1=int(B.eval(1))
    f=sp.lambdify(w,Bexpr,'mpmath')
    # fine golden-ish scan + refine
    grid=[mp.mpf(i)/4000 for i in range(1,4001)]
    gmin=min(grid,key=lambda g:f(g)); vmin=f(gmin)
    nr=int(B.count_roots(0,1))
    print(f"{s:>2} {k:>4} {B.degree():>5} {b0:>10} {b1:>14} {mp.nstr(vmin,6):>16} {float(gmin):>7.3f} {nr:>11}")

print("\n=== does normalized min_B/B(0) stay bounded below as s grows? (uniformity signal) ===")
for s in range(0,15):
    S=slack(s); P=sp.Poly(S,w); k=min(m for (m,) in P.monoms())
    Bexpr=sp.expand(S/w**k); B=sp.Poly(Bexpr,w); b0=mp.mpf(int(B.eval(0)))
    f=sp.lambdify(w,Bexpr,'mpmath')
    grid=[mp.mpf(i)/4000 for i in range(1,4001)]
    vmin=min(f(g) for g in grid)
    print(f" s={s:>2} parity={'even' if s%2==0 else 'odd '}  min_B/B(0) = {mp.nstr(vmin/b0,6)}")
