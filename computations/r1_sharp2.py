import sympy as sp
w=sp.symbols('w')
def coeffW(p): return (p+1)*w**(p*(p+2))
def A(t): return sp.expand(sum(coeffW(p)*coeffW(t-p) for p in range(t+1)))
def N(t): return sp.expand(sum((t-2*p)**2*coeffW(p)*coeffW(t-p) for p in range(t+1)))
def Vex(t): return sp.cancel(N(t)/A(t))
def slex(s): return sp.cancel(Vex(s)-2*Vex(s+1)+Vex(s+2)+2)
for s in range(0,3):
    S=sp.cancel(slex(s)); print(f"s={s}: D2V+2 = {S}")
    ratio=sp.cancel(S/(w**2*(1-w**2)))
    dr=sp.numer(sp.together(sp.diff(ratio,w)))
    crit=[complex(r).real for r in sp.Poly(dr,w).nroots() if abs(complex(r).imag)<1e-9 and 0<complex(r).real<1]
    vv=[(float(ratio.subs(w,r)),r) for r in crit]
    if vv:
        m=min(vv); print(f"     min ratio={m[0]:.6f} @w={m[1]:.4f}  (144/25={144/25})")
