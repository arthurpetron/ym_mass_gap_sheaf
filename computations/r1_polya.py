import sympy as sp
w,u=sp.symbols('w u')
def coeffW(p): return (p+1)*w**(p*(p+2))
def acNfull(t): return sp.expand(sum(coeffW(p)*coeffW(t-p) for p in range(t+1)))
def dmomNfull(t): return sp.expand(sum((t-2*p)**2*coeffW(p)*coeffW(t-p) for p in range(t+1)))
def slack(s):
    aS,a1,a2=acNfull(s),acNfull(s+1),acNfull(s+2)
    dS,d1,d2=dmomNfull(s),dmomNfull(s+1),dmomNfull(s+2)
    return sp.expand(dS*(a1*a2)+d2*(aS*a1)+2*(aS*(a1*a2)) - 2*(d1*(aS*a2)))

print("=== Polya positive-coeff form:  B_s(u/(1+u))*(1+u)^deg  in ZZ[u]  -> all coeffs >= 0? ===")
for s in range(0,11):
    S=slack(s); P=sp.Poly(S,w); k=min(m for (m,) in P.monoms())
    B=sp.Poly(sp.expand(S/w**k),w); d=B.degree()
    Pu=sp.Poly(sp.expand(B.as_expr().subs(w,u/(1+u))*(1+u)**d),u)
    cs=Pu.all_coeffs()
    allpos=all(c>=0 for c in cs); nneg=sum(1 for c in cs if c<0)
    print(f" s={s:>2} deg={d:>3}  Polya coeffs all>=0 = {allpos}  (#neg={nneg}, min={float(min(cs)):.4g})")

print("\n=== is slack_s already Polya-positive WITHOUT factoring w^k (i.e. slack_s(u/(1+u))*(1+u)^D)? ===")
for s in range(0,9):
    S=slack(s); D=sp.Poly(S,w).degree()
    Pu=sp.Poly(sp.expand(S.subs(w,u/(1+u))*(1+u)**D),u)
    cs=Pu.all_coeffs(); print(f" s={s:>2}  all>=0 = {all(c>=0 for c in cs)} (#neg={sum(1 for c in cs if c<0)})")

print("\n=== Bernstein coeff vectors beta_{s,i} (native), look for closed form ===")
def bern(B):
    d=B.degree(); a=[B.coeff_monomial(w**j) for j in range(d+1)]
    return [sum(sp.binomial(i,j)*a[j]/sp.binomial(d,j) for j in range(i+1)) for i in range(d+1)]
for s in range(0,5):
    S=slack(s); P=sp.Poly(S,w); k=min(m for (m,) in P.monoms()); B=sp.Poly(sp.expand(S/w**k),w)
    beta=[sp.nsimplify(b) for b in bern(B)]
    print(f" s={s}: beta = {[str(b) for b in beta]}")
