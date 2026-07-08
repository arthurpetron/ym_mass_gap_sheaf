import sympy as sp
w=sp.symbols('w')
def coeffW(p): return (p+1)*w**(p*(p+2))
def A(t): return sp.expand(sum(coeffW(p)*coeffW(t-p) for p in range(t+1)))
def N(t): return sp.expand(sum((t-2*p)**2*coeffW(p)*coeffW(t-p) for p in range(t+1)))
def slack(s):
    aS,a1,a2=A(s),A(s+1),A(s+2); dS,d1,d2=N(s),N(s+1),N(s+2)
    return sp.expand(dS*a1*a2 + d2*aS*a1 + 2*aS*a1*a2 - 2*d1*aS*a2)
def Bpoly(s):
    S=slack(s); P=sp.Poly(S,w); k=min(m for (m,) in P.monoms())
    return k, sp.Poly(sp.expand(S/w**k),w)

print("=== EVEN s: structure of B_s(w)-B_s(0). Is (B_s-B_s(0)) divisible by w^2? by (1-w)?  ===")
for s in range(2,11,2):
    k,B=Bpoly(s); b0=B.eval(0)
    G=sp.expand(B.as_expr()-b0)
    Pg=sp.Poly(G,w); kk=min(m for (m,) in Pg.monoms())
    # check value/deriv at endpoints
    val1=B.eval(1)
    print(f" s={s:>2}: B(0)={int(b0)}, lowest power in B-B(0) = w^{kk}, B(1)={int(val1)}, B(1)/B(0)={float(val1)/float(b0):.3f}")

print("\n=== EVEN s: Bernstein coeffs of (B_s - B_s(0))/w^2 on [0,1] all >=0?  (would prove even case) ===")
def bern(Bp):
    d=Bp.degree(); a=[Bp.coeff_monomial(w**j) for j in range(d+1)]
    return [sum(sp.binomial(i,j)*a[j]/sp.binomial(d,j) for j in range(i+1)) for i in range(d+1)]
for s in range(2,11,2):
    k,B=Bpoly(s); b0=B.eval(0)
    G=sp.expand(B.as_expr()-b0)
    Pg=sp.Poly(G,w); kk=min(m for (m,) in Pg.monoms())
    H=sp.Poly(sp.expand(G/w**kk),w)
    beta=bern(H)
    nneg=sum(1 for b in beta if b<0)
    print(f" s={s:>2}: (B-B(0))/w^{kk}: deg={H.degree()}, #neg Bernstein = {nneg}/{len(beta)}, H(0)={int(H.eval(0))}")
