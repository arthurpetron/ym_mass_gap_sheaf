import sympy as sp
w=sp.symbols('w')
def coeffW(p): return (p+1)*w**(p*(p+2))
def acNfull(t): return sp.expand(sum(coeffW(p)*coeffW(t-p) for p in range(t+1)))
def dmomNfull(t): return sp.expand(sum((t-2*p)**2*coeffW(p)*coeffW(t-p) for p in range(t+1)))
def slack(s):
    aS,a1,a2=acNfull(s),acNfull(s+1),acNfull(s+2)
    dS,d1,d2=dmomNfull(s),dmomNfull(s+1),dmomNfull(s+2)
    return sp.expand(dS*(a1*a2)+d2*(aS*a1)+2*(aS*(a1*a2)) - 2*(d1*(aS*a2)))

def bernstein_coeffs(Bpoly):
    d=Bpoly.degree(); a=[Bpoly.coeff_monomial(w**j) for j in range(d+1)]
    beta=[]
    for i in range(d+1):
        s=sp.Integer(0)
        for j in range(i+1):
            s+=sp.binomial(i,j)/sp.binomial(d,j)*a[j]
        beta.append(sp.nsimplify(s))
    return beta

print("=== Bernstein coeffs of B_s on [0,1]: all >= 0 (native degree, NO elevation)? ===")
for s in range(0,11):
    S=slack(s); P=sp.Poly(S,w); k=min(m for (m,) in P.monoms())
    B=sp.Poly(sp.expand(S/w**k),w)
    beta=bernstein_coeffs(B)
    nneg=all(b>=0 for b in beta)
    nbad=sum(1 for b in beta if b<0)
    minb=min(beta)
    print(f" s={s:>2} deg={B.degree():>3}  all_bernstein>=0 = {nneg}   (#neg={nbad}, min_beta={float(minb)})")
