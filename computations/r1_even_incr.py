import sympy as sp
w=sp.symbols('w')
def coeffW(p): return (p+1)*w**(p*(p+2))
def acNfull(t): return sp.expand(sum(coeffW(p)*coeffW(t-p) for p in range(t+1)))
def dmomNfull(t): return sp.expand(sum((t-2*p)**2*coeffW(p)*coeffW(t-p) for p in range(t+1)))
def slack(s):
    aS,a1,a2=acNfull(s),acNfull(s+1),acNfull(s+2)
    dS,d1,d2=dmomNfull(s),dmomNfull(s+1),dmomNfull(s+2)
    return sp.expand(dS*(a1*a2)+d2*(aS*a1)+2*(aS*(a1*a2)) - 2*(d1*(aS*a2)))
def Bpoly(s):
    S=slack(s); P=sp.Poly(S,w); k=min(m for (m,) in P.monoms())
    return k, sp.Poly(sp.expand(S/w**k),w)

print("=== EVEN s: does B_s(w) - B_s(0) have ALL nonneg coeffs? ===")
for s in range(0,15,2):
    k,B=Bpoly(s)
    b0=B.eval(0); d=B.degree()
    if d==0:
        print(f" s={s:>2}: B constant = {int(b0)} (trivially >=0)"); continue
    coeffs=[B.coeff_monomial(w**j) for j in range(d+1)]
    coeffs[0]=coeffs[0]-b0
    allnn=all(c>=0 for c in coeffs)
    nneg=sum(1 for c in coeffs if c<0)
    print(f" s={s:>2}: B-B(0) all coeffs>=0 = {allnn}  (#neg={nneg}, deg={d}, B(0)={int(b0)})")

print("\n=== ODD s: raw coeffs of B_s (support & signs) ===")
for s in range(1,10,2):
    k,B=Bpoly(s)
    d=B.degree()
    coeffs=[int(B.coeff_monomial(w**j)) for j in range(d+1)]
    supp=[(j,coeffs[j]) for j in range(len(coeffs)) if coeffs[j]!=0]
    signs=''.join('+' if c>0 else '-' for _,c in supp)
    print(f" s={s:>2}: deg={d}, #nz={len(supp)}, signs={signs}")
    print(f"        first: {supp[:5]}")
    print(f"        last:  {supp[-4:]}")
