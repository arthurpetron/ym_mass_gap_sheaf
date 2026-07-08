import sympy as sp
w=sp.symbols('w')
def coeffW(p): return (p+1)*w**(p*(p+2))
def acNfull(t): return sp.expand(sum(coeffW(p)*coeffW(t-p) for p in range(t+1)))
def dmomNfull(t): return sp.expand(sum((t-2*p)**2*coeffW(p)*coeffW(t-p) for p in range(t+1)))
def slack(s):
    aS,a1,a2=acNfull(s),acNfull(s+1),acNfull(s+2)
    dS,d1,d2=dmomNfull(s),dmomNfull(s+1),dmomNfull(s+2)
    return sp.expand(dS*(a1*a2)+d2*(aS*a1)+2*(aS*(a1*a2)) - 2*(d1*(aS*a2)))
def bern(B):
    d=B.degree(); a=[B.coeff_monomial(w**j) for j in range(d+1)]
    return [sp.nsimplify(sum(sp.binomial(i,j)*a[j]/sp.binomial(d,j) for j in range(i+1))) for i in range(d+1)]

# How SPARSE is B_s? (which w-powers actually appear) and the raw integer coeffs
print("=== raw B_s coefficients (low->high), and support gaps ===")
for s in range(0,6):
    S=slack(s); P=sp.Poly(S,w); k=min(m for (m,) in P.monoms()); B=sp.Poly(sp.expand(S/w**k),w)
    d=B.degree(); raw=[int(B.coeff_monomial(w**j)) for j in range(d+1)]
    supp=[j for j in range(d+1) if raw[j]!=0]
    print(f" s={s}: k={k} deg={d} support(w-powers)={supp}")
    print(f"        nz coeffs = {[raw[j] for j in supp]}")

print("\n=== leading Bernstein coeff beta_0 = B_s(0) closed form vs derived ===")
# beta_0 = a_0 = B(0); check against parity formula
for s in range(0,11):
    S=slack(s); P=sp.Poly(S,w); k=min(m for (m,) in P.monoms()); B=sp.Poly(sp.expand(S/w**k),w)
    print(f" s={s:>2} ({'even' if s%2==0 else 'odd'}): beta_0=B(0)={int(B.eval(0))}, beta_top=B_lead={int(B.LC())}")
