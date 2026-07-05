from fractions import Fraction as F
from math import comb
# Lean-matching poly ops on dict{exp:F}
def pmul(a,b):
    r={}
    for e1,c1 in a.items():
        for e2,c2 in b.items(): r[e1+e2]=r.get(e1+e2,F(0))+c1*c2
    return {e:c for e,c in r.items() if c!=0}
def padd(*ps):
    r={}
    for p in ps:
        for e,c in p.items(): r[e]=r.get(e,F(0))+c
    return {e:c for e,c in r.items() if c!=0}
def psc(k,a): return {e:F(k)*c for e,c in a.items() if F(k)*c!=0}
def c4(s): return s*(s+2)
def A(t): return padd(*[{c4(p)+c4(t-p):F((p+1)*(t-p+1))} for p in range(t+1)])
def Nm(t): return padd(*[{c4(p)+c4(t-p):F((t-2*p)**2*(p+1)*(t-p+1))} for p in range(t+1)])
def slackP(s):
    aS,a1,a2=A(s),A(s+1),A(s+2); dS,d1,d2=Nm(s),Nm(s+1),Nm(s+2)
    RHS=padd(pmul(dS,pmul(a1,a2)),pmul(d2,pmul(aS,a1)),psc(2,pmul(aS,pmul(a1,a2))))
    LHS=psc(2,pmul(d1,pmul(aS,a2)))
    return padd(RHS,psc(-1,LHS))
def envBoundPoly(s):
    return psc(F(144,25),pmul({2:F(1)},pmul({0:F(1),2:F(-1)},pmul(A(s),pmul(A(s+1),A(s+2))))))
# bernBasisSq (in x=w^2): (w^2)^i (1-w^2)^(n-i) as w-poly
def onemsq(): return {0:F(1),2:F(-1)}
def ppow(p,n):
    r={0:F(1)}
    for _ in range(n): r=pmul(r,p)
    return r
def shiftZ(k,p): return {e+k:c for e,c in p.items()}
def bernBasisSq(n,i): return shiftZ(2*i, ppow(onemsq(), n-i))
def bernTermsSq(n,terms): return padd(*[psc(c,bernBasisSq(n,i)) for (i,c) in terms])

def find_cert(s):
    G=padd(slackP(s), psc(-1,envBoundPoly(s)))
    k=min(G); B={e-k:c for e,c in G.items()}   # G = w^k * B, B poly in w
    assert all(e%2==0 for e in B), "B not even in w"
    Bx={e//2:c for e,c in B.items()}            # bracket in x=w^2
    d0=max(Bx)
    monoBx=[Bx.get(i,F(0)) for i in range(d0+1)]
    # elevate degree D until no-binomial Bernstein coeffs a_j>=0
    for D in range(d0, d0+40):
        # a_j = sum_i monoBx_dedegd... first get native no-binomial bern coeffs of Bx at degree d0,
        # then elevate. Actually directly: express Bx = sum_j a_j x^j (1-x)^(D-j).
        # Solve via: multiply Bx by (x+(1-x))^(D-d0)=1 and expand in Bernstein. 
        # no-binomial bern coeffs of a monomial-basis poly at degree D:
        # x^m = sum_{j>=m} C(D-m, j-m)/C(D,j) * C(D,j) ... use standard: 
        # We want a_j s.t. sum_j a_j x^j(1-x)^(D-j) = Bx. Match monomial coeffs.
        # coeff of x^p in RHS = sum_j a_j * C(D-j, p-j)*(-1)^(p-j) for j<=p.
        # Solve triangular for a_j.
        a=[F(0)]*(D+1)
        cx=[monoBx[i] if i<len(monoBx) else F(0) for i in range(D+1)]
        for j in range(D+1):
            s_=cx[j]
            for jj in range(j):
                s_-=a[jj]*F((-1)**(j-jj)*comb(D-jj, j-jj))
            a[j]=s_
        if all(c>=0 for c in a):
            terms=[(j,a[j]) for j in range(D+1) if a[j]!=0]
            # verify identity: G == shiftZ(k, bernTermsSq(D, terms))
            rec=shiftZ(k, bernTermsSq(D,terms))
            assert padd(G,psc(-1,rec))=={}, f"identity fail s={s}"
            return k,D,terms,(k+2*D)
    return None
for s in [1,2,3,4,5]:
    r=find_cert(s)
    if r:
        k,D,terms,totdeg=r
        print(f"s={s}: k={k}, bern-deg D={D} (in x=w^2), totalDeg(w)={totdeg}, #terms={len(terms)}, maxcoeff={max(c for _,c in terms)}")
    else:
        print(f"s={s}: NO cert up to elevation")

print("\n=== LEAN CERT DATA (s=1,2,3) ===")
for s in [1,2,3]:
    k,D,terms,td=find_cert(s)
    # emit as Lean list: [(i, Q'.mkPos num den ...)] but coeffs are k/25 -> rational. Represent each as (num,den)
    print(f"-- s={s}: k={k} D={D}")
    lean_terms=", ".join(f"({i}, {c.numerator}, {c.denominator})" for (i,c) in terms)
    print(f"   terms(i,num,den): [{lean_terms}]")
