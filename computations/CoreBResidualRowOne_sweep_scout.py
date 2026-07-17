#!/usr/bin/env python3
"""Exact scout of the Core-B shifted-row residual R(1,r) = boundaryResidualAt w h 1 r.

Faithful replica of lean/YMGap/Continuum/CoreBStructuralRecurrence.lean:
  coeffW w p        = (p+1) * w^(p*(p+2))          [dimQ * qpow w (c4 p)]
  acN w n s         = sum_{p<n} coeffW w p * coeffW w (s-p)   (Nat sub, truncated)
  modeWindow w s k  = acN w (s+1) (s+k)
  boundaryTerm w s k= coeffW w (s+1) * coeffW w k
  aComponentAt i    : [W(r+1)W(r+3), W(r+1)E(r+2), E(r)W(r+3), E(r)E(r+2)]
  mComponentAt j    : [W(r+2)^2, 2 W(r+2)E(r+1), E(r+1)^2]
  det(Aw,Ah,Mw,Mh)  = Aw*Mh - Mw*Ah
  R(s,r)            = sum over (i,j) != (0,0) of det(aAt(w,s,r,i), aAt(h,s,r,i),
                                                    mAt(w,s,r,j), mAt(h,s,r,j))
Goal: R(1,r) >= 0 on the physical simplex 0 <= h <= w, 4w <= 1.
Move 2 of the protocol: falsify before proving.
"""
import sympy as sp
from fractions import Fraction
from itertools import product

w, h = sp.symbols('w h', nonnegative=True)

def coeffW(x, p):
    return (p + 1) * x**(p * (p + 2))

def acN(x, n, s):
    return sum(coeffW(x, p) * coeffW(x, max(s - p, 0)) for p in range(n))

def W(x, s, k):
    return acN(x, s + 1, s + k)

def E(x, s, k):
    return coeffW(x, s + 1) * coeffW(x, k)

def aAt(x, s, r, i):
    return [W(x,s,r+1)*W(x,s,r+3), W(x,s,r+1)*E(x,s,r+2),
            E(x,s,r)*W(x,s,r+3),   E(x,s,r)*E(x,s,r+2)][i]

def mAt(x, s, r, j):
    return [W(x,s,r+2)**2, 2*W(x,s,r+2)*E(x,s,r+1), E(x,s,r+1)**2][j]

def det(Aw, Ah, Mw, Mh):
    return Aw*Mh - Mw*Ah

def R(s, r):
    tot = 0
    for i, j in product(range(4), range(3)):
        if (i, j) == (0, 0):
            continue
        tot += det(aAt(w,s,r,i), aAt(h,s,r,i), mAt(w,s,r,j), mAt(h,s,r,j))
    return sp.expand(tot)

def R_num(s, r, wv, hv):
    tot = Fraction(0)
    cw = lambda x,p: Fraction(p+1) * x**(p*(p+2))
    ac = lambda x,n,ss: sum(cw(x,p)*cw(x,max(ss-p,0)) for p in range(n))
    Wn = lambda x,k: ac(x, s+1, s+k)
    En = lambda x,k: cw(x, s+1)*cw(x, k)
    aA = lambda x,i: [Wn(x,r+1)*Wn(x,r+3), Wn(x,r+1)*En(x,r+2),
                      En(x,r)*Wn(x,r+3),   En(x,r)*En(x,r+2)][i]
    mA = lambda x,j: [Wn(x,r+2)**2, 2*Wn(x,r+2)*En(x,r+1), En(x,r+1)**2][j]
    for i, j in product(range(4), range(3)):
        if (i, j) == (0, 0):
            continue
        tot += aA(wv,i)*mA(hv,j) - mA(wv,j)*aA(hv,i)
    return tot

# ---- Part 1: falsification sweep on the physical simplex (exact rationals) ----
print("== falsification sweep: R(1,r) at exact simplex points (4w<=1, 0<=h<=w) ==")
ws = [Fraction(a, b) for a, b in
      [(1,4),(1,5),(1,6),(1,8),(1,10),(1,16),(3,16),(1,20),(2,9),(1,64),(5,21),(1,100)]]
bad = []
for r in range(0, 9):
    neg = 0
    for wv in ws:
        for num in range(0, 9):
            hv = wv * Fraction(num, 8)
            v = R_num(1, r, wv, hv)
            if v < 0:
                neg += 1
                bad.append((r, wv, hv, v))
    print(f"  r={r}: {len(ws)*9} points, negatives={neg}")
if bad:
    print("COUNTEREXAMPLES FOUND:")
    for b in bad[:6]:
        print("   ", b)
else:
    print("  no negative value found on the sweep")

# ---- Part 2: structure extraction for small r ----
print("\n== structure: content monomial, (w-h)/(w^2-h^2) factors, quotient signs ==")
for r in range(0, 5):
    e = R(1, r)
    if e == 0:
        print(f"  r={r}: identically zero"); continue
    p = sp.Poly(e, w, h)
    # content monomial
    mindeg_w = min(m[0] for m in p.monoms()); mindeg_h = min(m[1] for m in p.monoms())
    core = sp.expand(sp.cancel(e / (w**mindeg_w * h**mindeg_h)))
    fact = sp.factor(core)
    q1, r1 = sp.div(core, w - h, w)
    divisible_wh = sp.expand(r1) == 0
    q2, r2 = sp.div(core, w**2 - h**2, w)
    divisible_w2h2 = sp.expand(r2) == 0
    quotient = None
    if divisible_w2h2:
        quotient = sp.expand(q2)
    elif divisible_wh:
        quotient = sp.expand(q1)
    print(f"  r={r}: monomial w^{mindeg_w} h^{mindeg_h}, deg={sp.Poly(core,w,h).total_degree()}, "
          f"(w-h)|core: {divisible_wh}, (w^2-h^2)|core: {divisible_w2h2}")
    head = sp.factor_list(core)[1]
    print(f"        factor heads: {[str(f[0])[:60] + ('^'+str(f[1]) if f[1]>1 else '') for f in head][:4]}")
    if quotient is not None:
        qp = sp.Poly(quotient, w, h)
        negs = [(m, c) for m, c in zip(qp.monoms(), qp.coeffs()) if c < 0]
        print(f"        quotient: {len(qp.monoms())} monomials, {len(negs)} negative: "
              f"{[(f'w^{m[0]} h^{m[1]}', int(c)) for m, c in negs][:8]}")
