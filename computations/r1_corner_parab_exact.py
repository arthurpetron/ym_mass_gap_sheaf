import sympy as sp
t=sp.symbols('t',positive=True)
# P(t) = sum_{D=t-2p, p=0..t} (n^2-D^2) D^2 / sum (n^2-D^2), n=t+2. Split even/odd t.
def P_closed(parity):
    # D ranges over {parity, parity+2, ..} with |D|<=t; but easier: p=0..t, D=t-2p.
    # Use symbolic sum via known power sums. Do it for t=parity+2j general -> compute for many t, fit.
    pass
# numeric exact for many t, then fit polynomial (separately for even/odd t)
def Pexact(tv):
    n=tv+2; num=den=0
    for p in range(tv+1):
        D=tv-2*p; wt=n*n-D*D; den+=wt; num+=D*D*wt
    return sp.Rational(num,den)
# fit even t and odd t separately as rational function of t
print("P(t) exact values:")
ev=[(tv,Pexact(tv)) for tv in range(2,22,2)]
od=[(tv,Pexact(tv)) for tv in range(3,23,2)]
for lbl,dat in [("even t",ev),("odd t",od)]:
    print(f" {lbl}: "+", ".join(f"t={tv}:{v}" for tv,v in dat[:6]))
    # fit as polynomial in t (try degree 2) via interpolation
    pts=[(sp.Rational(tv),v) for tv,v in dat]
    poly=sp.interpolate(pts,t)
    print(f"   interpolated P(t) = {sp.simplify(poly)}")
# Delta^2 P
print("\nDelta^2 P(s) = P(s)-2P(s+1)+P(s+2):")
for s in [7,8,20,50]:
    print(f"  s={s}: {Pexact(s)-2*Pexact(s+1)+Pexact(s+2)}  (should be 2/5)")
