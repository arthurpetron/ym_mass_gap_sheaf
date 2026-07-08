import sympy as sp

w = sp.symbols('w', positive=True)

def coeffW(p):
    return (p+1)*w**(p*(p+2))

def acNfull(t):
    return sp.expand(sum(coeffW(p)*coeffW(t-p) for p in range(0, t+1)))

def dmomNfull(t):
    return sp.expand(sum((t-2*p)**2 * coeffW(p)*coeffW(t-p) for p in range(0, t+1)))

def slack(s):
    aS, a1, a2 = acNfull(s), acNfull(s+1), acNfull(s+2)
    dS, d1, d2 = dmomNfull(s), dmomNfull(s+1), dmomNfull(s+2)
    LHS = 2*(d1*(aS*a2))
    RHS = dS*(a1*a2) + d2*(aS*a1) + 2*(aS*(a1*a2))
    return sp.expand(RHS - LHS)

print("=== slack_s(w): factor out w^k, analyze bracket B_s on (0,1) ===")
for s in range(0, 9):
    S = slack(s)
    P = sp.Poly(S, w)
    if P.is_zero:
        print(f"s={s}: slack identically 0 (?)"); continue
    # factor out lowest power of w
    k = min(m for (m,) in P.monoms())
    B = sp.Poly(sp.expand(S/w**k), w)
    coeffs = B.all_coeffs()  # high->low
    b0 = B.eval(0)  # constant term = B_s(0), the leading slack coeff
    # min of B on (0,1): sample + real roots in (0,1)
    f = sp.lambdify(w, B.as_expr(), 'mpmath')
    import mpmath as mp
    mp.mp.dps=40
    grid = [mp.mpf(i)/2000 for i in range(1,2001)]
    vals = [(g, f(g)) for g in grid]
    gmin, vmin = min(vals, key=lambda t: t[1])
    # count real roots of B in (0,1)
    try:
        nroots = sp.Poly(B, w).count_roots(0,1)
    except Exception as e:
        nroots = f"err:{e}"
    signch = sum(1 for a,b in zip(coeffs, coeffs[1:]) if a*b<0)
    print(f"s={s}: k(w^k)={k}, deg(B)={B.degree()}, B(0)={b0}, "
          f"min_B on(0,1)={sp.nsimplify(vmin,rational=False)!s:.0}... @w={float(gmin):.3f}, "
          f"realroots_in(0,1)={nroots}, coeff_sign_changes={signch}")
