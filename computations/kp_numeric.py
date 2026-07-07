import mpmath as mp, sympy as sp
mp.mp.dps = 50

print("=== KP amplitude bound |z_n| <= (C*mu*a)^n, convergence C*mu*a < 1 ===")
# Combinatorial growth: per-cluster tree-graph factor eSurrogate=3 (>= e), animal count K^n.
# mu_comb = K * 3 (the growth constant). Single-polymer activity a = |z_1| <= g^2 ~ (1-w).
# 4D shared-link connectivity K ~ mu_lat = 6 (each plaquette borders 2(d-1)=6 via a shared link).
# Actually the KP effective growth constant that matters is the product; we test the
# self-consistent KP criterion  (growth)*a < 1  with growth ~ mu (=6, linear connectivity)
# and a = |z_1| ~ g^2 = -log w ~ (1-w).

print("\n(1) g^2 bracket:  (1-w) <= -log w <= (1-w)/w")
for w in ['0.9','0.99','0.999','0.9999']:
    W = mp.mpf(w)
    lo = 1-W; g2 = -mp.log(W); hi = (1-W)/W
    print(f"  w={w:8}  1-w={mp.nstr(lo,6):10}  g2={mp.nstr(g2,8):12}  (1-w)/w={mp.nstr(hi,8)}  bracket_ok={lo<=g2<=hi}")

print("\n(2) KP criterion  mu*a < 1  with a=|z1|<=g2~(1-w), mu=6 (4D):")
for w in ['0.9','0.99','0.999']:
    W = mp.mpf(w); a = 1-W; mu = 6
    r = mu*a
    conv = r < 1
    geo = 1/(1-r) if conv else mp.inf
    print(f"  w={w:8}  a=1-w={mp.nstr(a,6):9}  mu*a={mp.nstr(r,6):8}  converges={conv}  sum<=1/(1-mu a)={mp.nstr(geo,6)}")

print("\n(3) tree-count growth: tau_n <= n^(n-2) (Cayley) <= 3^n * n! (Euler), so |phi^T(Y)|<=3^|Y|")
for n in range(1,9):
    cay = n**(n-2) if n>=2 else 1
    eul = 3**n * sp.factorial(n)
    ratio = sp.Rational(cay, eul)
    print(f"  n={n}: n^(n-2)={cay:12}  3^n*n!={int(eul):18}  n^(n-2)/(3^n n!)={float(ratio):.3e}  (<=1: {cay<=eul})")

print("\n(4) full amplitude termwise:  |z_n| <= combGrowth_n * a^n <= (K*3*a)^n")
print("    with animal K=2 (illustrative), 3 the Euler surrogate, a=(1-w):")
for w in ['0.99','0.999']:
    W=mp.mpf(w); a=1-W; K=mp.mpf(2); mu=K*3
    r=mu*a; print(f"  w={w}: mu=K*3={mp.nstr(mu,4)}  mu*a={mp.nstr(r,6)}  conv={r<1}")

print("\n(5) second-cumulant n=2 tight bound (already proved): z_2 <= 6(1-w)^2 = mu*a^2 (mu=6, tree=1)")
for w in ['0.9','0.99']:
    W=mp.mpf(w); a=1-W
    print(f"  w={w}: 6(1-w)^2={mp.nstr(6*a*a,6)}   (mu a^2 with mu=6, matches inducedBound coeff 6)")

# exact sympy: 3^n n! >= n^(n-2) for all n (Euler e<3), and 1/(1-6(1-w)) finite for w>5/6
w=sp.Symbol('w')
print("\n(6) exact crossover: mu*a=1 => 6(1-w)=1 => w=5/6:", sp.solve(sp.Eq(6*(1-w),1),w))
print("    field KP gate 0<1-6(1-w) holds for w>5/6=0.8333...; continuum w->1 => a->0 => always converges.")
