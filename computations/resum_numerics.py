import mpmath as mp
import sympy as sp
mp.mp.dps = 45

print("="*70)
print("TEST 1: The two DISTINCT indices — perturbative order k vs cluster size n")
print("="*70)
# Zero-dim phi^4: Z(g) = <exp(-g x^4/4!)>_Gaussian, standard divergent asymptotic series.
# perturbative coefficient a_k = (-1/4!)^k * (4k-1)!! / k!   (moment <x^{4k}> = (4k-1)!!)
def dfact(m):  # (m)!! for odd m
    r=1
    while m>1:
        r*=m; m-=2
    return r
print("Perturbative coeffs a_k of Z(g)=Sum a_k g^k  (zero-dim phi^4):")
prev=None
for k in range(1,9):
    ak = sp.Rational((-1)**k, sp.factorial(k)) * sp.Rational(dfact(4*k-1), 24**k)
    akf=float(abs(ak))
    ratio = akf/abs(prev) if prev else float('nan')
    print(f"  k={k}: |a_k|={akf:.6e}   |a_k/a_(k-1)|={ratio:.3f}")
    prev=akf
print("  -> ratios DIVERGE (factorial growth): radius of convergence = 0 (Dyson).")

print()
print("="*70)
print("TEST 2: The single-MODE Gaussian z_1 = 1 - e^{-t}(1-2t), its analyticity, bound")
print("="*70)
t=sp.symbols('t')
z1 = 1 - sp.exp(-t)*(1-2*t)
ser = sp.series(z1, t, 0, 9).removeO()
print("Taylor series of single-mode z_1 in t:")
print("  ", sp.nsimplify(ser))
coeffs=[sp.Poly(ser,t).coeff_monomial(t**j) for j in range(0,9)]
print("  Taylor coeffs c_j:", [float(c) for c in coeffs])
print("  -> coeffs DECAY (entire function): single-mode z_1 series CONVERGES (radius inf).")
print("     => single-mode 'resummation' is TRIVIAL; NOT the factorial 4D series.")

print()
print("Check z_1(t) <= g^2 = 4t  for t>=0 (the ExactSinglePolymer claim), worst ratio:")
worst=0.0
viol=0
for tt in [mp.mpf(x)/1000 for x in range(1,4000)]:
    z=1-mp.e**(-tt)*(1-2*tt)
    g2=4*tt
    if z> g2+mp.mpf(10)**-30: viol+=1
    if g2>0: worst=max(worst, float(z/g2))
print(f"  violations of z_1<=4t: {viol}; worst z_1/g^2 ratio = {worst:.6f}  (->3/4 as t->0)")

print()
print("="*70)
print("TEST 3: THE DIRECTION GAP — proved z_1<=g^2=-log w  vs  NEEDED z_1<=1-w")
print("="*70)
print("  KP structure field single_le_g2 requires  z_1 <= fieldActivity = (1-w).")
print("  ExactSinglePolymer proves               z_1 <= g^2 = -log w.")
print("  But 1-w <= -log w, so z_1<=-log w does NOT imply z_1<=1-w.")
print(f"  {'w':>7} {'1-w':>12} {'-log w=g^2':>14} {'z1(single-mode)':>18} {'z1<=1-w?':>10}")
for w in [0.9,0.99,0.999,0.9999]:
    ww=mp.mpf(w)
    g2=-mp.log(ww)
    tt=g2/4
    z=1-mp.e**(-tt)*(1-2*tt)
    oneminus=1-ww
    ok = z<=oneminus
    print(f"  {w:>7} {float(oneminus):>12.6e} {float(g2):>14.6e} {float(z):>18.6e} {str(ok):>10}")
print("  -> single-mode z_1 ~ (3/4)g^2 ~ (3/4)(-log w) which EXCEEDS (1-w) as w->1")
print("     (since -log w / (1-w) -> 1 but (3/4) factor... check ratio z_1/(1-w)):")
for w in [0.9,0.99,0.999]:
    ww=mp.mpf(w); g2=-mp.log(ww); tt=g2/4
    z=1-mp.e**(-tt)*(1-2*tt)
    print(f"    w={w}: z_1/(1-w) = {float(z/(1-ww)):.6f}")

print()
print("="*70)
print("TEST 4: KP geometric bound uses RESUMMED z_1, indexed by n, NOT order k")
print("="*70)
print("  |z_n| <= (mu g^2)^n, mu=6. As w->1, g^2->0 so mu g^2 -> 0: KP IMPROVES.")
for w in [0.9,0.99,0.999]:
    ww=mp.mpf(w); g2=1-ww; mg=6*g2
    conv = mg<1
    print(f"  w={w}: mu(1-w)={float(mg):.4f} converges={conv} sum<=1/(1-mg)={float(1/(1-mg)):.4f}")
print("  -> geometric in n. This is a bound on the RESUMMED cluster amplitude z_n,")
print("     which PRESUPPOSES the single-polymer activity z_1<=g^2 is already finite.")
print("     It does NOT bound the order-k perturbative coeffs a_k (Test 1, factorial).")
