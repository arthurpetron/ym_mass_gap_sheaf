import mpmath as mp, sympy as sp
mp.mp.dps = 50

print("=== (1) Wick/Isserlis 4th-moment failure of the library base measure ===")
s = sp.symbols('s', positive=True)
# two-point law on {+s,-s}, equal weight
m2 = sp.Rational(1,2)*(s**2+(-s)**2)          # <A^2>
m4_lib = sp.Rational(1,2)*(s**4+(-s)**4)       # <A^4> library
m4_wick = 3*m2**2                               # <A^4> true Gaussian (Isserlis)
print(" <A^2>_lib      =", sp.simplify(m2))
print(" <A^4>_lib      =", sp.simplify(m4_lib))
print(" <A^4>_Gaussian =", sp.simplify(m4_wick), "  (Isserlis 3<A^2>^2)")
print(" ratio wick/lib =", sp.simplify(m4_wick/m4_lib))
print(" at s=1: lib =", m4_lib.subs(s,1), " wick =", m4_wick.subs(s,1),
      " -> lib < wick :", bool(m4_lib.subs(s,1) < m4_wick.subs(s,1)))
# cross-check the two-point law IS mean-zero and variance-matched but non-Gaussian:
kurt = sp.simplify(m4_lib/m2**2)   # =1 ; a true Gaussian has 3
print(" normalized kurtosis (lib) =", kurt, " (Gaussian = 3) -> NOT Gaussian")

print("\n=== (2) character basis diverges across the a->0 window (2w^3 > 1) ===")
for w in ['0.5','0.7937005259840998','0.9','0.99','0.999']:
    W = mp.mpf(w); print(f"  w={w:>20}  2w^3 = {mp.nstr(2*W**3, 30)}")
wstar = (mp.mpf(1)/2)**(mp.mpf(1)/3)
print("  crossover 2w^3=1 at w* =", mp.nstr(wstar,40))
print("  exact sympy: coeffW(9/10,1)=2*(9/10)^3 =", sp.Rational(2)*sp.Rational(9,10)**3,
      " > 1 :", bool(sp.Rational(2)*sp.Rational(9,10)**3 > 1))

print("\n=== (3) field-space activity converges: g^2 ~ (1-w) -> 0, mu(1-w)<1 ===")
mu = 6
for w in ['0.9','0.99','0.999']:
    W = mp.mpf(w); g2 = 1-W
    print(f"  w={w:>7}  1-w={mp.nstr(g2,20):>22}  mu*(1-w)={mp.nstr(mu*g2,20):>12}  converges: {mu*g2<1}")

print("\n=== (4) saturating vs dodge amplitude (BOUND not CONSTRUCT), mu=6 ===")
# both satisfy Sum|z_n| <= 1/(1-mu g^2); dodge z_n=0, sat z_n=(mu g^2)^n : distinct
for w in ['0.99']:
    W=mp.mpf(w); r=mu*(1-W)
    dodge_sum = 0
    sat_sum = sum(r**n for n in range(1,200))
    bound = 1/(1-r)
    print(f"  w={w}  r=mu*g^2={mp.nstr(r,10)}  KP bound 1/(1-r)={mp.nstr(bound,20)}")
    print(f"    dodge Sum z_n = {dodge_sum}   sat Sum z_n = {mp.nstr(sat_sum,20)}   both <= bound: "
          f"{dodge_sum<=bound and sat_sum<=bound}   amplitudes distinct: {dodge_sum!=sat_sum}")
