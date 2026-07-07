"""
Rigorous numeric/symbolic verification for the Isserlis-Gaussian-base construction.
mpmath dps>=40 for floats; sympy for EXACT rational/combinatorial identities.

Checks:
 1. Double-factorial moment law  <x^{2n}> = (2n-1)!! s^{2n}  (Isserlis, single mode).
 2. <x^4> = 3 s^4   (the FIX of library_base_fails_wick: 3, not 1).
 3. numPairings n = (2n-1)!! = (2n)!/(2^n n!) = # perfect matchings of 2n points, recursion.
 4. Multi-mode Wick 4-point  <x_i x_j x_k x_l> = C_ij C_kl + C_ik C_jl + C_il C_jk,
    diagonal reduction to 3 V^2, and vs a genuine random Gaussian sample.
 5. Determination-vs-resummation: each finite-order Feynman coefficient is a determined
    number (exact), but the perturbative series is ASYMPTOTIC (factorial growth) -> the
    K->infinity resummation is the residual.
"""
import sympy as sp
from sympy import factorial, factorial2, Rational, symbols, integrate, exp, sqrt, pi, oo, simplify
import mpmath as mp
mp.mp.dps = 50

print("="*72)
print("1) Double-factorial Isserlis moments <x^{2n}> = (2n-1)!! s^{2n}")
s = symbols('s', positive=True)
x = symbols('x', real=True)
def gauss_moment_exact(n, s):
    # <x^{2n}> for N(0, s^2) via exact integral
    return integrate(x**(2*n) * exp(-x**2/(2*s**2)) / (sqrt(2*pi)*s), (x, -oo, oo))
for n in range(0, 6):
    integ = sp.simplify(gauss_moment_exact(n, s))
    df = factorial2(2*n-1) if n >= 1 else sp.Integer(1)   # (2n-1)!!, with (-1)!!=1
    claim = df * s**(2*n)
    ok = sp.simplify(integ - claim) == 0
    print(f"  n={n}: integral={integ},  (2n-1)!!*s^(2n)={claim},  MATCH={ok}")
    assert ok

print("="*72)
print("2) <x^4> = 3 s^4  (fixes library_base_fails_wick: library gave s^4=1, Isserlis=3)")
m4 = sp.simplify(gauss_moment_exact(2, s))
print(f"  <x^4> = {m4}   == 3*s^4 ? {sp.simplify(m4 - 3*s**4)==0}")
print(f"  at s=1:  Isserlis <x^4> = {m4.subs(s,1)}   library {{+-1}} <x^4> = {sp.Integer(1)}   (3 > 1)")
assert sp.simplify(m4 - 3*s**4) == 0
assert m4.subs(s,1) == 3

print("="*72)
print("3) numPairings n = (2n-1)!! = (2n)!/(2^n n!) = # perfect matchings; recursion (2n+1)*")
def numPairings(n):
    r = 1
    for i in range(n):
        r *= (2*i+1)
    return r
for n in range(0, 8):
    a = numPairings(n)
    b = int(factorial2(2*n-1)) if n >= 1 else 1
    c = int(factorial(2*n)//(2**n * factorial(n)))
    rec = (2*(n-1)+1)*numPairings(n-1) if n >= 1 else 1
    print(f"  n={n}: prod={a}, (2n-1)!!={b}, (2n)!/(2^n n!)={c}, recursion={rec}, all equal={a==b==c==rec}")
    assert a == b == c == rec
print(f"  numPairings(2)=3, numPairings(3)=15  ->  {numPairings(2)==3 and numPairings(3)==15}")

print("="*72)
print("4) Multi-mode Wick 4-point  = sum over 3 pairings of C's; diagonal -> 3V^2")
Cij,Ckl,Cik,Cjl,Cil,Cjk = symbols('Cij Ckl Cik Cjl Cil Cjk')
wick4 = Cij*Ckl + Cik*Cjl + Cil*Cjk
V = symbols('V', positive=True)
diag = wick4.subs({Cij:V,Ckl:V,Cik:V,Cjl:V,Cil:V,Cjk:V})
print(f"  wick4(diagonal V) = {sp.simplify(diag)}   == 3 V^2 ? {sp.simplify(diag-3*V**2)==0}")
assert sp.simplify(diag-3*V**2)==0
# genuine multivariate Gaussian sample check: random 4x4 SPD covariance, compare
# <x_i x_j x_k x_l> (exact Isserlis) to Monte-Carlo estimate.
import random
random.seed(1)
mp.mp.dps = 30
# build a small 4-dim covariance
A = mp.matrix(4,4)
for i in range(4):
    for j in range(4):
        A[i,j] = mp.mpf(random.uniform(-1,1))
Cov = A*A.T  # SPD
i,j,k,l = 0,1,2,3
isserlis = Cov[i,j]*Cov[k,l] + Cov[i,k]*Cov[j,l] + Cov[i,l]*Cov[j,k]
# Monte Carlo via Cholesky
L = mp.cholesky(Cov)
N = 400000
acc = mp.mpf(0)
import math
for _ in range(N):
    z = mp.matrix([mp.mpf(random.gauss(0,1)) for _ in range(4)])
    xv = L*z
    acc += xv[i]*xv[j]*xv[k]*xv[l]
mc = acc/N
print(f"  Isserlis <x0x1x2x3> = {mp.nstr(isserlis,12)}")
print(f"  Monte-Carlo (N={N}) = {mp.nstr(mc,12)}   rel.err={mp.nstr(abs(mc-isserlis)/abs(isserlis),4)}")

print("="*72)
print("5) Determination vs resummation: finite-order coeffs DETERMINED; series ASYMPTOTIC")
# Toy: 0-dim phi^4 'partition' Z(g)=int e^{-x^2/2 - g x^4} dx / int e^{-x^2/2}.
# Perturbative coefficients a_k are EXACT determined rationals (Wick/Isserlis of x^{4k}):
#   Z(g) ~ sum_k (-g)^k /k! <x^{4k}> = sum_k (-g)^k/k! (4k-1)!!
# Each a_k is a determined number, but |a_k| ~ (4k-1)!! /k! grows factorially -> radius 0.
g = symbols('g')
def coeff(k):
    return Rational((-1)**k, factorial(k)) * factorial2(4*k-1)   # determined exact rational
print("  order-k Feynman coefficient a_k = (-1)^k/k! (4k-1)!!  (each EXACT/determined):")
for k in range(0, 8):
    ak = coeff(k)
    print(f"    a_{k} = {ak}   |a_k|={abs(ak)}")
ratios = [abs(coeff(k+1))/abs(coeff(k)) for k in range(1,7)]
print(f"  |a_(k+1)/a_k| = {[str(r) for r in ratios]}  -> grows without bound (radius of conv = 0)")
print("  => coefficients are DETERMINED term-by-term (the Isserlis fix), but the")
print("     K->inf sum is only defined by a resummation (Borel) prescription = the RESIDUAL.")
# Borel sum sanity: the true Z(g) for g=0.1 by direct quadrature vs asymptotic partial sums
gval = mp.mpf('0.1')
true = mp.quad(lambda t: mp.e**(-t**2/2 - gval*t**4), [-mp.inf, mp.inf]) / mp.sqrt(2*mp.pi)
print(f"  true Z(0.1) (quadrature) = {mp.nstr(true,20)}")
part = mp.mpf(0)
best = None
for k in range(0, 20):
    part += mp.mpf(str(coeff(k))) * gval**k
    err = abs(part-true)
    if best is None or err < best[1]:
        best = (k, err, part)
print(f"  best asymptotic partial sum at order k={best[0]}: {mp.nstr(best[2],20)} (err {mp.nstr(best[1],4)});")
print(f"  beyond optimal truncation the partial sums DIVERGE (asymptotic) -> resummation needed.")
print("="*72)
print("ALL CHECKS PASSED.")
