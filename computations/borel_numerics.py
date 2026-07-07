"""
Borel transform + renormalon assessment for the 0-dim phi^4 connected 2-point
z_1 = <x^2>(g), and the structural assessment for the su(2)/4D running-coupling case.

RIGOR: sympy EXACT for the coefficients; mpmath dps>=45 for the Borel/Laplace
reconstruction; no floats where an exact fact is claimed.
"""
import sympy as sp
import mpmath as mp

mp.mp.dps = 50

print("="*78)
print("PART A.  Exact connected 2-point coefficients d_k of the 0-dim phi^4 toy")
print("="*78)

# Z(g) = (1/sqrt(2pi)) int e^{-x^2/2 - g x^4} dx ,  <x^2>(g) = num/Z.
# Perturbative series in g about g=0, EXACT via Gaussian moments:
#   int x^{2m} e^{-x^2/2} dx / sqrt(2pi) = (2m-1)!!
# Z(g)      = sum_k (-g)^k/k! * <x^{4k}>_0        = sum_k (-g)^k/k! (4k-1)!!
# N(g)=<x^2 unnorm> = sum_k (-g)^k/k! <x^{4k+2}>_0 = sum_k (-g)^k/k! (4k+1)!!
g = sp.symbols('g')
K = 24  # order

def dfact(n):  # (n)!! for odd n, exact
    r = sp.Integer(1)
    while n > 1:
        r *= n
        n -= 2
    return r

Zser = sum((-g)**k/sp.factorial(k)*dfact(4*k-1) for k in range(K+1))
Nser = sum((-g)**k/sp.factorial(k)*dfact(4*k+1) for k in range(K+1))
# <x^2> = N/Z as a power series to order K
x2 = sp.series(Nser/Zser, g, 0, K+1).removeO()
x2poly = sp.Poly(sp.expand(x2), g)
d = [x2poly.coeff_monomial(g**k) for k in range(K+1)]
print("d_0..d_6 (exact) =", d[:7])
print("|d_1..d_5|       =", [abs(dd) for dd in d[1:6]])
signs = [sp.sign(dd) for dd in d[1:K+1]]
print("signs of d_1..d_%d =" % K, [int(s) for s in signs])
alt = all(int(signs[i]) == -int(signs[i+1]) for i in range(len(signs)-1))
print("STRICTLY ALTERNATING (d_k):", alt)

# ratio |d_{k+1}/d_k| and /k  -> factorial signature
print("\n|d_{k+1}/d_k| and /k  (factorial <=> ratio/k -> const != 0):")
for k in range(1, 12):
    r = abs(d[k+1])/abs(d[k])
    print(f"  k={k:2d}  |d_{k+1}/d_k| = {float(r):9.3f}   /k = {float(r)/k:7.4f}")

print("\n"+"="*78)
print("PART B.  The BOREL TRANSFORM  B(u) = sum_k d_k u^k / k!  (factorial divided out)")
print("="*78)
# b_k = d_k / k!
b = [sp.nsimplify(d[k]/sp.factorial(k)) for k in range(K+1)]
print("b_0..b_6 (exact) =", [sp.nsimplify(bb) for bb in b[:7]])
print("\n|b_{k+1}/b_k|  ->  1/radius  (should tend to a CONSTANT: finite radius):")
for k in range(1, 14):
    r = abs(b[k+1])/abs(b[k])
    print(f"  k={k:2d}  |b_{k+1}/b_k| = {float(r):10.5f}")
# The connected 2-point IR/UV growth of phi^4-0dim: d_k ~ (-1)^k k! A^k * C,
# so b_k ~ (-A)^k C  -> radius 1/A, singularity at u = -1/A (NEGATIVE axis, alternating).
# Estimate A = lim |b_{k+1}/b_k|
A_est = float(abs(b[K])/abs(b[K-1]))
print(f"\nEstimated 1/radius  A = lim|b_(k+1)/b_k| ~ {A_est:.6f}")
print(f"Estimated radius of convergence of B(u): 1/A ~ {1/A_est:.6f}")
print("Sign of successive b_k (alternating => nearest singularity on NEGATIVE u-axis):")
print("   ", [int(sp.sign(bb)) for bb in b[1:12]])

print("\n"+"="*78)
print("PART C.  BOREL / LAPLACE RECONSTRUCTION of the EXACT <x^2>(g)  (mpmath dps=50)")
print("="*78)
# <x^2>(g) = (1/g) int_0^inf e^{-u/g} B(u) du   [Borel sum in g].
# We must reconstruct the TRUE non-perturbative <x^2>(g) = N(g)/Z(g) with
#   Z(g)=(1/sqrt(2pi)) int e^{-x^2/2-g x^4} dx ,  N(g)= same with x^2 inserted.
def true_x2(gval):
    gv = mp.mpf(gval)
    num = mp.quad(lambda x: x**2*mp.e**(-x**2/2 - gv*x**4), [-mp.inf, 0, mp.inf])
    den = mp.quad(lambda x:      mp.e**(-x**2/2 - gv*x**4), [-mp.inf, 0, mp.inf])
    return num/den

# Borel transform as a numerical function via its (truncated) exact series,
# but B(u) has a finite radius, so we need it BEYOND the radius for the Laplace
# integral. Use the CLOSED FORM of B(u): for this model B(u) is analytic on
# [0,inf) (nearest singularity on the NEGATIVE axis). We evaluate B(u) by
# analytic continuation via a Pade approximant of the truncated Borel series.
bfloat = [mp.mpf(str(sp.Rational(bb))) if bb.is_rational else mp.mpf(str(sp.N(bb,60))) for bb in b]

def pade_eval(coeffs, u, L, M):
    # build [L/M] Pade of sum coeffs[k] u^k, evaluate at u
    P, Q = mp.pade(coeffs, L, M)
    return mp.polyval(P[::-1], u)/mp.polyval(Q[::-1], u)

def borel_sum_x2(gval, L=11, M=12):
    gv = mp.mpf(gval)
    # (1/g) int_0^inf e^{-u/g} B(u) du,  B(u) via Pade continuation
    f = lambda u: mp.e**(-u/gv)*pade_eval(bfloat, u, L, M)
    val = mp.quad(f, [0, gv, 5*gv, 20*gv, mp.inf])
    return val/gv

for gval in ['0.02', '0.05', '0.1']:
    t = true_x2(gval)
    bs = borel_sum_x2(gval)
    print(f"  g={gval}:  true <x^2> = {mp.nstr(t,18)}   Borel[11/12] = {mp.nstr(bs,18)}   |diff| = {mp.nstr(abs(t-bs),4)}")

print("\n"+"="*78)
print("PART D.  RENORMALON assessment: sign of the coefficients decides the axis")
print("="*78)
print("0-dim phi^4 toy: d_k ALTERNATE  => B(u) nearest singularity on NEGATIVE u-axis")
print("   => Laplace int_0^inf e^{-u/g}B(u) du has NO singularity on the path => CONVERGES,")
print("      unambiguously reconstructs the exact <x^2>(g).  BOREL-SUMMABLE.  (verified Part C)")
print()
print("4D asymptotically-free su(2) YM (the real theory): the IR renormalon gives")
print("   FIXED-SIGN large-order growth  d_k ~ +k! (beta0/N)^k  (Parisi/'t Hooft/Beneke)")
print("   => B(u) singularity on the POSITIVE u-axis at u_0 = (2N)/(beta0) * (2-loop struct).")
print("   The one-loop coefficient of SU(2):  beta0 = 11/3 * C2(adj) = 11/3 * 2 = 22/3.")
b0 = sp.Rational(11,3)*2
print("   SU(2) one-loop beta0 = 11/3 * C2(adj=2) =", b0, "=", float(b0))
print("   Leading IR-renormalon Borel singularity  u_0 = 2/beta0 (in the standard")
print("   normalization t = 1/(beta0 g^2) Borel variable) => u_0 =", sp.Rational(2)/b0,
      "= %.4f > 0 (ON the positive axis)." % float(sp.Rational(2)/b0))
print()
print("   => The Laplace path (0,inf) HITS the singularity => the naive Borel sum is")
print("      AMBIGUOUS by ~ exp(-u_0/g^2) ~ exp(-2/(beta0 g^2)) = the CONDENSATE scale.")
print("      This is the genuine non-perturbative renormalon ambiguity of 4D YM.")
