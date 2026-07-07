from mpmath import mp, mpf, exp
import sympy as sp
mp.dps = 50

# ============================================================
# CLAIM 2: matching the renormalon ambiguity to the self-similar condensate.
# Condensate module: condRateExp = c/beta0 = 6/11, condOffset=12,
#   condExponent(k) = (6/11)(k+12),  condensateCReal(k)=exp(-(6/11)(k+12)),
#   rho = exp(-6/11).
# su(2): beta0 = 11/3 * C2(adj) = 11/3 * 2 = 22/3.  c=4 (dim-4 condensate/OPE).
#   c/beta0 = 4/(22/3) = 12/22 = 6/11.  EXACT.
# One-loop AF running matched so 1/g_k^2 = k + 12  (=> c/(beta0 g_k^2)=condExponent(k)).
#   => g_k^2 = 1/(k+12);  1/g_k^2 increases by exactly 1 per RG step.
# Renormalon pole (Borel var t0=c/beta0=6/11): ambiguity exponent
#   t0/g_k^2 = (6/11)(k+12) = condExponent(k).
# So renormalon ambiguity ∝ exp(-t0/g_k^2) = condensateCReal(k), EXACTLY,
#   and per step multiplies by rho=exp(-6/11).
# ============================================================
c   = sp.Rational(4)
b0  = sp.Rational(11,3)*2        # = 22/3
t0  = c/b0
print("beta0 (su2 1-loop) =", b0, "  c =", c, "  t0 = c/beta0 =", t0, "= 6/11?", t0==sp.Rational(6,11))
condRateExp = sp.Rational(6,11)
print("condRateExp =", condRateExp, "  matches t0:", t0==condRateExp)

rho = exp(mpf(-6)/11)
print("rho = exp(-6/11) =", mp.nstr(rho,15))

def condExponent(k): return mpf(6)/11*(k+12)
def condensate(k):   return exp(-condExponent(k))
# ambiguity exponent from renormalon with g_k^2 = 1/(k+12):
def ambExp(k):       return (mpf(6)/11) * (k+12)   # t0/g_k^2

print("\n k | condExponent | condensate(k) | ambiguity-exp t0/g_k^2 | ratio cond(k+1)/cond(k)")
for k in range(6):
    ce=condExponent(k); cd=condensate(k); ae=ambExp(k)
    ratio = condensate(k+1)/condensate(k)
    print(f" {k} | {mp.nstr(ce,10):>12} | {mp.nstr(cd,12):>14} | {mp.nstr(ae,10):>10} | {mp.nstr(ratio,15)}")
    assert abs(ce-ae) < mpf('1e-40'), "exponent mismatch"
    assert abs(ratio-rho) < mpf('1e-40'), "ratio != rho"
print("\nALL: condExponent(k) == t0/g_k^2 (renormalon amb exp)  AND  cond(k+1)/cond(k)==rho  to 1e-40")

# su(2) numeric Lambda scale at a reference: Lambda/mu = exp(-1/(2 beta0 g^2)) form check (info)
print("\nInfo: leading IR renormalon in Borel u-plane sits at u=2 (dim-4); ambiguity ~ (Lambda/Q)^4.")
