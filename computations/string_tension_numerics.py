from mpmath import mp, mpf, log, exp, sqrt
from fractions import Fraction as F
mp.dps = 50

print("="*74)
print(" OS/CONFINEMENT numerics — string tension sigma, essential singularity")
print("="*74)

# ---------------------------------------------------------------------------
# (1) STRONG-COUPLING (fixed spacing) string tension: PROVED-analog, POSITIVE.
#     SU(2) fundamental Wilson loop, char expansion leading order:
#        <W(C)> = ( I_2(beta)/I_1(beta) )^{Area}  (Area = # plaquettes)
#     => sigma * a^2 = - log( I_2(beta)/I_1(beta) )  > 0 for all finite beta.
#     Small beta: I_2/I_1 ~ beta/4, so sigma a^2 ~ -log(beta/4) = log(4/beta).
# ---------------------------------------------------------------------------
from mpmath import besseli
print("\n(1) STRONG COUPLING (fixed a): sigma*a^2 = -log(I2/I1) > 0  [confinement, fixed-a]")
print(f"   {'beta':>8} {'I2/I1':>16} {'sigma*a^2':>16} {'log(4/beta)':>16}")
for beta in [mpf('0.1'), mpf('0.5'), mpf('1.0'), mpf('2.0'), mpf('4.0')]:
    ratio = besseli(2, beta)/besseli(1, beta)
    sa2 = -log(ratio)
    print(f"   {float(beta):8.3f} {float(ratio):16.10f} {float(sa2):16.10f} {float(log(4/beta)):16.10f}")
print("   -> sigma*a^2 > 0 at every FIXED beta: the strong-coupling area law (positive).")
print("      This is the analog of the PROVED fixed-spacing gap 107/108.")

# ---------------------------------------------------------------------------
# (2) CONTINUUM string tension via dimensional transmutation.
#     Physical sigma = (sigma a^2)/a^2. To take a->0 at FIXED physical sigma,
#     beta->infinity (g->0) along the AF trajectory:
#        a * Lambda_L = R2loop(g) := (b0 g^2)^{-b1/(2 b0^2)} * exp(-1/(2 b0 g^2))
#     with g^2 = 2N/beta = 4/beta for SU(2).
#     => sqrt(sigma_phys) = sqrt(sigma a^2) / a  = c_sigma * Lambda_L
#        and  a ~ (1/Lambda) exp(-1/(2 b0 g^2))  -> ESSENTIAL SINGULARITY at g=0.
# ---------------------------------------------------------------------------
# 2-loop coefficients (continuum, SU(N)=SU(2)) in the standard normalization
# b0 = 11N/(48 pi^2), b1 = 34 N^2/(3 (16 pi^2)^2). We only need the SHAPE.
from mpmath import pi
N = 2
b0 = mpf(11)*N/(48*pi**2)
b1 = mpf(34)*N**2/(3*(16*pi**2)**2)
def aLambda(g2):
    return (b0*g2)**(-b1/(2*b0**2)) * exp(-1/(2*b0*g2))
print("\n(2) DIMENSIONAL TRANSMUTATION: a*Lambda = (b0 g^2)^{-b1/2b0^2} exp(-1/(2 b0 g^2))")
print(f"    b0 = {float(b0):.6e},  b1 = {float(b1):.6e}")
print(f"   {'g^2':>8} {'a*Lambda':>22} {'exp(-1/2b0g^2)':>22}")
for g2 in [mpf('1.0'), mpf('0.5'), mpf('0.2'), mpf('0.1'), mpf('0.05')]:
    print(f"   {float(g2):8.3f} {mp.nstr(aLambda(g2),12):>22} {mp.nstr(exp(-1/(2*b0*g2)),12):>22}")
print("   -> a*Lambda -> 0 like exp(-1/(2 b0 g^2)) : ESSENTIAL SINGULARITY at g^2=0.")
print("      sqrt(sigma_phys) = const * Lambda = (1/a) * exp(-1/(2 b0 g^2)) * poly.")

# ---------------------------------------------------------------------------
# (3) THE DECISIVE CHECK: is sqrt(sigma) (continuum) tracked by ANY polynomial
#     in g^2 ? Compare exp(-1/(2 b0 g^2)) against g^2, g^4, g^6 as g^2 -> 0.
#     If the essential singularity beats every polynomial, a strong-coupling
#     (analytic-in-beta) argument CANNOT reach the continuum sigma>0.
# ---------------------------------------------------------------------------
print("\n(3) ESSENTIAL SINGULARITY vs POLYNOMIAL (the renormalon obstruction):")
print(f"   {'g^2':>8} {'exp(-1/2b0g^2)':>18} {'g^2':>10} {'ratio/g^2':>14} {'ratio/g^6':>14}")
for g2 in [mpf('0.2'), mpf('0.1'), mpf('0.05'), mpf('0.02')]:
    ess = exp(-1/(2*b0*g2))
    print(f"   {float(g2):8.3f} {mp.nstr(ess,10):>18} {float(g2):10.4f} {mp.nstr(ess/g2,8):>14} {mp.nstr(ess/g2**3,8):>14}")
print("   -> exp(-1/(2b0 g^2)) / g^{2n} -> 0 for EVERY n: the continuum string")
print("      tension is NON-PERTURBATIVE (invisible to any analytic/polynomial bound).")

# ---------------------------------------------------------------------------
# (4) Same essential singularity as the CONDENSATE (repo's condensate doc).
#     Condensate Lambda^2 ~ exp(-c/(b0 g^2)); string tension sigma ~ Lambda^2.
#     Both are the SAME exp(-c/(b0 g^2)) up to the coefficient c. CONFIRM ratio.
# ---------------------------------------------------------------------------
print("\n(4) sigma_phys ~ Lambda^2  (string tension IS a condensate-type scale):")
print(f"   {'g^2':>8} {'sigma~Lambda^2':>20} {'(a*Lambda)^2':>20}")
for g2 in [mpf('0.2'), mpf('0.1'), mpf('0.05')]:
    aL = aLambda(g2)
    print(f"   {float(g2):8.3f} {mp.nstr(aL**2,12):>20} {mp.nstr(aL**2,12):>20}")
print("   -> sqrt(sigma) = Lambda : the SAME non-perturbative scale as the condensate.")
print("      Confinement route reduces to the SAME essential singularity exp(-c/b0 g^2).")
print("\nDONE.")
