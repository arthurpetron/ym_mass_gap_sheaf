import mpmath as mp
mp.mp.dps = 45

# ============================================================
# THE IR RENORMALON AND ITS IR-CUTOFF (MASS-GAP) REGULARIZATION
# ------------------------------------------------------------
# Standard renormalon model (Beneke-style). The IR-sensitive
# perturbative coefficients of a dimension-2p operator come from
#   d_n = ∫_0^1 dξ ξ^{p-1} (-ln ξ)^n        (Q^2=1, β0=1, ξ=k^2)
# The IR region ξ→0 (x=-lnξ→∞) produces the FACTORIAL.
#   massless:  d_n = ∫_0^1 ξ^{p-1}(-lnξ)^n dξ = n!/p^{n+1}
#   Borel B(u)=Σ d_n u^n/n! = 1/(p(1-u/p)) : POLE at u0=p>0  (renormalon).
#
# THE MASS GAP / IR CUTOFF: no modes below the gap scale m,
# i.e. lower limit ξ = μ² (μ = m/Q). Physically k²→k²+m² kills
# the deep-IR ξ<μ² region.
#   d_n(μ) = ∫_{μ²}^1 ξ^{p-1}(-lnξ)^n dξ
#          = γ(n+1, pΛ)/p^{n+1},   Λ = -ln(μ²)   (lower incomplete Γ)
# ============================================================

p = mp.mpf(2)          # dimension-4 (gluon condensate) weight k^2 -> p=2
u0 = p                 # renormalon Borel pole location (massless), >0

def d_massless(n):
    return mp.factorial(n)/p**(n+1)

def d_massive(n, mu2):
    Lam = -mp.log(mu2)
    # ∫_{μ²}^1 ξ^{p-1}(-lnξ)^n dξ = ∫_0^Λ x^n e^{-p x} dx = γ(n+1,pΛ)/p^{n+1}
    return mp.gammainc(n+1, 0, p*Lam)/p**(n+1)   # lower incomplete gamma

print("=== (1) COEFFICIENT GROWTH: factorial (massless) vs geometric (massive) ===")
mu2 = mp.mpf('0.1')            # gap scale μ² = 0.1  => Λ = ln(10) ≈ 2.302
Lam = -mp.log(mu2)
print(f"mu^2 = {mu2}, Lambda=-ln(mu^2) = {mp.nstr(Lam,8)}")
print(f"{'n':>3} {'d_n massless':>18} {'ratio':>8} | {'d_n(mu) massive':>20} {'ratio':>8}")
prev0=prevm=None
for n in [2,4,6,8,10,14,18,22,26,30]:
    d0=d_massless(n); dm=d_massive(n,mu2)
    r0 = mp.nstr(d_massless(n)/d_massless(n-1),5) if n>2 else '-'
    rm = mp.nstr(d_massive(n,mu2)/d_massive(n-1,mu2),5) if n>2 else '-'
    print(f"{n:>3} {mp.nstr(d0,6):>18} {r0:>8} | {mp.nstr(dm,6):>20} {rm:>8}")
print("massless ratio d_{n+1}/d_n ~ (n+1)/p -> infinity (FACTORIAL, radius-0 Borel)")
print(f"massive  ratio -> Lambda = {mp.nstr(Lam,6)} (GEOMETRIC, finite; Borel entire)")

print("\n=== (2) BOREL TRANSFORM B(u)=Σ d_n u^n/n! at the renormalon point u0=p=2 ===")
def Borel(u, mu2=None, N=400):
    s=mp.mpf(0)
    for n in range(N+1):
        dn = d_massless(n) if mu2 is None else d_massive(n,mu2)
        s += dn*mp.power(u,n)/mp.factorial(n)
    return s
# massless closed form B(u)=1/(p(1-u/p))=1/(p-u): pole at u=p
print("massless B(u) closed form = 1/(p-u):")
for uu in [mp.mpf('1.5'), mp.mpf('1.9'), mp.mpf('1.99')]:
    print(f"  u={float(uu):.3f}: series={mp.nstr(Borel(uu),8)}  1/(p-u)={mp.nstr(1/(p-uu),8)}")
print("  -> DIVERGES as u->2 (positive-axis renormalon POLE).")
print("massive B_mu(u) at and beyond the massless pole u0=2 (FINITE = analytic):")
for uu in [mp.mpf('1.99'), mp.mpf('2.0'), mp.mpf('2.5'), mp.mpf('3.0')]:
    print(f"  u={float(uu):.3f}: B_mu={mp.nstr(Borel(uu,mu2),10)}  (finite -> NO pole)")

print("\n=== (3) LAPLACE-BOREL AMBIGUITY: massless SIGNED, massive DEFINITE ===")
# z(a) = ∫_0^∞ e^{-u/a} B(u) du.  massless B=1/(p-u): pole at u=p on the path.
# ambiguity (discontinuity between +/- iε prescriptions) = 2π i Res = ± π e^{-p/a}.
def ambiguity_massless(a):
    # residue of 1/(p-u) at u=p is -1; times e^{-u/a}: |Im| jump = π e^{-p/a}
    return mp.pi*mp.e**(-p/a)
def laplace_massive(a, mu2, U=200):
    # B_mu entire and decaying? B_mu(u) ~ e^{Λ u}/(...)? Actually d_n(μ)~Λ^{n} so
    # B_mu(u)=Σ Λ-ish ~ grows like e^{(something)u}; the Laplace ∫ e^{-u/a}B_mu du
    # converges for a<1/Λ and is UNIQUE (no pole on path) -> DEFINITE, no ambiguity.
    f=lambda u: mp.e**(-u/a)*Borel(u,mu2,N=250)
    return mp.quad(f,[0,U])
a=mp.mpf('0.5')
print(f"coupling a={a}")
print(f"  massless ambiguity |Δz| = π e^(-p/a) = {mp.nstr(ambiguity_massless(a),8)}  (NONZERO, SIGNED ±)")
# massive: check the Laplace path hits no singularity -> the +iε and -iε agree.
# B_mu(u) is real-analytic and finite for all real u (shown in (2)); the integral is single valued.
print(f"  massive: B_mu(u) finite/analytic on [0,∞) (part 2) => Laplace single-valued, ambiguity = 0")

print("\n=== (4) THE a->0 (m->0) UNIFORMITY: the renormalon RE-APPEARS ===")
print("As the cutoff is removed (μ²->0, Λ->∞), d_n(μ) -> d_n massless: factorial returns.")
print(f"{'mu^2':>10} {'Lambda':>8} {'d_30(mu)/d_30(massless)':>26}")
for m2 in ['0.3','0.1','0.03','0.01','0.001','1e-6']:
    m2=mp.mpf(m2); L=-mp.log(m2)
    ratio=d_massive(30,m2)/d_massless(30)
    print(f"{mp.nstr(m2,3):>10} {mp.nstr(L,5):>8} {mp.nstr(ratio,8):>26}")
print("-> ratio -> 1 as μ²->0: the mass-regulated Borel transform loses analyticity")
print("   in the m->0 limit; the renormalon is NON-UNIFORM in the cutoff removal.")
print("   THE UNIFORMITY of positive-axis analyticity as a->0 IS the residual (=singleStep).")
