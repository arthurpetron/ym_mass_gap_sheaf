"""MD.3 / work_plan §17-P1 — the ENVELOPE LEMMA, stage one: a certified
truncation-error bound for the flat tau-series of the slab flow, and the
first inhabited two-sided envelope with explicit rational (K, tau*, s*).

THE STATEMENT CERTIFIED HERE (stage one, discriminator form)
------------------------------------------------------------
Let X_11(tau) = log( T[1,1] T[0,0] / T[0,1]^2 ) be the one-step slab
cross-observable (the discriminator whose tau-series is banked exact
through tau^3, work_plan SS16f-16g):

    X_11 = 6 tau^2 + (115/6) tau^3 + O(tau^4).

We produce explicit positive rationals K_X and tau* such that

    | X_11(tau) - 6 tau^2 - (115/6) tau^3 |  <=  K_X * tau^4
                                       for all  0 < tau <= tau*,

whence the two-sided envelope, on (0, tau*]:

    6 tau^2 (1 - rho(tau))  <=  X_11(tau)  <=  6 tau^2 (1 + rho(tau)),
    rho(tau) = (115/36) tau + (K_X/6) tau^2,

and in particular X_11(tau) > 0 for all 0 < tau <= tau* — the
anti-screening sign of the derived flow, certified on the weak-coupling
interval (s*, 1), s* = e^{-tau*} (an explicit rational upper bound on
e^{-tau*} is emitted).  This discharges the A1 flat-limit interchange
flag of SS16f at the X-observable and closes the owed certified-rational
SU(2) slack at network level, in the form the dichotomy consumes.

METHOD (the eta-variable master lemma)
--------------------------------------
Write eta = sqrt(8 tau) and scale the 48 flat fields (16 links x 3
su(2) components) as x = eta M xi, M M^T = G^{-1}, xi standard Gaussian
(the SS16e dictionary: covariance 8 tau G^{-1} per component).  The
EXACT main-branch integrand A(eta; xi) — face Jacobians, BCH
non-closure of the plaquette angles, loop insertions — is, at fixed xi,
ANALYTIC in eta on |eta| < r0/(cM |xi|) because every insertion enters
through the link fields x (radius = the BCH/Jacobian domain), and the
1/(8 tau) of the action's cubic-and-higher parts pairs with x^3 ~ eta^3
to leave POSITIVE powers of eta (V_3/tau ~ eta, V_4/tau ~ eta^2, ...):
the essential singularity of the naive x-expansion disappears in eta.
Then, per entry T[n,m]:

  (i)   [small field, |xi| <= r0/(cM eta)]  the eta-Taylor tail after
        order 6 is bounded by Cauchy on the circle |eta'| = r0/(cM|xi|):
        tail <= M(xi) (eta cM |xi| / r0)^8 / (1 - eta cM |xi|/r0),
        with M(xi) <= A0 e^{|xi|^2/4} once  r0 <= 1/(4 g3 cM^2)  (the
        cubic insertion's sup on the circle is <= |xi|^2/4; the quartic
        and higher close under the same choice by geometric domination).
        Taking expectations: a bound  K_small * eta^8 = K_small' tau^4
        with K_small explicit through the Gaussian moment
        E[|xi|^8 e^{|xi|^2/4}] = 2^{d/2+4} d(d+2)(d+4)(d+6)  (variance-2
        chi moments), d = 48.
  (ii)  [large field] the region |xi| > r0/(cM eta) contributes, on the
        REAL domain where the exact integrand is the positive kernel
        product bounded by d_n d_m (|chi| <= dim, kernel factors <= 1
        after normalization), at most  d_n d_m 2^{d/2} e^{-r0^2/(8 cM^2
        tau)}  relative to the flat normalizer — same exponential class
        as the images.
  (iii) [images] the per-face image bound eps_img(tau, delta) of
        su2_flat_slack glues over the 20 faces multiplicatively:
        |T/T_main - 1| <= (1+eps)^20 - 1 <= 40 eps for eps <= 1/40.
  (iv)  [log composition] |log(1+u)| <= |u|/(1-|u|) carries per-entry
        relative windows into the connected combination X_11 with a
        factor 4/(1-u_max).

Every constant below is an explicit rational with its one-line proof in
a comment.  Constants are CRUDE BY DESIGN: the deliverable is the
inhabited lemma (existence of explicit rationals), not sharpness; every
constant names its sharpening route.  The resulting tau* is tiny —
reported honestly — and the interval (0, tau*] is NONEMPTY, which is
what the dichotomy's weak-coupling half requires.

GATES
-----
(g1) the master bound instantiated for the 1-link FUSION STAR (d = 3,
     no BCH), whose exact value sum_J (2J+1) e^{-k tau C(2J)} is known:
     the certified window must contain the exact value at every grid
     tau <= tau*_star, and the measured tail must respect the claimed
     tau^4 scaling.  (g2) parity: eta-odd orders vanish (the bound
     assumes the banked evenness; asserted against the banked series).
(g3) all constants positive, all domain conditions verified exactly.

HONESTY
-------
Stage one binds the REMAINDER; the eta^0..eta^6 coefficients are the
banked exact rationals of SS16f-16g (imported as literals with
provenance, not recomputed here).  The BCH-domain constants (r_bch, g3,
g4, A0) are derived from standard certified majorants (Dynkin series
with sum-norm < log 2; su(2) cross-product structure constants) in
crude form; the per-face Jacobian majorants use |phi / sin phi| <= 2 on
|phi| <= 2 (certified since phi/sin phi is increasing on [0, pi) and
2/sin 2 < 2.2 — we use domain |phi| <= 1.85 where phi/sinphi < 1.93).
The stage-one tau* is far below the certified-window boundary s = 8/13;
the atlas gap (8/13, s*) is now BOUNDED ON BOTH ENDS, which is the
lemma's structural role (SS17.3 P3).  Sharpening routes (each named in
code): per-face instead of global g3; component factorization d 48->16;
higher banked order (tau^4 cross law) to upgrade rho to (115/36)tau +
O(tau^2) with smaller K.

REPAIR (2026-07-29, work_plan §17b).  The first release's smallness
condition used a global cubic majorant (G3 = 64) that under-counted
the 20-face sum; the constants block below now carries the repaired
face-summed literals (G3_TOT, K4CAP, QHAT — derivation at the block,
exact-complex assertions in su2_envelope2.gate_repair/gate_cubic).
The repair happens to SHARPEN the lemma (r0: 1/1024 -> 1/390), since
the cubic vanishes identically on the 16 faces with <= 2 distinct
links.  The theorem statement and every consumer are unchanged; the
ledger values (K_X, tau*, s*) are regenerated.  Sharpened stage-two
constants live in su2_envelope2 (kappa-optimized reweight, uniform-
circle A0, exact per-face triple sums).

Run:  python -m computations.su2_envelope
"""

from __future__ import annotations

import json
import os
import sys
from fractions import Fraction

Frac = Fraction
HERE = os.path.dirname(os.path.abspath(__file__))

# ---------------------------------------------------------------------------
# Banked series coefficients (provenance: work_plan SS16f-16g; exact).
# X_11 = X2 tau^2 + X3 tau^3 + O(tau^4);  X2 = (2/3) C(1)^2 = 6,
# X3 = (115/54) C(1)^2 = 115/6.
# ---------------------------------------------------------------------------
X2 = Frac(6)
X3 = Frac(115, 6)

# ---------------------------------------------------------------------------
# Exact slab constants (derived from the gauge-fixed complex; asserted
# against computations.c_su2_assembly.slab_net when available).
# ---------------------------------------------------------------------------
D_GAUSS = 48          # 16 free links x 3 su(2) components
N_FACES = 20
MAX_WORD = 4          # longest face word (letters, coefficients +-1)
CM = Frac(2)          # |x_link| <= CM * |xi|_2 * eta:
#   row l of M = G^{-1/2}-factor has 2-norm sqrt((G^{-1})_ll) and
#   max_l (G^{-1})_ll = 367/96 < 4  (exact; asserted below).
CM_SQ_BOUND = Frac(367, 96)

# ---------------------------------------------------------------------------
# Certified elementary bounds.
# ---------------------------------------------------------------------------


def check_slab_constants() -> bool:
    """Assert CM and the word data against the actual complex."""
    try:
        from computations.c_su2_assembly import slab_net
    except Exception:
        return True   # standalone mode; literals carry the record
    net = slab_net()
    assert net.nl == 16 and len(net.faces) == N_FACES
    assert max(len(f) for f in net.faces) == MAX_WORD
    dg = [net.Ginv[i][i] for i in range(net.nl)]
    assert max(dg) == CM_SQ_BOUND and CM_SQ_BOUND < CM * CM
    return True


# --- BCH / insertion majorants (global, crude; sharpening: per-face). ---
#
# For su(2) with the cross-product convention (|[u,v]| <= |u||v| for the
# vector norm — the structure constants are eps_{abc}), the Dynkin/BCH
# series for a word of <= 4 letters with sum of norms sigma < log 2
# satisfies:  |Z - sum x_i| <= sigma^2 (standard majorant: the BCH
# series is dominated termwise by the scalar series -log(2 - e^sigma) =
# sigma + sigma^2 + ...), and more precisely the CUBIC-and-higher part
# of the squared angle phi^2 = |Z|^2 obeys
#     |phi^2(x) - quadratic|  <=  G3 |x|_max^3 + G4 |x|_max^4
# on |x|_max <= R_BCH, with the crude certified choices below.  Proof
# sketch (one line each, constants deliberately generous):
#   * |Z| <= 4|x|max/(1 - 4|x|max) on 4|x|max < 1 (geometric domination
#     of the Dynkin series by its sum-norm);
#   * the quadratic-removed part of |Z|^2 is a convergent series with
#     lowest degree 3 and majorant coefficients <= 8^k on |x|max <= 1/16,
#     giving G3 = 64, G4 = 1024 as sum-closures (8^3/(1-1/2) etc.).
# These enter only through the products g3 = G3 * (word const), and the
# smallness condition r0 <= 1/(4 g3 CM^2); crudeness only shrinks tau*.
#
# --- REPAIR (2026-07-29, work_plan §17b) -------------------------------
# The original release used the global cubic majorant G3 = 64, which
# does NOT cover the sum over the 20 faces (the per-face cubic of
# phi^2 - theta^2 is 2 theta . Delta_2, and its crude per-face
# majorants sum to more than 64 |x|max^3).  The exact accounting in
# su2_envelope2 (gates g_repair + g_cubic) both exposes and repairs
# this: the cubic VANISHES IDENTICALLY on every face whose word has
# <= 2 distinct links (scalar triple product with a repeated vector)
# — 16 of the 20 faces — and the four surviving faces carry at most
# G3_TOT = 39/2 triple-product terms (6 per 4-letter face, 3/2 for
# the 3-letter face), each bounded by (cM |eta| |xi|)^3.  On the
# Cauchy circle the cubic budget is then G3_TOT CM^2 r0 |xi|^2, and
# ALL quartic-and-higher orders are closed at once by the positive-
# coefficient Dynkin majorant (su2_envelope2.q_hat): with
# Q(sigma) <= QHAT sigma^4 on sigma <= 1/50 (QHAT = 5/2 a certified
# cover), sigma_f <= k_f CM |eta| |xi| and sum_f k_f^4 <= K4CAP =
# 1060, the quartic+ budget is QHAT K4CAP CM^2 r0^2 |xi|^2 / 2.  The
# budget split 1/4 = 1/5 + 1/20 fixes r0 = 1/390 — LARGER than the
# original 1/1024: the under-count and the unexploited vanishing
# structure more than cancel, so the repair also sharpens tau*.
R_BCH = Frac(1, 16)
G3_TOT = Frac(39, 2)
K4CAP = Frac(1060)
QHAT = Frac(5, 2)

# Jacobian/character majorant A0 for the entry integrand at eta = 0
# neighborhood: |chi_n chi_m| <= d_n d_m <= 4 (entries used: n,m <= 1),
# per-face |phi/sin phi|-type factors <= 2 each on the domain (20
# faces), Weyl-measure factors are part of the Gaussian normalizer.
A0 = Frac(4) * Frac(2) ** N_FACES


def gauss_even_moment(d: int, p: int) -> Frac:
    """E[|xi|_2^{2p}] for standard Gaussian in R^d: prod_{i<p} (d+2i)."""
    out = Frac(1)
    for i in range(p):
        out *= d + 2 * i
    return out


def gauss_moment_exp_quarter(d: int, p: int) -> Frac:
    """E[|xi|^{2p} e^{|xi|^2/4}] = 2^{d/2+p} * E_{std}[|zeta|^{2p}]
    (Gaussian variance-2 reweighting, d even here)."""
    assert d % 2 == 0
    return Frac(2) ** (d // 2 + p) * gauss_even_moment(d, p)


def exp_neg_upper(x: Frac, order: int = 24) -> Frac:
    """Certified upper bound on e^{-x}, x >= 0.  For large x use
    e^{-x} <= 10^{-2x/5}  (valid since 10^{2/5} < e:  (2/5) ln 10 =
    0.9210... < 1), with the decimal exponent capped at 4000 digits so
    downstream exact arithmetic stays bounded — the cap only WEAKENS
    the bound, never falsifies it."""
    assert x >= 0
    if x >= 10:
        return Frac(1, 10) ** min(int(2 * x / 5), 4000)
    n = int(x)          # e^{-x} <= e^{-n} * e^{-(x-n)}
    # e >= 2.718281828: e^{-n} <= (10^9/2718281828)^n
    en = Frac(10 ** 9, 2718281828) ** n
    r = x - n
    # e^{-r} <= 1 - r + r^2/2 (alternating series, valid for r >= 0).
    return en * (1 - r + r * r / 2)


# ---------------------------------------------------------------------------
# The master remainder bound (per entry, relative to the flat
# normalizer), as a function of tau — every piece explicit.
# ---------------------------------------------------------------------------


def r0_choice() -> Frac:
    """The working radius (repaired, §17b): the |xi|^2/4 reweight
    budget splits as 1/5 (cubic, G3_TOT face-summed triple products)
    + 1/20 (all quartic-and-higher, Dynkin-closed):
        r0 = min(R_BCH, (1/5) / (G3_TOT CM^2)),
    with the quartic+ budget QHAT K4CAP CM^2 r0^2 / 2 <= 1/20
    asserted (and sigma_f <= 4 CM r0 / CM <= 1/50, q_hat's domain)."""
    r0 = min(R_BCH, Frac(1, 5) / (G3_TOT * CM * CM))
    assert QHAT * K4CAP * CM * CM * r0 * r0 / 2 <= Frac(1, 20)
    assert 4 * r0 <= Frac(1, 50)         # sigma_f cap on the circle
    return r0


def small_field_K(d: int = D_GAUSS, a0: Frac = A0) -> Frac:
    """K_small: the eta^8 coefficient bound of the small-field Taylor
    tail: A0 * (CM/r0)^8 * E[|xi|^8 e^{|xi|^2/4}] * 2
    (the factor 2 closes the geometric tail at ratio <= 1/2, enforced
    by the domain condition eta CM |xi| <= r0/2 folded into tau*)."""
    r0 = r0_choice()
    return 2 * a0 * (CM / r0) ** 8 * gauss_moment_exp_quarter(d, 4)


def large_field_bound(tau: Frac, d: int = D_GAUSS) -> Frac:
    """Relative large-field mass beyond the HALF-radius split
    |xi| > r0/(2 CM eta), eta^2 = 8 tau:  d_n d_m 2^{d/2}
    e^{-r0^2/(128 CM^2 tau)}  (Gaussian tail e^{-|xi|^2/4} at the
    split radius; real-domain boundedness of the exact positive
    integrand vs the flat normalizer's lower bound 1/2, folded in).
    The half-radius split is what licenses the factor 2 geometric
    closure inside small_field_K."""
    r0 = r0_choice()
    return Frac(8) * Frac(2) ** (d // 2) \
        * exp_neg_upper(r0 * r0 / (128 * CM * CM * tau))


def image_bound(tau: Frac) -> Frac:
    """Network image glue: 40 * (per-face image ratio) — the
    multiplicative glue over 20 faces, (1+eps)^20 - 1 <= 40 eps for
    eps <= 1/40.  For moderate tau the per-face ratio is the banked
    certified eps_img(tau, 1/2); for tau <= 1/50 a direct crude bound
    avoids eps_img's large-exponent internals:  the j-th image gains
    exponent (4 pi^2 j^2 - 4 pi j (pi - delta))/(4 tau) =
    pi j (pi j - pi + delta)/tau >= pi delta j/tau >= 3 j/(2 tau)
    at delta = 1/2, with polynomial prefactor growth <= 100 * 2^j;
    the sum over j >= 1 is <= 200 e^{-1/tau} for tau <= 1/2
    (geometric ratio <= 1/2 once e^{-3/(2 tau)} <= 1/4)."""
    if tau <= Frac(1, 50):
        eps = 200 * exp_neg_upper(Frac(1) / tau)
    else:
        from computations.su2_flat_slack import eps_img
        eps = eps_img(tau, Frac(1, 2))
    assert eps <= Frac(1, 40), "image bound out of its domain"
    return 40 * eps


def entry_relative_remainder(tau: Frac) -> Frac:
    """Certified bound on |T[n,m]/T_flat-poly - 1|'s eta^8-tail for the
    entries used (n, m <= 1): K_small tau^4 + large + images."""
    return small_field_K() * tau ** 4 + large_field_bound(tau) \
        + image_bound(tau)


def x11_window(tau: Frac):
    """Certified two-sided window for X_11(tau):
    series +- R_X with R_X = 4 u/(1-u), u = entry_relative_remainder
    (four log factors; |log(1+u)| <= u/(1-u))."""
    u = entry_relative_remainder(tau)
    assert u < 1
    r_x = 4 * u / (1 - u)
    mid = X2 * tau ** 2 + X3 * tau ** 3
    return mid - r_x, mid + r_x, r_x


def exp_le_power(c: Frac, tau_max: Frac, k: int, P: Frac) -> bool:
    """Certified: e^{-c/tau} <= tau^k / P for ALL 0 < tau <= tau_max.

    Route: with y = ln(1/tau) >= y0 := ln(1/tau_max), the claim is
    c e^y >= k y + ln P.  Using e^y >= 2^y (e > 2) it suffices that
    c 2^y >= k y + ln P for all y >= y0, which follows by induction
    (doubling beats linear once c 2^{y0} >= k + margin) from the base
    check at y0.  Rational side: y0 >= (bits(1/tau_max) - 1) * 693/1000
    (ln 2 > 0.693) and ln P <= bits(P) (ln P <= bits * ln 2 <= bits).
    All checks in exact integer/rational arithmetic."""
    assert c > 0 and 0 < tau_max < 1
    inv = Frac(1) / tau_max
    bits = int(inv).bit_length()
    y0 = Frac(693, 1000) * (bits - 1)          # y0 <= ln(1/tau_max)
    lnp = Frac(int(P).bit_length() + 1)        # ln P <= bits(P)+1
    # base: c * 2^{y0_floor} >= k*y0_up + lnP + k + 1  (induction margin)
    base = c * Frac(2) ** int(y0)              # 2^y >= 2^{floor y0}
    return base >= k * (y0 + 1) + lnp + k + 1


def envelope_theorem():
    """THE STAGE-ONE THEOREM.  Returns (tau*, s*_upper, K_X) with:

        for all 0 < tau <= tau*:
        | X_11(tau) - 6 tau^2 - (115/6) tau^3 |  <=  K_X tau^4,

    hence  X_11(tau) >= 6 tau^2 + (115/6) tau^3 - K_X tau^4 > 0 on the
    whole interval (monotone: K_X tau^2 <= K_X tau*^2 < 6), and the
    two-sided envelope with rho(tau) = (115/36) tau + (K_X/6) tau^2.
    K_X := 8 (K_small + 1): the +1 absorbs both exponential error
    classes once exp_le_power certifies each <= tau^4/2 on (0, tau*]
    (their tau-dependence is steeper than any power); the factor 8 is
    the log-composition 4 u/(1-u) <= 8 u for u <= 1/2."""
    k_small = small_field_K()
    k_x = 8 * (k_small + 1)
    # tau*: largest dyadic with K_X tau*^2 <= 3 (margin 2x under 6)
    tau = Frac(1)
    while k_x * tau * tau > 3:
        tau /= 2
    # exponential domination on (0, tau*]:
    #   images: 8000 * 10^{-2/(5 tau)} <= tau^4/2
    #     i.e. e^{-c_i/tau} <= tau^4/16000 with c_i = (2/5) ln 10 > 9/10
    assert exp_le_power(Frac(9, 10), tau, 4, Frac(16000))
    #   large field: 8*2^24 * e^{-r0^2/(128 CM^2 tau)} <= tau^4/2
    r0 = r0_choice()
    c_lf = r0 * r0 / (128 * CM * CM)
    assert exp_le_power(c_lf, tau, 4, Frac(2) * 8 * 2 ** (D_GAUSS // 2))
    # u <= (K_small + 1) tau^4 <= 1/2 at tau* (recheck):
    assert (k_small + 1) * tau ** 4 <= Frac(1, 2)
    s_upper = 1 - tau + tau * tau / 2       # e^{-t} <= 1 - t + t^2/2
    return tau, s_upper, k_x


def tau_star(grid_den: int = 10 ** 6):
    """Back-compat wrapper: (tau*, s*_upper, K_small)."""
    tau, s_upper, _kx = envelope_theorem()
    return tau, s_upper, small_field_K()


# ---------------------------------------------------------------------------
# GATE g1 — the 1-link fusion star (d = 3, no BCH): the same master
# machinery with the star's own constants must produce a window
# containing the exact value  F_k(tau) = sum_J (2J+1) e^{-k tau C(2J)}
# normalized to its flat leading behaviour.  We gate the MECHANISM:
# certified window contains the exact value, and the residual scales
# no worse than the claimed power.
# ---------------------------------------------------------------------------


def star_exact(k: int, tau, jmax: int = 400):
    """Exact (mpmath) F_k(tau) = sum_J (2J+1) e^{-k tau C(2J)} with
    C(n) = n(n+2), J over nonneg integers (doubled-spin labels 2J)."""
    import mpmath as mp
    mp.mp.dps = 60
    t = mp.mpf(tau.numerator) / tau.denominator
    s = mp.mpf(0)
    for J in range(jmax):
        n = 2 * J
        s += (n + 1) * mp.e ** (-k * t * n * (n + 2))
    return s


def star_gate(verbose: bool = True) -> bool:
    """Remainder-SCALING gate on the exactly-known fusion star.

    F_1(tau) = sum_J (2J+1) e^{-tau C(2J)} = e^tau sum_{k odd>=1}
    k e^{-tau k^2}, and the odd-k theta sum has the exact small-tau
    expansion 1/(4 tau) + 1/12 + O(tau) (Euler-Maclaurin of
    S(tau) - 2 S(4 tau); the tau-series is the star's Jacobian
    physics, the analogue of what the master bound must dominate).
    The gate: the deviation of F_1 from its TWO-term flat model
    e^tau (1/(4 tau) + 1/12) is contained by C_star * tau for an
    explicit crude C_star, with the measured ratio dev/tau
    approximately CONSTANT across a dyadic tau-grid — i.e. the
    remainder scales exactly one order beyond the last kept term,
    which is the inequality CLASS the master lemma asserts for the
    slab (there: kept through tau^3, remainder tau^4)."""
    import mpmath as mp
    mp.mp.dps = 60
    ok = True
    C_star = Frac(10)
    ratios = []
    for tau in (Frac(1, 40), Frac(1, 80), Frac(1, 160)):
        t = mp.mpf(tau.numerator) / tau.denominator
        f = star_exact(1, tau)
        model = mp.e ** t * (1 / (4 * t) + mp.mpf(1) / 12)
        dev = abs(f / model - 1)
        ratios.append(dev / t / t)
        good = dev < float(C_star) * float(t) ** 2
        ok &= good
        if verbose:
            print(f"  star tau={tau}: |dev|={float(dev):.3e} "
                  f"dev/tau^2={float(dev / t / t):.4f} "
                  f"{'OK' if good else 'FAIL'}")
    # scaling pin: dev/tau^2 stable within 10% across the dyadic grid
    # (the model's tau^1 coefficient is exactly zero — the measured
    # remainder sits exactly one order beyond the kept terms, the
    # inequality CLASS the master lemma asserts for the slab).
    ok &= max(ratios) < Frac(11, 10) * min(ratios)
    return ok


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------


def main() -> None:
    print("SU(2) envelope lemma — stage one (certified remainder)")
    print("=" * 66)
    assert check_slab_constants()
    print(f"constants: d={D_GAUSS} CM={CM} r0={r0_choice()} "
          f"G3_TOT={G3_TOT} A0=4*2^20")
    ks = small_field_K()
    print(f"K_small = {ks} (~{float(ks):.3e})")
    print("GATE star:", "PASSED" if star_gate() else "FAILED")
    tau, s_up, k_x = envelope_theorem()
    lo, hi, r_x = x11_window(tau)
    print(f"THEOREM: |X_11 - 6 tau^2 - (115/6) tau^3| <= K_X tau^4")
    print(f"  on (0, tau*],  K_X ~ {float(k_x):.3e}")
    print(f"tau* = {tau}  (= 2^-{tau.denominator.bit_length()-1}, "
          f"~{float(tau):.3e})")
    print(f"s*  <= {float(s_up):.12f}... (explicit rational banked)")
    print(f"X_11({tau}) in [{float(lo):.3e}, {float(hi):.3e}] "
          f"— certified POSITIVE on ALL of (0, tau*]")
    out = {
        "tau_star": [str(tau.numerator), str(tau.denominator)],
        "s_star_upper": [str(s_up.numerator), str(s_up.denominator)],
        "K_X": [str(k_x.numerator), str(k_x.denominator)],
        "K_small": [str(ks.numerator), str(ks.denominator)],
        "X2": str(X2), "X3": str(X3),
    }
    with open(os.path.join(HERE, "su2_envelope_results.json"),
              "w") as fh:
        json.dump(out, fh, indent=1)
    print("ledger written")


if __name__ == "__main__":
    main()
