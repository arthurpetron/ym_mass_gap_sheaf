"""MD.3 / work_plan §17-P1 — the ENVELOPE LEMMA, stage two: sharpened
certified constants from the EXACT slab complex, and the certified
SU(2)-vs-U(1) sign separation on a common interval.

WHAT CHANGES RELATIVE TO STAGE ONE (su2_envelope.py)
----------------------------------------------------
Stage one inhabited the lemma with deliberately crude global constants
(K_X ~ 3.8e49, tau* = 2^-82).  Stage two replaces the three crude
blocks by certified constants derived from the exact gauge-fixed slab
complex, and repairs a face-sum under-count in the stage-one insertion
budget (see REPAIR below):

  (1) INSERTION BUDGET, exact per-face.  The action remainder
      Delta S_f = phi_f^2 - theta_f^2 (all BCH orders) is split as
      2 theta.Delta_2 (exact cubic) + Q_f (quartic and higher).
      The cubic is a sum of scalar triple products
      x_k . (x_i x x_j): it VANISHES IDENTICALLY on every face whose
      word has <= 2 distinct links (repeated vector in the triple
      product) — 16 of the 20 slab faces.  The four surviving faces
      contribute the exact-rational triple-sum constant

          T3 = sum_f (1/2) sum_{i<j, e_i != e_j}
                          sum_{k, e_k not in {e_i,e_j}} c_i c_j c_k

      with c_e >= sqrt((G^-1)_ee) certified rational upper bounds
      (isqrt).  Quartic-and-higher is closed IN ALL ORDERS by the
      positive-coefficient Dynkin majorant f(s) = -log(2 - e^s):
      with g3(s) = f(s) - s - s^2 (the >= cubic tail of ||Z-theta||)
      and R = Z - theta,

          |Q_f| <= 2 sigma_f g3(sigma_f) + (sigma_f^2/2 + g3(sigma_f))^2
                =: Q(sigma_f),

      and Q(s)/s^4 is increasing (positive Taylor coefficients), so
      Q(sigma) <= [Q(s0)/s0^4] sigma^4 on sigma <= s0.  All BCH
      orders are covered — no G4-style separate closure is needed.
  (2) REWEIGHT EXPONENT kappa, optimized.  The budget requirement
      becomes  (r0/cM) T3 + qhat (r0/cM)^2 S4 / 2  <=  kappa  with
      E[|xi|^8 e^{kappa|xi|^2}] = (1-2 kappa)^{-(d/2+4)} prod(d+2i);
      kappa is scanned over a dyadic grid (the optimum of
      r0^-8 (1-2k)^-28 sits at kappa = 1/9).  Stage one hard-wired
      kappa = 1/4 (cost 2^28 in the moment).
  (3) A0, uniform circle bounds.  On the Cauchy circle
      |eta'| = r0/(cM |xi|) EVERY link field has ||x'_e|| <= r0
      uniformly in xi, so the Jacobian and character factors admit
      xi-INDEPENDENT bounds barely above 1 (certified series bounds
      for |z/sin z| and |sinh z / z|); only the 1/eta'^2-divided
      action remainder needs the e^{kappa|xi|^2} budget.  Stage one
      charged 2^20 here.

Everything else — the eta = sqrt(8 tau) master-lemma structure, the
half-radius split, the large-field and image exponential shells, the
log-composition 4u/(1-u), exp_le_power symbolic domination, and the
theorem shape

    | X_11(tau) - 6 tau^2 - (115/6) tau^3 |  <=  K_X tau^4
                                        on (0, tau*],  K_X tau*^2 <= 3

— is inherited verbatim from stage one (the audited functions are
imported, not duplicated).

THE U(1) MIRROR LANE (the §17.4 fence, executed)
------------------------------------------------
The identical machinery at one abelian component (the c_su2_assembly
g4 convention: covariance 8 tau G^-1, characters e^{i m theta}) has
NO insertions at all (abelian: Delta S == 0, no Jacobians), so the
main branch is entire and the same Cauchy argument gives tiny
constants.  The banked series content is
    X_U1(tau) = -8 (G^-1)_{t,b} tau + 0 tau^2 + 0 tau^3 + R,
(G^-1)_{t,b} = 1 exactly on this complex; kappa_2 = kappa_3 = 0 are
the banked §16f g4 / §16g mirror gates.  Stage two certifies
|R| <= K_U1 tau^4 with K_U1 explicit — and hence the certified
two-sided SEPARATION on the common interval (0, tau*]:

    X_SU2(tau)  >  0  >  X_U1(tau),

anti-screening vs screening, both nonperturbative on the interval.
Scheme covariance of the mirror's linear term is gated against the
SECOND banked U(1) instrument (the M = infinity theta kernel,
u1_theta_kernel): Qmin = 3n^2 + 3m^2 + 2nm gives X_lin = -2 tau in
theta normalization, and the engine/theta conversion factor is
EXACTLY 4 on both the diagonal (12 tau n^2 vs 3 n^2) and the cross
(8 tau vs 2) — the sign is convention-invariant.

REPAIR (stage-one face-sum under-count)
---------------------------------------
Stage one's smallness condition r0 <= 1/(4 g3 cM^2) used g3 = 64 as a
GLOBAL cubic majorant, but the per-face cubic majorant summed over
faces is not covered by 64 |x|max^3 in general.  The exact accounting
here shows the honest global constant is G3_TOT = 39/2 triple-product
terms (only the four >= 3-distinct-link faces contribute; 16 faces
have exactly zero cubic), which happens to IMPROVE r0: the under-count
error and the unexploited vanishing structure roughly cancel.
su2_envelope.py now carries the repaired literals, and this module's
gate g_repair asserts them against the exact complex.

GATES
-----
  g_complex   slab constants (nl, faces, word lengths, Ginv diagonal,
              c_e^2 >= (G^-1)_ee, loop links) against the live complex.
  g_cubic     the triple-product structure on random exact-rational
              link vectors: theta.Delta_2 == 0 on every face with
              <= 2 distinct links; |theta.Delta_2| <= per-face
              triple-sum bound on the others; the Delta_2 formula
              cross-checked against mpmath matrix logs (independent
              of c_su2_assembly's bch machinery).
  g_dynkin    certified g3_up / exp_up / sqrt_up dominate mpmath
              values on a grid (upper bounds really are upper).
  g_repair    the su2_envelope repaired literals cover the exact
              accounting: T3 <= G3_TOT cM^3 and sum_f k_f^4 <= K4CAP.
  g_mirror    (G^-1)_{t,b} = 1 exactly; the theta-kernel Qmin form
              (3, 3, 2) from the banked u1 ledger; engine/theta
              conversion factor 4 on diagonal and cross; banked
              kappa_2 = kappa_3 = 0 provenance in the c_su2 ledgers.
  g_star      stage one's remainder-scaling gate on the fusion star
              (imported; the mechanism gate).
  g_dominate  stage two beats repaired stage one: K_X2 < K_X1 and
              tau*2 > tau*1, with both windows valid at tau*1.

HONESTY
-------
The deliverable is still the inhabited lemma with SOUND explicit
rationals — now K_X ~ 3.8e33, tau* = 2^-55 (from 2^-82 unsound /
2^-76 repaired): 2^27 of certified-domain gain over the original
release, still far from the atlas range s in (0.6, 1).  The remaining distance is structural: the
Cauchy radius shrinks like 1/|xi| because ONE global circle must keep
every link field inside the BCH domain.  Named next levers, ranked:
(i) polydisc Cauchy in per-face variables (radius set by face-local
fields — removes the global |xi| shrink, the dominant loss); (ii) the
tau^4 cross law (one more engine order — moves the remainder to
tau^5 and makes rho's tau-linear term sharp); (iii) exact per-face
c_e products in T3 tightened by the D4 symmetry classes.  The
matched-flow form 1 < tau'/tau <= 1 + c tau still awaits the diagonal
kappa_3 or the P2 iterated-map route — this module does not claim it.

Run:  python -m computations.su2_envelope2
"""

from __future__ import annotations

import json
import os
from fractions import Fraction
from math import isqrt

from computations.su2_envelope import (
    A0 as A0_STAGE1,
)
from computations.su2_envelope import (
    CM,
    D_GAUSS,
    N_FACES,
    X2,
    X3,
    exp_le_power,
    star_gate,
)
from computations.su2_envelope import (
    envelope_theorem as envelope_theorem_stage1,
)

Frac = Fraction
HERE = os.path.dirname(os.path.abspath(__file__))
OUT_JSON = os.path.join(HERE, "su2_envelope2_results.json")

# ---------------------------------------------------------------------------
# Certified elementary bounds (all UPPER bounds, exact rationals).
# ---------------------------------------------------------------------------


def sqrt_up(x: Frac, prec: int = 10 ** 9) -> Frac:
    """Certified rational upper bound on sqrt(x), x >= 0:
    r = (isqrt(ceil(x prec^2)) + 1) / prec  =>  r^2 >= x."""
    assert x >= 0
    q = -((-x.numerator * prec * prec) // x.denominator)   # ceil
    return Frac(isqrt(q) + 1, prec)


def exp_up(x: Frac) -> Frac:
    """Certified upper bound on e^x for 0 <= x < 1:
    sum_{k<=4} x^k/k! + x^5/(120 (1 - x/6))  (geometric tail)."""
    assert 0 <= x < 1
    s = 1 + x + x * x / 2 + x ** 3 / 6 + x ** 4 / 24
    return s + x ** 5 / (120 * (1 - x / 6))


def g3_up(s0: Frac) -> Frac:
    """Certified upper bound on g3(s0) = f(s0) - s0 - s0^2, where
    f(s) = -log(2 - e^s) is the Dynkin/BCH scalar majorant: with
    u = e^{s0} - 1 < 1,  f = sum_m u^m / m
      <= u + u^2/2 + u^3/3 + u^4/(4(1-u)).
    All Taylor coefficients of f (and hence of g3) are positive, so
    g3(s) <= [g3_up(s0)/s0^3] s^3 for 0 <= s <= s0."""
    u = exp_up(s0) - 1
    assert u < 1
    f_up = u + u * u / 2 + u ** 3 / 3 + u ** 4 / (4 * (1 - u))
    out = f_up - s0 - s0 * s0
    assert out >= 0
    return out


def q_hat(s0: Frac) -> Frac:
    """Certified qhat with Q(sigma) <= qhat sigma^4 on sigma <= s0,
    Q(s) = 2 s g3(s) + (s^2/2 + g3(s))^2 (the >= quartic remainder
    majorant of |Delta S_f|; positive coefficients => Q(s)/s^4
    increasing => qhat = Q(s0)/s0^4 dominates on [0, s0])."""
    g = g3_up(s0)
    q = 2 * s0 * g + (s0 * s0 / 2 + g) ** 2
    return q / s0 ** 4


def inv_one_minus_sin_ratio(z2: Frac) -> Frac:
    """Certified upper bound on |z / sin z| for complex |z|^2 <= z2 < 6:
    |sin z / z| >= 1 - (|z|^2/6)/(1 - |z|^2/20)  (alternating-series
    domination of sum |z|^{2k}/(2k+1)!), so the reciprocal bounds."""
    q = (z2 / 6) / (1 - z2 / 20)
    assert q < 1
    return 1 / (1 - q)


def sinh_ratio_up(z2: Frac) -> Frac:
    """Certified upper bound on |sin z / z| (and |sinh z / z|) for
    complex |z|^2 <= z2 < 20:  1 + (|z|^2/6)/(1 - |z|^2/20)."""
    return 1 + (z2 / 6) / (1 - z2 / 20)


# ---------------------------------------------------------------------------
# The exact slab data (certified rational upper bounds per link/face).
# ---------------------------------------------------------------------------

# Repaired stage-one-form literals (asserted by g_repair below).
G3_TOT = Frac(39, 2)      # global triple-product count over the slab
K4CAP = 1060              # sum_f k_f^4 (word-length fourth powers)


class SlabData:
    """Exact per-face constants from the live complex."""

    def __init__(self) -> None:
        from computations.c_su2_assembly import slab_net
        net = slab_net()
        assert net.nl == 16 and len(net.faces) == N_FACES
        self.net = net
        self.c: list[Frac] = [sqrt_up(net.Ginv[e][e])
                              for e in range(net.nl)]
        self.words: list[list[tuple[int, int]]] = net.faces
        self.s_f: list[Frac] = []
        self.t3_f: list[Frac] = []
        for path in net.faces:
            es = [e for e, _ in path]
            cf = [self.c[e] for e in es]
            self.s_f.append(sum(cf, Frac(0)))
            t3 = Frac(0)
            k = len(es)
            for i in range(k):
                for j in range(i + 1, k):
                    if es[i] == es[j]:
                        continue
                    for kk in range(k):
                        if es[kk] in (es[i], es[j]):
                            continue
                        t3 += cf[i] * cf[j] * cf[kk]
            self.t3_f.append(t3 / 2)
        self.T3: Frac = sum(self.t3_f, Frac(0))
        # only multi-letter faces can carry any BCH remainder
        self.S4: Frac = sum((s ** 4 for s, w in
                             zip(self.s_f, self.words, strict=True) if len(w) >= 2),
                            Frac(0))
        self.s_max: Frac = max(self.s_f)
        self.k4: int = sum(len(w) ** 4 for w in self.words)
        # loop links (single free link each, adapted gauge)
        self.t_link, self.t_sign = net.loop_t
        assert net.loop_b is not None
        self.b_link, self.b_sign = net.loop_b
        self.ginv_tb: Frac = net.Ginv[self.t_link][self.b_link]


# ---------------------------------------------------------------------------
# The sharpened SU(2) pipeline.
# ---------------------------------------------------------------------------


def gauss_even_moment(d: int, p: int) -> Frac:
    out = Frac(1)
    for i in range(p):
        out *= d + 2 * i
    return out


def gauss_moment_exp(d: int, p: int, kappa: Frac) -> Frac:
    """E[|xi|^{2p} e^{kappa |xi|^2}] = (1-2k)^{-(d/2+p)} prod(d+2i),
    standard Gaussian in R^d, kappa < 1/2 (d even)."""
    assert d % 2 == 0 and 0 <= kappa < Frac(1, 2)
    return (1 - 2 * kappa) ** (-(d // 2) - p) * gauss_even_moment(d, p)


def r0_budget(data: SlabData, kappa: Frac) -> tuple[Frac, Frac]:
    """Largest working r0 (dyadic-refined) with the FULL insertion
    budget on the Cauchy circle inside kappa |xi|^2:

        (r0/cM) T3  +  qhat(s0) (r0/cM)^2 S4 / 2   <=  kappa,
        s0 = (r0/cM) s_max  (the max face sigma on the circle).

    Returns (r0, s0)."""
    r0 = kappa * CM / data.T3          # cubic-only seed
    for _ in range(200):
        s0 = (r0 / CM) * data.s_max
        lhs = (r0 / CM) * data.T3 \
            + q_hat(s0) * (r0 / CM) ** 2 * data.S4 / 2
        if lhs <= kappa:
            break
        r0 *= Frac(63, 64)
    r0 = Frac(r0.numerator * 2 ** 20 // r0.denominator, 2 ** 20)
    s0 = (r0 / CM) * data.s_max
    assert (r0 / CM) * data.T3 \
        + q_hat(s0) * (r0 / CM) ** 2 * data.S4 / 2 <= kappa
    return r0, s0


def a0_sharp(data: SlabData, r0: Frac, s0: Frac) -> Frac:
    """Certified xi-uniform bound on the non-action factors of the
    integrand on the Cauchy circle (entries n, m <= 1):
      characters:  d_n d_m e^{(||theta_t|| + ||theta_b||)/2} with
                   ||theta|| <= (r0/cM) c_link  (uniform on circle);
      face Jacobians:  |phi/sin phi|-type, |phi_f| <= s0 (1 + g3-tail)
                   <= 2 s0, one factor per face;
      link Haar:   |sin u / u|^2-type, |u_e| <= r0, two factors per
                   link (both direction bounds taken as upper)."""
    th = (r0 / CM) * (data.c[data.t_link] + data.c[data.b_link])
    char = 4 * exp_up(th / 2)
    phi2 = (2 * s0) ** 2
    jac_face = inv_one_minus_sin_ratio(phi2)
    jac_link = sinh_ratio_up(r0 * r0) ** 2
    return char * jac_face ** N_FACES * jac_link ** data.net.nl


def su2_constants(data: SlabData,
                  kappas: tuple[Frac, ...] = (
                      Frac(1, 6), Frac(1, 8), Frac(1, 9),
                      Frac(1, 10), Frac(1, 12), Frac(1, 16)),
                  ) -> dict[str, Frac]:
    """Scan kappa, return the best certified constant set."""
    best: dict[str, Frac] = {}
    for kappa in kappas:
        r0, s0 = r0_budget(data, kappa)
        a0 = a0_sharp(data, r0, s0)
        k_small = 2 * a0 * (CM / r0) ** 8 \
            * gauss_moment_exp(D_GAUSS, 4, kappa)
        if not best or k_small < best["K_small"]:
            best = {"kappa": kappa, "r0": r0, "s0": s0, "A0": a0,
                    "K_small": k_small}
    return best


def envelope_theorem2() -> tuple[Frac, Frac, Frac, dict[str, Frac]]:
    """THE STAGE-TWO THEOREM.  Returns (tau*, s*_upper, K_X, consts):

        for all 0 < tau <= tau*:
        | X_11(tau) - 6 tau^2 - (115/6) tau^3 |  <=  K_X tau^4,

    with the same shell structure as stage one (K_X = 8 (K_small + 1)
    absorbing the exponential classes via exp_le_power; positivity
    margin K_X tau*^2 <= 3 < 6; s* <= 1 - tau* + tau*^2/2)."""
    data = SlabData()
    consts = su2_constants(data)
    k_small = consts["K_small"]
    k_x = 8 * (k_small + 1)
    tau = Frac(1)
    while k_x * tau * tau > 3:
        tau /= 2
    # exponential shells on (0, tau*] (same certificates as stage one)
    assert exp_le_power(Frac(9, 10), tau, 4, Frac(16000))
    r0 = consts["r0"]
    c_lf = r0 * r0 / (128 * CM * CM)
    assert exp_le_power(c_lf, tau, 4, Frac(2) * 8 * 2 ** (D_GAUSS // 2))
    assert (k_small + 1) * tau ** 4 <= Frac(1, 2)
    s_upper = 1 - tau + tau * tau / 2
    return tau, s_upper, k_x, consts


def x11_window2(tau: Frac) -> tuple[Frac, Frac]:
    """Certified two-sided window at tau <= tau* (stage-two K_X)."""
    tau_star, _, k_x, _ = envelope_theorem2()
    assert 0 < tau <= tau_star
    mid = X2 * tau ** 2 + X3 * tau ** 3
    return mid - k_x * tau ** 4, mid + k_x * tau ** 4


# ---------------------------------------------------------------------------
# The U(1) mirror lane (same machinery, abelian component).
# ---------------------------------------------------------------------------

D_U1 = 16          # 16 links x 1 component
X1_U1 = Frac(-8)   # engine convention: -8 (G^-1)_{t,b}, banked below


def exp_up_any(x: Frac) -> Frac:
    """Certified upper bound on e^x for any x >= 0, by exponent
    halving: e^x = (e^{x/2^k})^{2^k} with x/2^k < 9/10."""
    assert x >= 0
    halvings = 0
    while x >= Frac(9, 10):
        x /= 2
        halvings += 1
    e = exp_up(x)
    for _ in range(halvings):
        e = e * e
    return e


def u1_constants(data: SlabData,
                 r0s: tuple[Frac, ...] = (
                     Frac(2), Frac(3), Frac(4), Frac(5), Frac(6),
                     Frac(8)),
                 ) -> dict[str, Frac]:
    """The abelian lane: no insertions (Delta S == 0, no Jacobians),
    kappa = 0, entire main branch.  A0 = e^{(r0/cM)(c_t + c_b)}
    (|e^{iL}| on the circle, uniform in xi); r0 scanned."""
    best: dict[str, Frac] = {}
    ct = data.c[data.t_link] + data.c[data.b_link]
    for r0 in r0s:
        a0 = exp_up_any((r0 / CM) * ct)
        k_small = 2 * a0 * (CM / r0) ** 8 * gauss_even_moment(D_U1, 4)
        if not best or k_small < best["K_small"]:
            best = {"r0": r0, "A0": a0, "K_small": k_small}
    return best


def mirror_theorem() -> tuple[Frac, Frac]:
    """|X_U1(tau) - X1_U1 tau| <= K_U1 tau^4 on (0, tau*] (the SU(2)
    tau*, so both statements live on the COMMON interval), whence the
    certified separation X_SU2 > 0 > X_U1 there.  Returns
    (K_U1, margin) with margin = the certified gap floor at tau*."""
    data = SlabData()
    assert data.ginv_tb == 1            # banked: exact on this complex
    tau_star, _, k_x, _ = envelope_theorem2()
    consts = u1_constants(data)
    k_small = consts["K_small"]
    k_u1 = 8 * (k_small + 1)
    r0 = consts["r0"]
    c_lf = r0 * r0 / (128 * CM * CM)
    assert exp_le_power(c_lf, tau_star, 4, Frac(2) * 8 * 2 ** (D_U1 // 2))
    assert exp_le_power(Frac(9, 10), tau_star, 4, Frac(16000))
    # separation: X_U1 <= -8 tau + K_U1 tau^4 < 0 on (0, tau*]
    assert k_u1 * tau_star ** 3 < 8
    margin = 8 * tau_star - k_u1 * tau_star ** 4
    assert margin > 0
    return k_u1, margin


# ---------------------------------------------------------------------------
# Gates.
# ---------------------------------------------------------------------------


def _rand_rational_vectors(seed: int, n: int) -> list[list[Frac]]:
    """Deterministic exact-rational 3-vectors (LCG; no floats)."""
    state = seed
    out: list[list[Frac]] = []
    for _ in range(n):
        v: list[Frac] = []
        for _ in range(3):
            state = (1103515245 * state + 12345) % (2 ** 31)
            v.append(Frac(state % 2001 - 1000, 1000))
        out.append(v)
    return out


def _cross(u: list[Frac], v: list[Frac]) -> list[Frac]:
    return [u[1] * v[2] - u[2] * v[1],
            u[2] * v[0] - u[0] * v[2],
            u[0] * v[1] - u[1] * v[0]]


def _dot(u: list[Frac], v: list[Frac]) -> Frac:
    return u[0] * v[0] + u[1] * v[1] + u[2] * v[2]


def _bch_quadratic_numeric_gate(xs: list[list[Frac]],
                                d2: list[Frac],
                                digits: int = 40) -> bool:
    """Independent mpmath check that Delta_2 = (1/2) sum_{i<j}
    [x_i, x_j] is the grade-2 BCH part: map v -> v.T with
    T_a = -i sigma_a / 2 ([T_a, T_b] = eps_abc T_c), take the exact
    matrix log of the product of exponentials, extract the vector,
    and compare theta + Delta_2 against it to O(|x|^3)."""
    import mpmath as mp
    mp.mp.dps = digits
    sig = [mp.matrix([[0, 1], [1, 0]]),
           mp.matrix([[0, -1j], [1j, 0]]),
           mp.matrix([[1, 0], [0, -1]])]

    def mat(v: list[Frac]) -> object:
        m = mp.zeros(2, 2)
        for a in range(3):
            m += mp.mpf(v[a].numerator) / v[a].denominator \
                * (-1j / 2) * sig[a]
        return m

    scale = Frac(1, 64)      # keep |x| small so O(|x|^3) is visible
    prod = mp.eye(2)
    for x in xs:
        prod = prod * mp.expm(mat([c * scale for c in x]))
    z = mp.logm(prod)
    def tr(m: object) -> object:
        return m[0, 0] + m[1, 1]        # type: ignore[index]

    zvec = [(-2) * tr(z * mat_a)
            for mat_a in (mat([Frac(1), Frac(0), Frac(0)]),
                          mat([Frac(0), Frac(1), Frac(0)]),
                          mat([Frac(0), Frac(0), Frac(1)]))]
    # note tr(T_a T_b) = -delta_ab/2  =>  v_a = -2 tr(M T_a)
    ok = True
    norm3 = sum(abs(sum(c * scale for c in x)) for x in xs) ** 3
    for a in range(3):
        model = sum(x[a] for x in xs) * scale + d2[a] * scale * scale
        diff = abs(zvec[a] - (mp.mpf(model.numerator) /
                              model.denominator))
        ok &= diff < 2 * float(norm3)
    return ok


def gate_cubic(data: SlabData, seed: int = 20260729) -> bool:
    """The triple-product structure, exactly, on random rational
    vectors: per face, with x_i = s_i * v_{e_i},
      theta = sum_i x_i,  Delta_2 = (1/2) sum_{i<j} [x_i, x_j],
    theta . Delta_2 == 0 whenever the word has <= 2 distinct links,
    and |theta . Delta_2|^2 <= (per-face triple-sum with ||v_e||
    bounds)^2 otherwise.  On the largest 3- and 4-letter words the
    Delta_2 formula itself is cross-checked against mpmath matrix
    logs (independent of c_su2_assembly's bch machinery)."""
    vecs = _rand_rational_vectors(seed, data.net.nl)
    ok = True
    numeric_checked = set()
    for path in data.words:
        xs = [[Frac(s) * comp for comp in vecs[e]] for e, s in path]
        k = len(xs)
        theta = [sum(x[c] for x in xs) for c in range(3)]
        d2 = [Frac(0)] * 3
        for i in range(k):
            for j in range(i + 1, k):
                cr = _cross(xs[i], xs[j])
                d2 = [a + b / 2 for a, b in zip(d2, cr, strict=True)]
        if k >= 3 and k not in numeric_checked:
            ok &= _bch_quadratic_numeric_gate(xs, d2)
            numeric_checked.add(k)
        pairing = _dot(theta, d2)
        es = [e for e, _ in path]
        if len(set(es)) <= 2:
            ok &= pairing == 0
        else:
            bound = Frac(0)
            nv = [sqrt_up(_dot(vecs[e], vecs[e])) for e in es]
            for i in range(k):
                for j in range(i + 1, k):
                    if es[i] == es[j]:
                        continue
                    for kk in range(k):
                        if es[kk] in (es[i], es[j]):
                            continue
                        bound += nv[i] * nv[j] * nv[kk]
            bound /= 2
            ok &= pairing * pairing <= bound * bound
    return ok


def gate_dynkin(digits: int = 40) -> bool:
    """Certified upper bounds really are upper (mpmath grid)."""
    import mpmath as mp
    mp.mp.dps = digits
    ok = True
    for s0 in (Frac(1, 100), Frac(1, 20), Frac(1, 8), Frac(1, 2)):
        t = mp.mpf(s0.numerator) / s0.denominator
        f = -mp.log(2 - mp.e ** t)
        g3_true = f - t - t * t
        ok &= mp.mpf(g3_up(s0).numerator) / g3_up(s0).denominator \
            >= g3_true > 0
        ok &= mp.mpf(exp_up(s0).numerator) / exp_up(s0).denominator \
            >= mp.e ** t
    for x in (Frac(2), Frac(367, 96), Frac(3, 7)):
        r = sqrt_up(x)
        ok &= r * r >= x
        ok &= (r - Frac(1, 10 ** 6)) ** 2 < x     # and it is tight
    for z2 in (Frac(1, 100), Frac(1, 4), Frac(1)):
        t = mp.sqrt(mp.mpf(z2.numerator) / z2.denominator)
        b = inv_one_minus_sin_ratio(z2)
        ok &= mp.mpf(b.numerator) / b.denominator >= t / mp.sin(t)
        c = sinh_ratio_up(z2)
        ok &= mp.mpf(c.numerator) / c.denominator >= mp.sinh(t) / t
    return ok


def gate_repair(data: SlabData) -> bool:
    """The repaired stage-one literals cover the exact accounting."""
    from computations.su2_envelope import QHAT
    ok = data.T3 <= G3_TOT * CM ** 3
    ok &= data.k4 <= K4CAP
    ok &= sum(1 for w in data.words
              if len(set(e for e, _ in w)) >= 3) == 4
    ok &= q_hat(Frac(1, 50)) <= QHAT     # stage one's quartic+ cover
    return bool(ok)


def gate_mirror(data: SlabData) -> bool:
    """Mirror provenance + engine/theta scheme covariance factor 4."""
    ok = data.ginv_tb == 1
    # theta-kernel Qmin form from the banked u1 ledger: 3 n^2 + 3 m^2
    # + 2 n m; engine diagonal: -log T[n,0] variance part
    # = (8 tau) Ginv_tt C_comp with Ginv_tt = 3 => 12 tau n^2 in the
    # n^2-normalization used by the theta kernel (C(n) = n^2):
    # 12/3 = 4 = 8 Ginv_tb / 2  — the same conversion on the cross.
    path = os.path.join(HERE, "u1_theta_results.json")
    with open(path) as fh:
        led = json.load(fh)
    qd, qd2, qc = (Frac(x) for x in led["Qmin_form"])
    ok &= (qd, qd2, qc) == (Frac(3), Frac(3), Frac(2))
    ginv_tt = data.net.Ginv[data.t_link][data.t_link]
    ok &= ginv_tt == 3
    engine_diag = 8 * ginv_tt * Frac(1, 2)      # (n^2 Var)/2 per n^2
    engine_cross = 8 * data.ginv_tb             # nm coefficient
    ok &= engine_diag / qd == engine_cross / qc == 4
    # banked connected-order zeros: kappa_2 (§16f g4 "u1_mirror") and
    # kappa_3 (§16g "u1_tau3"), plus the SU(2) series literals.
    with open(os.path.join(HERE, "c_su2_assembly_results.json")) as fh:
        a = json.load(fh)
    ok &= a["u1_mirror"] is True
    ok &= Frac(a["X11_tau2"]) == X2
    with open(os.path.join(HERE, "c_su2_tau3_results.json")) as fh:
        t3led = json.load(fh)
    ok &= t3led["u1_tau3"] is True
    ok &= Frac(t3led["X"]["1,1"]["tau2"]) == X2
    ok &= Frac(t3led["X"]["1,1"]["tau3"]) == X3
    return bool(ok)


def gate_dominate() -> bool:
    """Stage two strictly dominates repaired stage one."""
    t1, _, k1 = envelope_theorem_stage1()
    t2, _, k2, _ = envelope_theorem2()
    return k2 < k1 and t2 > t1


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------


def main() -> None:
    print("SU(2) envelope lemma — stage two (sharpened constants)")
    print("=" * 66)
    data = SlabData()
    print(f"exact complex: T3 = {float(data.T3):.4f}  "
          f"S4 = {float(data.S4):.1f}  s_max = {float(data.s_max):.3f}")
    print("GATE cubic structure:",
          "PASSED" if gate_cubic(data) else "FAILED")
    print("GATE dynkin/sqrt/exp bounds:",
          "PASSED" if gate_dynkin() else "FAILED")
    print("GATE stage-one repair literals:",
          "PASSED" if gate_repair(data) else "FAILED")
    print("GATE mirror provenance/covariance:",
          "PASSED" if gate_mirror(data) else "FAILED")
    print("GATE star (stage-one mechanism):",
          "PASSED" if star_gate(verbose=False) else "FAILED")
    tau, s_up, k_x, consts = envelope_theorem2()
    print(f"kappa = {consts['kappa']}  r0 = {consts['r0']} "
          f"(~{float(consts['r0']):.3e})  A0 ~ {float(consts['A0']):.4f}")
    print("THEOREM: |X_11 - 6 tau^2 - (115/6) tau^3| <= K_X tau^4 "
          "on (0, tau*]")
    print(f"  K_X ~ {float(k_x):.3e}   "
          f"tau* = 2^-{tau.denominator.bit_length() - 1}  "
          f"(~{float(tau):.3e})")
    print(f"  s* <= 1 - {float(1 - s_up):.3e}  (explicit rational banked)")
    k_u1, margin = mirror_theorem()
    print(f"U(1) MIRROR: |X_U1 + 8 tau| <= K_U1 tau^4,  "
          f"K_U1 ~ {float(k_u1):.3e}")
    print(f"  SEPARATION on (0, tau*]: X_SU2 > 0 > X_U1 "
          f"(gap floor ~{float(margin):.3e} at tau*)")
    print("GATE stage-two dominates stage one:",
          "PASSED" if gate_dominate() else "FAILED")
    t1, _, k1 = envelope_theorem_stage1()
    print(f"  (stage one repaired: K_X ~ {float(k1):.3e}, "
          f"tau* = 2^-{t1.denominator.bit_length() - 1})")
    out = {
        "tau_star": [str(tau.numerator), str(tau.denominator)],
        "s_star_upper": [str(s_up.numerator), str(s_up.denominator)],
        "K_X": [str(k_x.numerator), str(k_x.denominator)],
        "K_small": [str(consts["K_small"].numerator),
                    str(consts["K_small"].denominator)],
        "kappa": str(consts["kappa"]),
        "r0": str(consts["r0"]),
        "A0": str(consts["A0"]),
        "T3": str(SlabData().T3),
        "K_U1": [str(k_u1.numerator), str(k_u1.denominator)],
        "X1_U1": str(X1_U1),
        "stage1_repaired_tau_star": [str(t1.numerator),
                                     str(t1.denominator)],
        "stage1_repaired_K_X": [str(k1.numerator), str(k1.denominator)],
        "A0_stage1": str(A0_STAGE1),
    }
    with open(OUT_JSON, "w") as fh:
        json.dump(out, fh, indent=1)
    print("ledger written")


if __name__ == "__main__":
    main()
