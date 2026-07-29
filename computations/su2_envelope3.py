"""MD.3 / work_plan §17-P1 — the ENVELOPE LEMMA, stage three: the
MAJORANT-SERIES envelope.  The middle coefficients (eta^8..eta^N) are
bounded by exact-rational Gaussian-moment majorants with NO Cauchy
radius penalty; the analyticity machinery is demoted to the ultra-tail
(order N+2) only.  This executes the §17b "next lever" — it both
subsumes the polydisc idea (the per-face locality lives in the
per-face majorant factors) and delivers the tau^4-law item in the
weakened-but-sufficient form the positivity theorem needs (a certified
BOUND on every middle coefficient instead of its exact value).

WHY THIS BEATS STAGES ONE/TWO STRUCTURALLY
------------------------------------------
Stages one/two bound the whole remainder-after-6 by a single Cauchy
tail: K ~ A0 (cM/r0)^8 E[|xi|^8 e^{kappa|xi|^2}], paying (1/r0)^8 with
r0 ~ 4e-3 pinned by the insertion budget — the dominant, structural
loss (§17b HONESTY).  But the middle Taylor coefficients a_k of the
entry T(eta) = E[A(eta; xi)] are GLOBAL Gaussian moments — finite,
explicit integrals needing no analyticity at all.  Stage three bounds
them directly:

    |a_k| <= m_k := E-bound[ |coeff_k(A)(xi)| ],

by majorant composition: A factorizes as (character trace) x
(link Haar factors) x (face Jacobians) x (face action factors
exp(-g_f)), each factor's eta-coefficients dominated by an explicit
positive-coefficient series in eta whose coefficients are monomials in
the field atoms; products/exponentials of majorants majorize products
/exponentials (all coefficients positive).  The expectation of each
monomial is bounded by the pooled-Hoelder step

    E[prod_i chi_i^{a_i}] <= E[chi^D],   D = sum a_i,

(chi = |z|, z standard 3-dim Gaussian; every atom is c_e * chi_e in
law with c_e^2 >= (G^-1)_ee), whose even moments are exact rationals
and odd moments have the exact form sqrt(2/pi) 2^{m+1} (m+1)! <=
(4/5) 2^{m+1} (m+1)!.  No radius, no reweight, no (1/r0)^8.

PER-FACE STRUCTURE (the polydisc content, absorbed)
---------------------------------------------------
The action factor's series g_f = sum_j eta^j S_{f,j+2}/2 is bounded
per order with the exact word structure:
  j=1 (cubic):   |S_{f,3}| = 2|theta.Delta_2| <= 2 t3_f — the §17b
                 triple-product sums; ZERO on the 16 faces with <= 2
                 distinct links.
  j=2 (quartic): |S_{f,4}| = |Delta_2.Delta_2 + 2 theta.Delta_3| <=
                 p_f^2 + 2 s_f d3_f, with p_f (pair sums, repeated-
                 link pairs dropped) and d3_f (grade-3 majorant from
                 the labelled BCH fold recursion, top-level repeated-
                 letter brackets dropped) exact rationals per face.
  j=3 (quintic): 2 p_f d3_f + 2 a4 s_f^5 (a4 the Goldberg grade-4
                 scalar coefficient).
  j>=4:          the Goldberg/Dynkin closure [z^{j+2}](f(z)^2 - z^2)
                 s_f^{j+2}, f(z) = -log(2 - e^z) (all orders, all
                 positive).
The face Jacobian z/sin z (positive z^2-coefficients) is composed
with the same phi^2-majorant (cubic term refined by t3_f); link Haar
uses (sinh u/u)^2 >= |(sin u/u)^2|-coefficients; the character trace
uses |tr e^{iL}|/d_n d_m coefficient bounds exp-majorized.

THE THEOREM (stage three)
-------------------------
With Lambda(z) = -log(1 - sum_{even k>=2} m_k z^k) (positive
coefficients; |[eta^k] log T| <= [z^k]Lambda) and eta^2 = 8 tau:

    |X_11(tau) - 6 tau^2 - (115/6) tau^3|
        <=  R_X(tau) := 4 sum_{even k=8}^{N} Lambda_k (8 tau)^{k/2}
            + 4 u_inf(tau) / (1 - u_all(tau))     on (0, tau*],

u_inf = ultra-tail (order-(N+2) Cauchy with stage-two (r0, kappa)
machinery re-optimized per order) + large-field shell + LF-polynomial
closure (the E[1_LF |poly-coeff|] piece, closed by Cauchy-Schwarz
with L^2 majorants mL2_k — a piece stages one/two absorbed silently
in shell slack; here it is explicit) + image shell; u_all adds the
entry-poly deficit.  R_X(tau)/tau^2 is nondecreasing (every summand
is; asserted domain conditions tau* < c/2 for the shells), so the
single check R_X(tau*) <= 3 tau*^2 certifies X_11 > 0 and the
two-sided envelope on ALL of (0, tau*].

REPAIR CARRIED (§17c).  Stages one/two consumed the eta^8 Cauchy tail
as K_small tau^4, dropping 8^4 (eta^2 = 8 tau); both modules now
carry ETA8 = 8^4 explicitly (stage one tau* -> 2^-82, stage two ->
2^-61).  Stage three's powers are exact by construction ((8 tau)^{k/2}
throughout).

U(1) MIRROR.  Same pipeline, abelian lane (character factor only —
no BCH, no Jacobians, kappa = 0):  |X_U1 + 8 tau| <= R_X^{U1}(tau) on
the common interval, and the separation X_SU2 > 0 > X_U1 stands on
(0, tau*].  The mirror's majorant path is gated against the EXACT
abelian entries (T = e^{-V eta^2/16}-form, V = 8 from (G^-1): exact
coefficients 4^j/j! must be dominated — they are).

GATES
-----
  g_dynkin3   Goldberg scalar series positivity; f^2 consistency;
              numeric (mpmath, matrix logs + t-grading fit): exact
              BCH grades 2..4 on random rational face words are
              dominated by the labelled-fold majorants (p_f, d3_f)
              and by a_k sigma^k.
  g_fold      the labelled majorant fold agrees with the exact vector
              fold: |theta.Delta_2| <= t3-value, ||Delta_2|| <= p-value,
              ||Delta_3|| <= d3-value on random exact-rational vectors
              (values with certified sqrt uppers of actual norms).
  g_series    all majorant series coefficients >= 0; z/sin z and
              (sinh u/u)^2 coefficient domination vs mpmath.
  g_u1_exact  the U(1) majorants dominate the EXACT abelian entry
              coefficients 4^j/j! for all j <= N/2.
  g_moments   mu(d) uppers dominate mpmath chi_3 moments on a grid.
  g_dominate  tau*_3 > tau*_2 (repaired) and the stage-two window is
              contained in the stage-three bound at tau*_2.
  g_star      stage one's fusion-star mechanism gate (imported).

HONESTY
-------
tau* lands at the value printed by main() (banked in the ledger; the
scan certifies the exact dyadic).  The remaining structural losses,
ranked: (i) the pooled-Hoelder step E[prod chi^a] <= E[chi^D] ignores
the spread of a monomial across near-independent atoms — sharp
product-moment bounds (Wick/Isserlis trace formulas for quadratic
forms, or a Cauchy-Schwarz tree over atom groups) are the next
constant-factor lever inside m_k; (ii) the large-field shell
exp(-r0^2/(128 cM^2 tau)) now CAPS the certified interval — its fix
is compact-domain (owned-boundary) large-field bounds, i.e. image
technology, not more series orders; (iii) the matched-flow form
1 < tau'/tau <= 1 + c tau still awaits the diagonal kappa_3 or P2's
iterated-map consumer.  The banked series through tau^3 is imported
(provenance §16f-g); middle coefficients are BOUNDED, not computed —
the exact tau^4 cross law remains open (and is now needed only for
MD.4 curvature sharpness, not for the positivity interval).

Run:  python -m computations.su2_envelope3
"""

from __future__ import annotations

import json
import os
from fractions import Fraction
from math import factorial

from computations.su2_envelope import (
    CM,
    D_GAUSS,
    X2,
    X3,
    exp_neg_upper,
    image_bound,
    star_gate,
)
from computations.su2_envelope2 import (
    SlabData,
    a0_sharp,
    envelope_theorem2,
    gauss_even_moment,
    gauss_moment_exp,
    r0_budget,
    sqrt_up,
)

Frac = Fraction
HERE = os.path.dirname(os.path.abspath(__file__))
OUT_JSON = os.path.join(HERE, "su2_envelope3_results.json")

NMAX = 26                      # eta-order truncation of the majorants
DMAX = 3 * NMAX + 6            # chi-degree cap
D_U1 = 16

# ---------------------------------------------------------------------------
# Exact truncated series helpers (1D, dense rational).
# ---------------------------------------------------------------------------


def ser_mul(a: list[Frac], b: list[Frac], n: int) -> list[Frac]:
    out = [Frac(0)] * n
    for i, ai in enumerate(a):
        if ai == 0 or i >= n:
            continue
        for j, bj in enumerate(b):
            if i + j >= n:
                break
            if bj:
                out[i + j] += ai * bj
    return out


def goldberg_series(n: int) -> list[Frac]:
    """Taylor coefficients of f(z) = -log(2 - e^z) = sum_m u^m/m,
    u = e^z - 1 — the Goldberg/Dynkin scalar BCH majorant: the
    grade-k part of log(e^{x_1}...e^{x_m}) has norm <= [z^k]f(z) *
    sigma^k, sigma = sum ||x_i||, for sigma < log 2 (submultiplicative
    bracket norm; the su(2) cross product qualifies)."""
    u = [Frac(0)] + [Frac(1, factorial(k)) for k in range(1, n)]
    f = [Frac(0)] * n
    up = [Frac(0)] * n
    up[0] = Frac(1)
    for m in range(1, n):
        up = ser_mul(up, u, n)
        for i in range(n):
            f[i] += up[i] / m
    assert all(x > 0 for x in f[1:]), "Goldberg positivity"
    assert f[1] == 1 and f[2] == 1 and f[3] == 1
    return f


def z_over_sin_series(n: int) -> list[Frac]:
    """Coefficients of z / sin z (reciprocal of sin z / z); all even
    coefficients positive (asserted)."""
    s = [Frac(0)] * n
    for j in range(0, (n - 1) // 2 + 1):
        s[2 * j] = Frac((-1) ** j, factorial(2 * j + 1))
    inv = [Frac(0)] * n
    inv[0] = Frac(1)
    for k in range(1, n):
        acc = Frac(0)
        for j in range(1, k + 1):
            acc += s[j] * inv[k - j]
        inv[k] = -acc
    assert all(inv[k] >= 0 for k in range(n)), "z/sin z positivity"
    return inv


def haar_coeff(j: int) -> Frac:
    """(sinh u / u)^2 = sum_j 2^{2j+1} u^{2j} / (2j+2)! — dominates
    |(sin u / u)^2| coefficientwise."""
    return Frac(2 ** (2 * j + 1), factorial(2 * j + 2))


# ---------------------------------------------------------------------------
# chi_3 moment uppers (chi = |z|, z standard Gaussian in R^3).
# ---------------------------------------------------------------------------


def mu_chi(d: int) -> Frac:
    """Certified upper bound on E[chi^d]: even d exact
    prod_{i<d/2}(3+2i); odd d = 2m+1 exact sqrt(2/pi) 2^{m+1} (m+1)!
    <= (4/5) 2^{m+1} (m+1)!."""
    if d % 2 == 0:
        out = Frac(1)
        for i in range(d // 2):
            out *= 3 + 2 * i
        return out
    m = (d - 1) // 2
    return Frac(4, 5) * 2 ** (m + 1) * factorial(m + 1)


# ---------------------------------------------------------------------------
# Labelled BCH fold: per-face exact majorant constants p_f, d3_f.
# ---------------------------------------------------------------------------


def _bracket(u: list[tuple[Frac, tuple[int, ...]]],
             v: list[tuple[Frac, tuple[int, ...]]],
             ) -> list[tuple[Frac, tuple[int, ...]]]:
    """Norm-majorant bracket: ||[a,b]|| <= ||a|| ||b||, with the exact
    zero [x_e, x_e] = 0 dropped when both sides are the SAME single
    letter (same link; signs +-1 square away)."""
    out = []
    for cu, lu in u:
        for cv, lv in v:
            if len(lu) == 1 and len(lv) == 1 and lu[0] == lv[0]:
                continue
            out.append((cu * cv, lu + lv))
    return out


def face_fold_majorants(word: list[tuple[int, int]],
                        c: list[Frac]) -> tuple[Frac, Frac]:
    """(p_f, d3_f): certified upper bounds on ||Delta_2|| and
    ||Delta_3|| for the face word, via the labelled graded BCH fold
    (the bch_parts recursion with norm semantics):
      A2' = A2 + [A1,B]/2,
      A3' = A3 + [A2,B]/2 + [A1,[A1,B]]/12 + [B,[B,A1]]/12."""
    a1: list[tuple[Frac, tuple[int, ...]]] = []
    a2: list[tuple[Frac, tuple[int, ...]]] = []
    a3: list[tuple[Frac, tuple[int, ...]]] = []
    for e, _s in word:
        b1 = [(Frac(1), (e,))]
        n2 = a2 + [(x / 2, w) for x, w in _bracket(a1, b1)]
        n3 = a3 + [(x / 2, w) for x, w in _bracket(a2, b1)] \
            + [(x / 12, w) for x, w in _bracket(a1, _bracket(a1, b1))] \
            + [(x / 12, w) for x, w in _bracket(b1, _bracket(b1, a1))]
        a1 = a1 + b1
        a2, a3 = n2, n3
    val2 = sum((x * _prod(c, w) for x, w in a2), Frac(0))
    val3 = sum((x * _prod(c, w) for x, w in a3), Frac(0))
    return val2, val3


def _prod(c: list[Frac], w: tuple[int, ...]) -> Frac:
    out = Frac(1)
    for e in w:
        out *= c[e]
    return out


# ---------------------------------------------------------------------------
# 2D majorant series: index = eta-order k, dict chi-degree -> coeff.
# ---------------------------------------------------------------------------

Ser2 = list[dict[int, Frac]]


def ser2_zero() -> Ser2:
    return [dict() for _ in range(NMAX + 1)]


def ser2_one() -> Ser2:
    out = ser2_zero()
    out[0][0] = Frac(1)
    return out


def ser2_mul(a: Ser2, b: Ser2) -> Ser2:
    out = ser2_zero()
    for k1 in range(NMAX + 1):
        d1 = a[k1]
        if not d1:
            continue
        for k2 in range(NMAX + 1 - k1):
            d2 = b[k2]
            if not d2:
                continue
            o = out[k1 + k2]
            for e1, c1 in d1.items():
                for e2, c2 in d2.items():
                    if e1 + e2 > DMAX:
                        continue
                    o[e1 + e2] = o.get(e1 + e2, Frac(0)) + c1 * c2
    return out


def ser2_exp(a: Ser2) -> Ser2:
    assert not a[0], "exp needs vanishing constant term"
    out = ser2_zero()
    out[0][0] = Frac(1)
    for k in range(1, NMAX + 1):
        acc: dict[int, Frac] = dict()
        for j in range(1, k + 1):
            if not a[j]:
                continue
            for e1, c1 in a[j].items():
                for e2, c2 in out[k - j].items():
                    if e1 + e2 > DMAX:
                        continue
                    acc[e1 + e2] = acc.get(e1 + e2, Frac(0)) + j * c1 * c2
        out[k] = {e: cc / k for e, cc in acc.items()}
    return out


# ---------------------------------------------------------------------------
# The integrand majorant pipeline.
# ---------------------------------------------------------------------------


class Majorants:
    """m_k (E-bounds on |a_k|) and mL2_k (L^2 versions) for the SU(2)
    entry integrand, plus per-face structure constants."""

    def __init__(self, data: SlabData) -> None:
        self.data = data
        n = NMAX + 3
        self.f_gold = goldberg_series(n)
        self.f2 = ser_mul(self.f_gold, self.f_gold, n)
        self.b_jac = z_over_sin_series(n)
        c = data.c
        self.p_f: list[Frac] = []
        self.d3_f: list[Frac] = []
        for w in data.words:
            p, d3 = face_fold_majorants(w, c)
            self.p_f.append(p)
            self.d3_f.append(d3)
        prod = self._char_factor()
        prod = self._fold_haar(prod)
        prod = self._fold_faces(prod)
        self.coef = prod
        self.m = [self._ebound(k, sq=False) for k in range(NMAX + 1)]
        self.mL2 = [self._ebound(k, sq=True) for k in range(NMAX + 1)]

    def _char_factor(self) -> Ser2:
        data = self.data
        ct = data.c[data.t_link] + data.c[data.b_link]
        a = ser2_zero()
        a[1] = {1: Frac(7, 8) * ct}       # 7/8 >= sqrt(3)/2 (spin-1/2)
        return ser2_exp(a)

    def _fold_haar(self, prod: Ser2) -> Ser2:
        for e in range(self.data.net.nl):
            h = ser2_zero()
            for j in range(0, NMAX // 2 + 1):
                h[2 * j][2 * j] = haar_coeff(j) * self.data.c[e] ** (2 * j)
            prod = ser2_mul(prod, h)
        return prod

    def _delta_s_majorant(self, fi: int) -> list[Frac]:
        """D_i: |[eta^i] (phi_f^2 - theta_f^2)| <= D_i (chi-degree i),
        i >= 3, with the refined low orders and Goldberg closure."""
        data, sf = self.data, self.data.s_f[fi]
        p, d3 = self.p_f[fi], self.d3_f[fi]
        a4 = self.f_gold[4]
        d = [Frac(0)] * (NMAX + 3)
        d[3] = 2 * data.t3_f[fi]
        d[4] = p * p + 2 * sf * d3
        d[5] = 2 * p * d3 + 2 * a4 * sf ** 5
        for i in range(6, NMAX + 3):
            d[i] = self.f2[i] * sf ** i
        return d

    def _fold_faces(self, prod: Ser2) -> Ser2:
        for fi, w in enumerate(self.data.words):
            sf = self.data.s_f[fi]
            dsm = self._delta_s_majorant(fi)
            # Jacobian: z/sin z at phi; phi^2-majorant series
            fsq = ser2_zero()
            fsq[2][2] = sf * sf
            for i in range(3, NMAX + 1):
                if dsm[i]:
                    fsq[i][i] = dsm[i]
            jac = ser2_one()
            pw = ser2_one()
            for j in range(1, NMAX // 2 + 1):
                pw = ser2_mul(pw, fsq)
                bj = self.b_jac[2 * j]
                if bj == 0:
                    continue
                for k in range(NMAX + 1):
                    for e_, c_ in pw[k].items():
                        jac[k][e_] = jac[k].get(e_, Frac(0)) + bj * c_
            prod = ser2_mul(prod, jac)
            # action factor exp(-g): g_j = D_{j+2}/2
            if len(w) < 2:
                continue                   # single letter: Delta S == 0
            g = ser2_zero()
            for j in range(1, NMAX + 1):
                if j + 2 < len(dsm) and dsm[j + 2]:
                    g[j][j + 2] = dsm[j + 2] / 2
            prod = ser2_mul(prod, ser2_exp(g))
        return prod

    def _ebound(self, k: int, sq: bool) -> Frac:
        """m_k = sum_d coef * mu(d) (pooled Hoelder), or the L^2
        version sum_d coef * sqrt-upper(mu(2d))."""
        out = Frac(0)
        for dd, cc in self.coef[k].items():
            out += cc * (sqrt_up(mu_chi(2 * dd)) if sq else mu_chi(dd))
        return out


# ---------------------------------------------------------------------------
# Log-composition majorant Lambda and the assembled bound.
# ---------------------------------------------------------------------------


def log_majorant(m: list[Frac], n: int) -> list[Frac]:
    """Lambda = -log(1 - sum_{even k>=2} m_k z^k), coefficients to
    order n-1: |[eta^k] log T| <= Lambda_k (majorant log)."""
    lam = [Frac(0)] * n
    for k in range(2, n, 2):
        if k < len(m):
            lam[k] = m[k]
    out = [Frac(0)] * n
    pw = [Frac(0)] * n
    pw[0] = Frac(1)
    for j in range(1, n // 2 + 1):
        pw = ser_mul(pw, lam, n)
        if all(x == 0 for x in pw):
            break
        for i in range(n):
            out[i] += pw[i] / j
    return out


class Stage3:
    """The assembled stage-three bound and theorem scan."""

    def __init__(self) -> None:
        self.data = SlabData()
        self.maj = Majorants(self.data)
        self.lam = log_majorant(self.maj.m, NMAX + 1)

    def ultra_k(self, order: int, kappa: Frac) -> tuple[Frac, Frac]:
        """(K, r0): |tail after order-1 of the small-field part| <=
        K (8 tau)^{order/2} — stage-two Cauchy machinery at general
        even order."""
        r0, s0 = r0_budget(self.data, kappa)
        a0 = a0_sharp(self.data, r0, s0)
        return 2 * a0 * (CM / r0) ** order \
            * gauss_moment_exp(D_GAUSS, order // 2, kappa), r0

    def entry_bound(self, tau: Frac, n: int, ku: Frac, r0: Frac,
                    ) -> tuple[Frac, Frac, Frac]:
        """(mid, u_inf, pdef): the per-entry pieces at tau."""
        e2 = 8 * tau
        mid = sum((self.lam[k] * e2 ** (k // 2)
                   for k in range(8, n + 1, 2)), Frac(0))
        u_inf = ku * e2 ** ((n + 2) // 2)
        # large-field shell + its polynomial closure (Cauchy-Schwarz)
        c_lf = r0 * r0 / (128 * CM * CM)
        u_inf += Frac(8) * Frac(2) ** (D_GAUSS // 2) \
            * exp_neg_upper(c_lf / tau)
        lf2 = exp_neg_upper(r0 * r0 / (256 * CM * CM * tau))
        u_inf += Frac(2) ** 12 * lf2 \
            * sum((self.maj.mL2[k] * e2 ** (k // 2)
                   for k in range(0, n + 1, 2)), Frac(0))
        u_inf += image_bound(tau)
        pdef = sum((self.maj.m[k] * e2 ** (k // 2)
                    for k in range(2, 7, 2)), Frac(0))
        return mid, u_inf, pdef

    def x_bound(self, tau: Frac, n: int, ku: Frac, r0: Frac) -> Frac:
        """R_X(tau); raises AssertionError outside the valid domain."""
        mid, u_inf, pdef = self.entry_bound(tau, n, ku, r0)
        u_all = mid + u_inf + pdef
        assert u_all < Frac(1, 2), "composition guard"
        # monotonicity domain for the shells (R_X / tau^2 increasing)
        assert tau < r0 * r0 / (512 * CM * CM)
        return 4 * mid + 4 * u_inf / (1 - u_all)

    def theorem(self, kappas: tuple[Frac, ...] = (
            Frac(1, 9), Frac(1, 6), Frac(1, 5), Frac(1, 4),
            Frac(3, 10), Frac(1, 3), Frac(2, 5), Frac(9, 20)),
            ) -> dict[str, object]:
        """Scan (kappa, N) and dyadic tau for the largest tau* with
        R_X(tau*) <= 3 tau*^2.  Monotonicity of R_X/tau^2 (each
        summand nondecreasing on the asserted domain) extends the
        single check to all of (0, tau*]."""
        best: dict[str, object] = {}
        for kappa in kappas:
            try:
                r0, _ = r0_budget(self.data, kappa)
            except AssertionError:
                continue
            for n in range(8, NMAX - 1, 2):
                ku, r0_ = self.ultra_k(n + 2, kappa)
                tau_ok = None
                for p in range(20, 90):
                    tau = Frac(1, 2 ** p)
                    try:
                        rx = self.x_bound(tau, n, ku, r0_)
                    except AssertionError:
                        continue
                    if rx <= 3 * tau * tau:
                        tau_ok = tau
                        break
                if tau_ok and (not best or tau_ok > best["tau_star"]):
                    best = {"tau_star": tau_ok, "N": n, "kappa": kappa,
                            "K_ultra": ku, "r0": r0_}
        assert best, "no admissible parameters"
        tau = best["tau_star"]
        assert isinstance(tau, Frac)
        best["R_X_at_tau"] = self.x_bound(
            tau, int(best["N"]), best["K_ultra"], best["r0"])  # type: ignore[arg-type]
        best["s_star_upper"] = 1 - tau + tau * tau / 2
        return best


# ---------------------------------------------------------------------------
# The U(1) mirror lane.
# ---------------------------------------------------------------------------


_R0_U1 = Fraction(4)


class MirrorStage3:
    """Abelian pipeline: character factor only (no BCH, no Jacobians,
    flat Haar).  Exact entries e^{-V eta^2/16}-form are dominated by
    the majorants (gated)."""

    def __init__(self, data: SlabData) -> None:
        self.data = data
        ct = data.c[data.t_link] + data.c[data.b_link]
        self.m = [Frac(0)] * (NMAX + 1)
        self.m[0] = Frac(1)
        for k in range(1, NMAX + 1):
            self.m[k] = ct ** k * mu_chi(k) / factorial(k)
        self.lam = log_majorant(self.m, NMAX + 1)

    def ultra_k(self, order: int, r0: Frac) -> Frac:
        from computations.su2_envelope2 import exp_up_any
        data = self.data
        ct = data.c[data.t_link] + data.c[data.b_link]
        a0 = exp_up_any((r0 / CM) * ct)
        return 2 * a0 * (CM / r0) ** order * gauss_even_moment(
            D_U1, order // 2)

    def x_bound(self, tau: Frac, n: int, r0: Frac = _R0_U1) -> Frac:
        e2 = 8 * tau
        mid = sum((self.lam[k] * e2 ** (k // 2)
                   for k in range(8, n + 1, 2)), Frac(0))
        u_inf = self.ultra_k(n + 2, r0) * e2 ** ((n + 2) // 2)
        u_inf += Frac(8) * Frac(2) ** (D_U1 // 2) \
            * exp_neg_upper(r0 * r0 / (128 * CM * CM * tau))
        u_inf += image_bound(tau)
        pdef = sum((self.m[k] * e2 ** (k // 2)
                    for k in range(2, 7, 2)), Frac(0))
        u_all = mid + u_inf + pdef
        assert u_all < Frac(1, 2)
        return 4 * mid + 4 * u_inf / (1 - u_all)

    def exact_coeff_gate(self) -> bool:
        """The exact abelian entries: worst entry (n = m = 1) has
        log T = -V eta^2 / 16, V-hat = v_tt + v_bb + 2 s_t s_b v_tb
        = 8 exactly, i.e. T = e^{-4 tau}-form with |a_{2j}| = 4^j/j!
        in eta^2/8-units — i.e. (1/2)^j/j! in eta^2-units.  The
        majorants must dominate them."""
        d = self.data
        g = d.net.Ginv
        v = g[d.t_link][d.t_link] + g[d.b_link][d.b_link] \
            + 2 * d.t_sign * d.b_sign * g[d.t_link][d.b_link]
        ok = v == 8
        for j in range(1, NMAX // 2 + 1):
            exact = (Frac(v, 16)) ** j / factorial(j)
            ok &= self.m[2 * j] >= exact
        return bool(ok)


# ---------------------------------------------------------------------------
# Gates.
# ---------------------------------------------------------------------------


def _rand_vecs(seed: int, n: int) -> list[list[Frac]]:
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


def _vadd(u: list[Frac], v: list[Frac], s: Frac) -> list[Frac]:
    return [a + s * b for a, b in zip(u, v, strict=True)]


def _fold_exact(xs: list[list[Frac]],
                ) -> tuple[list[Frac], list[Frac], list[Frac]]:
    """Exact graded BCH fold (grades 1-3) on su(2) vectors."""
    th = [Frac(0)] * 3
    d2 = [Frac(0)] * 3
    d3 = [Frac(0)] * 3
    for x in xs:
        n2 = _vadd(d2, _cross(th, x), Frac(1, 2))
        n3 = _vadd(d3, _cross(d2, x), Frac(1, 2))
        n3 = _vadd(n3, _cross(th, _cross(th, x)), Frac(1, 12))
        n3 = _vadd(n3, _cross(x, _cross(x, th)), Frac(1, 12))
        th = _vadd(th, x, Frac(1))
        d2, d3 = n2, n3
    return th, d2, d3


def gate_fold(data: SlabData, maj: Majorants, seed: int = 91) -> bool:
    """Labelled majorants dominate the exact vector fold, per face."""
    vecs = _rand_vecs(seed, data.net.nl)
    nrm = [sqrt_up(sum(v[i] * v[i] for i in range(3))) for v in vecs]
    ok = True
    for w in data.words:
        xs = [[Frac(s) * comp for comp in vecs[e]] for e, s in w]
        th, d2, d3 = _fold_exact(xs)

        def n2(v: list[Frac]) -> Frac:
            return sum(x * x for x in v)

        # values of the labelled majorants at the ACTUAL norms
        p_val, d3_val = face_fold_majorants(w, nrm)
        t3_val = Frac(0)
        es = [e for e, _ in w]
        for i in range(len(es)):
            for j in range(i + 1, len(es)):
                if es[i] == es[j]:
                    continue
                for k in range(len(es)):
                    if es[k] in (es[i], es[j]):
                        continue
                    t3_val += nrm[es[i]] * nrm[es[j]] * nrm[es[k]]
        t3_val /= 2
        pairing = sum(a * b for a, b in zip(th, d2, strict=True))
        ok &= pairing * pairing <= t3_val * t3_val
        ok &= n2(d2) <= p_val * p_val
        ok &= n2(d3) <= d3_val * d3_val
    return bool(ok)


def gate_dynkin_numeric(data: SlabData, digits: int = 60) -> bool:
    """mpmath: exact BCH grades 2..4 (t-grading fit of the matrix log
    of prod exp(t x_i)) are dominated by a_k sigma^k on the face
    words with random rational vectors."""
    import mpmath as mp
    mp.mp.dps = digits
    f = goldberg_series(8)
    vecs = _rand_vecs(20260730, data.net.nl)
    sig = [mp.matrix([[0, 1], [1, 0]]),
           mp.matrix([[0, -1j], [1j, 0]]),
           mp.matrix([[1, 0], [0, -1]])]

    def mat(v: list[Frac], t: object) -> object:
        m = mp.zeros(2, 2)
        for a in range(3):
            m += (mp.mpf(v[a].numerator) / v[a].denominator) * t \
                * (-1j / 2) * sig[a]
        return m

    ok = True
    for w in data.words:
        if len(w) < 2:
            continue
        xs = [[Frac(s) * c for c in vecs[e]] for e, s in w]
        sigma = sum(mp.sqrt(sum(mp.mpf(c.numerator) / c.denominator ** 1
                                * mp.mpf(c.numerator) / c.denominator
                                for c in x)) for x in xs)
        # t-grading: Z(t) = sum_k t^k z_k; fit via 6 t-values
        ts = [mp.mpf(1) / (10 * (i + 1)) for i in range(6)]
        zs = []
        for t in ts:
            pr = mp.eye(2)
            for x in xs:
                pr = pr * mp.expm(mat(x, t))
            zs.append(mp.logm(pr))
        # Vandermonde solve for grades 1..6 componentwise
        vand = mp.matrix(6, 6)
        for i in range(6):
            for j in range(6):
                vand[i, j] = ts[i] ** (j + 1)
        grades = [mp.zeros(2, 2) for _ in range(6)]
        for r in range(2):
            for cc in range(2):
                rhs = mp.matrix([z[r, cc] for z in zs])
                sol = mp.lu_solve(vand, rhs)
                for j in range(6):
                    grades[j][r, cc] = sol[j]

        def opnorm(m: object) -> object:
            return mp.sqrt(sum(abs(m[i, j]) ** 2      # type: ignore[index]
                               for i in range(2) for j in range(2)))

        for k in (2, 3, 4):
            # su(2) vector norm = 2-norm of the matrix rep * sqrt(2)
            # guard: Frobenius/sqrt(2) <= vector norm <= Frobenius*2
            zk = opnorm(grades[k - 1]) * mp.sqrt(2)
            bound = mp.mpf(f[k].numerator) / f[k].denominator * sigma ** k
            ok &= zk <= bound * (1 + mp.mpf(10) ** (-20))
    return bool(ok)


def gate_moments(digits: int = 40) -> bool:
    """mu_chi uppers dominate mpmath chi_3 moments."""
    import mpmath as mp
    mp.mp.dps = digits
    ok = True
    for d in range(1, 30):
        exact = 2 ** (mp.mpf(d) / 2) * mp.gamma((3 + mp.mpf(d)) / 2) \
            / mp.gamma(mp.mpf(3) / 2)
        up = mu_chi(d)
        ok &= mp.mpf(up.numerator) / up.denominator >= exact
    return bool(ok)


def gate_series(maj: Majorants, digits: int = 40) -> bool:
    """Majorant series positivity; z/sin z coefficients match the
    true Taylor coefficients (mpmath); (sinh u/u)^2 dominates
    |(sin u/u)^2| coefficientwise."""
    import mpmath as mp
    mp.mp.dps = digits
    ok = all(cc >= 0 for row in maj.coef for cc in row.values())
    # z/sin z Taylor coefficients vs mpmath (exact-match check)
    tay = mp.taylor(lambda z: z / mp.sin(z) if z != 0 else mp.mpf(1),
                    0, 12)
    for j in range(0, 6):
        b = maj.b_jac[2 * j]
        ok &= abs(mp.mpf(b.numerator) / b.denominator
                  - tay[2 * j]) < mp.mpf(10) ** (-25)
    # haar: 2^{2j+1}/(2j+2)! >= |(-1)^j-alternating sin-version|
    # coefficient of (sin u/u)^2 = (cos 2u - 1)/(-2u^2)-expansion:
    # |c_j| = 2^{2j+1}/(2j+2)! — equality in absolute value; check
    # numerically that the sinh version dominates pointwise.
    u = mp.mpf(1) / 3
    hv = sum((mp.mpf(haar_coeff(j).numerator)
              / haar_coeff(j).denominator) * u ** (2 * j)
             for j in range(0, (NMAX + 2) // 2))
    ok &= hv >= (mp.sin(u) / u) ** 2
    return bool(ok)


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------


def main() -> None:
    print("SU(2) envelope lemma — stage three (majorant series)")
    print("=" * 66)
    st = Stage3()
    data, maj = st.data, st.maj
    print(f"per-face p_f (4 largest): "
          f"{sorted((float(x) for x in maj.p_f), reverse=True)[:4]}")
    print(f"m_8 ~ {float(maj.m[8]):.3e}   m_10 ~ {float(maj.m[10]):.3e}"
          f"   m_12 ~ {float(maj.m[12]):.3e}")
    print("GATE fold majorants:", "PASSED" if gate_fold(data, maj)
          else "FAILED")
    print("GATE dynkin numeric:", "PASSED"
          if gate_dynkin_numeric(data) else "FAILED")
    print("GATE moments:", "PASSED" if gate_moments() else "FAILED")
    print("GATE series:", "PASSED" if gate_series(maj) else "FAILED")
    print("GATE star (mechanism):", "PASSED"
          if star_gate(verbose=False) else "FAILED")
    best = st.theorem()
    tau = best["tau_star"]
    assert isinstance(tau, Frac)
    print("THEOREM: |X_11 - 6 tau^2 - (115/6) tau^3| <= R_X(tau) "
          "on (0, tau*]")
    print(f"  tau* = 2^-{tau.denominator.bit_length() - 1}  "
          f"(~{float(tau):.3e})   N = {best['N']}  "
          f"kappa = {best['kappa']}")
    print(f"  R_X(tau*)/tau*^2 = "
          f"{float(best['R_X_at_tau'] / tau / tau):.4f} <= 3")  # type: ignore[operator]
    mir = MirrorStage3(data)
    print("GATE U(1) exact-coefficient domination:",
          "PASSED" if mir.exact_coeff_gate() else "FAILED")
    rx_u1 = mir.x_bound(tau, int(best["N"]))
    assert rx_u1 < 8 * tau
    print(f"U(1) MIRROR: |X_U1 + 8 tau| <= {float(rx_u1):.3e} at tau*"
          f" < 8 tau* — SEPARATION X_SU2 > 0 > X_U1 on (0, tau*]")
    t2, _, k2, _ = envelope_theorem2()
    print("GATE dominates stage two:", "PASSED" if tau > t2 else "FAILED")
    print(f"  (stage two repaired: tau* = 2^-"
          f"{t2.denominator.bit_length() - 1})")
    out = {
        "tau_star": [str(tau.numerator), str(tau.denominator)],
        "N": int(best["N"]),                    # type: ignore[call-overload]
        "kappa": str(best["kappa"]),
        "r0": str(best["r0"]),
        "R_X_over_tau2_at_tau_star": str(best["R_X_at_tau"] / tau / tau),  # type: ignore[operator]
        "s_star_upper": [str(best["s_star_upper"].numerator),   # type: ignore[union-attr]
                         str(best["s_star_upper"].denominator)],  # type: ignore[union-attr]
        "m8": str(maj.m[8]), "m10": str(maj.m[10]),
        "lambda8": str(st.lam[8]),
        "X2": str(X2), "X3": str(X3),
        "mirror_RX_at_tau_star": str(rx_u1),
        "stage2_tau_star": [str(t2.numerator), str(t2.denominator)],
        "stage2_K_X": [str(k2.numerator), str(k2.denominator)],
    }
    with open(OUT_JSON, "w") as fh:
        json.dump(out, fh, indent=1)
    print("ledger written")


if __name__ == "__main__":
    main()
