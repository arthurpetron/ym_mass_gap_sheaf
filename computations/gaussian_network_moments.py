"""MD.3 (via §16d) — the Gaussian network dictionary of the slab and
the fusion-channel structure of the flat-limit SU(2) pair moment.

**What this module is.**  The first stage of the c_SU2 moment
computation queued in work_plan §16d: (1) the exact rational Gaussian
network dictionary of the slab (link/face/loop covariances from the
face-boundary incidence), gated against the U(1) theta-side Qmin by
Legendre duality; (2) the leading flat-limit formula for the SU(2)
pair moment as a FUSION-CHANNEL SUM; (3) the fusion-mean identity
that kills the linear cross slope; (4) the single-face insertion-
calculus gate; (5) the connected cross-ratio observable with its
group-separated asymptotics, U(1) side verified from the certified
theta kernel.  No value of c_SU2 is claimed here: this is the
dictionary and the structure theorems the assembly will consume.

**1. The dictionary.**  Gauge-fix the adapted tree (tree links = id).
Per su(2) component, the flat limit of the slab is the Gaussian
network with action S(X) = |B X|^2 / (4 tau) on the 16 free links,
B the 20 x 16 face-boundary incidence; every abelianized face angle
is theta_f = (B X)_f and each coarse loop angle is a single free
link (adapted gauge).  Covariances (per component, exact rationals
times 2 tau):

    C_X = 2 tau G^{-1},  G = B^T B  (16 x 16, positive definite),
    Sigma_F = 2 tau B G^{-1} B^T,   Sigma_L = 2 tau L G^{-1} L^T.

GATE (Legendre duality with the flux picture): L G^{-1} L^T must
equal M = [[3, 1], [1, 3]] — then E[e^{i(n theta_t + m theta_b)}] =
e^{-tau (3n^2 + 3m^2 + 2nm)} = e^{-tau Qmin(n,m)}, the U(1) theta
result, from the ANGLE picture.  The SU(2) normalization is fixed by
the single-face gate below: per-component variances are 4x the
abelian ones (class half-angle phi = |theta|/2), i.e. 8 tau G-forms.

**2. The fusion-channel formula (leading order).**  Writing the
coarse loop insertions as operator tilts chi_n = tr exp(i theta_t.J)
on spin j = n/2, and taking the Gaussian expectation with
commutators deferred (they enter at relative O(tau^2)):

    T[n,m] / Theta(tau)
      ~ sum_{J = |j-j'|}^{j+j'} (2J+1)
          e^{- tau [ 3 C(n) + 3 C(m) + (C(2J) - C(n) - C(m)) ] },

C(n) = n(n+2).  The abelian cross term gamma n m is REPLACED by the
fusion-channel spread delta_J = C(2J) - C(n) - C(m).

**3. The fusion-mean identity (exact, trivial, decisive).**

    sum_J (2J+1) delta_J = tr_{j (x) j'} ( Cas ) - d_n d_m (C_j+C_j')
                         = 2 tr(J_1 . J_2) = 0,

because tr J_i = 0.  So the MEAN channel spread vanishes
identically: the SU(2) pair moment has NO O(tau) cross correction at
leading fusion order — the algebraic form of the §16c realness
prediction.  First surviving cross effect: -tau^2 Var_fusion(delta)/2
in the log (an O(tau^2) connected cross ratio).  Consequence:
c_SU2 is carried ENTIRELY by the Jacobian/BCH insertion moments
(plus the finite-basis cumulant mechanism on the leading exponents,
which is computable exactly once the leading form is fixed).

**4. The discriminating observable.**  The connected cross ratio

    X_{nm}(s) = log( T[n,m] T[0,0] / (T[n,0] T[0,m]) )

has group-separated asymptotics as tau -> 0:

    U(1):   X_{nm} -> - gamma n m tau = -2 n m tau   (exact, theta),
    SU(2):  X_{nm} -> + Var_fusion(delta)/2 tau^2  (prediction;
            n = m = 1: delta in {-6, +2}, weights {1, 3},
            mean 0, Var 12  =>  X_11 -> +6 tau^2),

opposite SIGN and different ORDER.  The U(1) lane is verified here
from the certified theta kernel; the SU(2) lane awaits the
M -> infinity resummation (it is the designated first consumer).

**5. Honesty.**  The fusion formula defers operator-ordering
(commutator) corrections, rigorously O(tau^2) relative for fixed
(n, m) — they feed the same order as Var_fusion(delta), so the
SU(2) tau^2 COEFFICIENT above is indicative until the BCH moments
are assembled; the O(tau) statements (mean identity, no linear
cross) are NOT affected by ordering corrections.  Images and
theta-separation slack are exponentially small as in §16c.  The
per-face/per-link Jacobian insertions (sin phi / phi and
(sin u / u)^2) are NOT yet assembled into c_SU2 — their covariance
data is emitted for the assembly step.

Run:  python -m computations.gaussian_network_moments
"""

from __future__ import annotations

import json
import os
import sys
from fractions import Fraction
from typing import Dict, List, Tuple

HERE = os.path.dirname(os.path.abspath(__file__))
Frac = Fraction
OUT_JSON = os.path.join(HERE, "gaussian_network_results.json")

sys.set_int_max_str_digits(0)

from computations.dp6_u1_slab_blocking import (  # noqa: E402
    _CX,
    _W_FACE,
    _W_TOP_LOOP,
    _W_BOT_LOOP,
    _TOP,
    _BOTTOM,
    _WALLS,
    NF,
)

FREE: List[int] = list(_CX.free)
NL = len(FREE)                      # 16 free links

# face-boundary incidence over free links (20 x 16) and loop rows
B: List[List[int]] = [[_W_FACE[f][e] for e in FREE] for f in range(NF)]
L: List[List[int]] = [[_W_TOP_LOOP[e] for e in FREE],
                      [_W_BOT_LOOP[e] for e in FREE]]


def mat_mul(A, Bm):
    return [[sum(A[i][k] * Bm[k][j] for k in range(len(Bm)))
             for j in range(len(Bm[0]))] for i in range(len(A))]


def mat_T(A):
    return [list(r) for r in zip(*A)]


def mat_inv(A):
    n = len(A)
    M = [[Frac(A[i][j]) for j in range(n)]
         + [Frac(1 if i == j else 0) for j in range(n)] for i in range(n)]
    for col in range(n):
        piv = next(r for r in range(col, n) if M[r][col] != 0)
        M[col], M[piv] = M[piv], M[col]
        inv = 1 / M[col][col]
        M[col] = [x * inv for x in M[col]]
        for r in range(n):
            if r != col and M[r][col]:
                f = M[r][col]
                M[r] = [a - f * b for a, b in zip(M[r], M[col])]
    return [row[n:] for row in M]


G = mat_mul(mat_T(B), B)            # 16 x 16, positive definite
G_INV = mat_inv(G)
SIGMA_F = mat_mul(mat_mul(B, G_INV), mat_T(B))     # 20 x 20 (x 2 tau)
SIGMA_L = mat_mul(mat_mul(L, G_INV), mat_T(L))     # 2 x 2  (x 2 tau)
SIGMA_FL = mat_mul(mat_mul(B, G_INV), mat_T(L))    # 20 x 2 (x 2 tau)


def cas4(n: int) -> int:
    return n * (n + 2)


# ---------------------------------------------------------------------------
# Gates.
# ---------------------------------------------------------------------------


def gate_loops_are_single_links() -> bool:
    """Adapted gauge: each coarse loop is one free link."""
    ok = True
    for row in L:
        nz = [abs(x) for x in row if x]
        ok &= (len(nz) == 1 and nz[0] == 1)
    return ok


def gate_duality() -> bool:
    """Legendre duality: L G^{-1} L^T == [[3,1],[1,3]] == the flux-
    picture Qmin form (u1_theta_kernel: Qmin = 3n^2+3m^2+2nm)."""
    return SIGMA_L == [[Frac(3), Frac(1)], [Frac(1), Frac(3)]]


def face_variance_classes() -> Dict[str, List[Frac]]:
    """Diagonal of Sigma_F grouped by face type (D4 symmetry check)."""
    out: Dict[str, List[Frac]] = {"top": [], "bottom": [],
                                  "iwall": [], "pwall": []}
    pwalls = [f for f in range(NF)
              if f not in _TOP and f not in _BOTTOM and f not in _WALLS]
    for f in range(NF):
        v = SIGMA_F[f][f]
        if f in _TOP:
            out["top"].append(v)
        elif f in _BOTTOM:
            out["bottom"].append(v)
        elif f in _WALLS:
            out["iwall"].append(v)
        else:
            out["pwall"].append(v)
    assert len(pwalls) == 8
    return out


def insertion_data() -> Dict[str, str]:
    """The covariance aggregates the (ii)-insertion assembly will
    consume: for each loop l and face f, Cov(theta_f, theta_l)
    (x 2 tau), and the sums of squares by face class.  Emitted as
    data; no c is derived from them here."""
    agg: Dict[str, Frac] = {}
    for li, name in ((0, "top_loop"), (1, "bot_loop")):
        s_all = sum(SIGMA_FL[f][li] ** 2 for f in range(NF))
        s_tiles = sum(SIGMA_FL[f][li] ** 2 for f in _TOP + _BOTTOM)
        s_iw = sum(SIGMA_FL[f][li] ** 2 for f in _WALLS)
        agg[f"sum_cov2_{name}_all"] = s_all
        agg[f"sum_cov2_{name}_tiles"] = s_tiles
        agg[f"sum_cov2_{name}_iwalls"] = s_iw
    # link-insertion aggregates: Cov(X_e, theta_l) = 2 tau (G^-1 L^T)
    GL = mat_mul(G_INV, mat_T(L))
    for li, name in ((0, "top_loop"), (1, "bot_loop")):
        agg[f"sum_cov2_links_{name}"] = sum(GL[e][li] ** 2
                                            for e in range(NL))
    return {k: str(v) for k, v in agg.items()}


# ---------------------------------------------------------------------------
# Fusion-channel structure.
# ---------------------------------------------------------------------------


def fusion_channels(n: int, m: int) -> List[Tuple[int, int, int]]:
    """(N_J = 2J, d_J, delta_J) over J in |j-j'|..j+j', j = n/2."""
    out = []
    for NJ in range(abs(n - m), n + m + 1, 2):
        dJ = NJ + 1
        delta = cas4(NJ) - cas4(n) - cas4(m)
        out.append((NJ, dJ, delta))
    return out


def fusion_mean_identity(nmax: int = 6) -> bool:
    """sum_J d_J delta_J == 0 exactly, for all n, m <= nmax (the
    trace-free identity tr(J_1 . J_2) = 0 — kills the linear cross
    slope for SU(2))."""
    for n in range(0, nmax + 1):
        for m in range(0, nmax + 1):
            ch = fusion_channels(n, m)
            if sum(d for _N, d, _x in ch) != (n + 1) * (m + 1):
                return False
            if sum(d * x for _N, d, x in ch) != 0:
                return False
    return True


def fusion_variance(n: int, m: int) -> Frac:
    """Var_fusion(delta) = sum d_J delta_J^2 / (d_n d_m) (mean 0)."""
    ch = fusion_channels(n, m)
    return Frac(sum(d * x * x for _N, d, x in ch), (n + 1) * (m + 1))


def t_flat(n: int, m: int, tau) -> float:
    """Leading fusion-channel pair moment, normalized so that
    t_flat -> d_n d_m as tau -> 0 (Theta and e^{20 tau} dropped)."""
    import math
    acc = 0.0
    for _NJ, dJ, delta in fusion_channels(n, m):
        acc += dJ * math.exp(-tau * (3 * cas4(n) + 3 * cas4(m) + delta))
    return acc


# ---------------------------------------------------------------------------
# Gate: the single-face insertion calculus.
# ---------------------------------------------------------------------------


def single_face_gate(digits: int = 25):
    """e^{tau} * E_flat[(sin phi / phi) chi_n(phi)] == d_n e^{-tau C(n)}
    with phi = |theta|/2, theta an isotropic R^3 Gaussian of
    per-component variance 8 tau: the (sin phi / phi) Jacobian
    insertion converts the flat (n+1)^2 into the exact C(n) =
    (n+1)^2 - 1 together with the e^{tau} face normalization.  This
    is the gate fixing every constant of the insertion calculus."""
    import mpmath as mp
    mp.mp.dps = digits + 15
    worst = mp.mpf(0)
    for tau in (mp.mpf("0.05"), mp.mpf("0.3"), mp.mpf("0.8")):
        a = 8 * tau                  # per-component variance
        norm = (2 * mp.pi * a) ** mp.mpf("1.5")
        for n in (0, 1, 2, 3):
            # radial: theta = r, phi = r/2;
            # (sin phi/phi) chi_n = sin((n+1)phi)/phi = 2 sin((n+1)r/2)/r
            val = mp.quad(
                lambda r: (4 * mp.pi * r * r / norm)
                * (2 * mp.sin((n + 1) * r / 2) / r)
                * mp.e ** (-r * r / (2 * a)),
                [0, mp.inf])
            got = mp.e ** tau * val
            want = (n + 1) * mp.e ** (-tau * n * (n + 2))
            worst = max(worst, abs(got - want) / want)
    return worst < mp.mpf(10) ** (-digits), worst


# ---------------------------------------------------------------------------
# The connected cross ratio: U(1) lane verified from the theta kernel.
# ---------------------------------------------------------------------------


def u1_cross_ratio(s: Frac) -> Tuple[Frac, Frac, float]:
    """Certified window for X_11 = log(T[1,1] T[0,0]/(T[1,0] T[0,1]))
    (U(1), M = infinity theta kernel); returned as the window of the
    RATIO (exact rationals) plus the float log."""
    import math
    from computations.u1_theta_kernel import theta_window
    tgt = Frac(1, 10 ** 12)
    w = {}
    for (n, m) in ((1, 1), (0, 0), (1, 0), (0, 1)):
        lo, hi, _R = theta_window(n, m, s, s ** 6 * tgt)
        w[(n, m)] = (lo, hi)
    r_lo = (w[(1, 1)][0] * w[(0, 0)][0]) / (w[(1, 0)][1] * w[(0, 1)][1])
    r_hi = (w[(1, 1)][1] * w[(0, 0)][1]) / (w[(1, 0)][0] * w[(0, 1)][0])
    return r_lo, r_hi, math.log(float((r_lo + r_hi) / 2))


def main() -> None:
    print("Gaussian network dictionary + fusion structure (§16e)")
    print(f"free links: {NL}; faces: {NF}")
    ok1 = gate_loops_are_single_links()
    print(f"  gate: coarse loops are single free links: "
          f"{'PASSED' if ok1 else 'FAILED'}")
    ok2 = gate_duality()
    print(f"  gate: L G^-1 L^T == [[3,1],[1,3]] (Legendre dual of "
          f"Qmin): {'PASSED' if ok2 else 'FAILED'}")
    fv = face_variance_classes()
    for k, v in fv.items():
        uniq = sorted(set(v))
        print(f"  face variance class {k}: {[str(x) for x in uniq]} "
              f"(x 2 tau; {len(v)} faces, {len(uniq)} value(s))")
    ok3 = fusion_mean_identity()
    print(f"  fusion-mean identity sum d_J delta_J == 0 (n,m <= 6): "
          f"{'PASSED' if ok3 else 'FAILED'}")
    print(f"  Var_fusion(delta): (1,1): {fusion_variance(1, 1)}, "
          f"(1,2): {fusion_variance(1, 2)}, "
          f"(2,2): {fusion_variance(2, 2)}")
    ok4, w4 = single_face_gate()
    print(f"  gate: single-face insertion calculus (25 digits): "
          f"{'PASSED' if ok4 else 'FAILED'}  worst rel = {w4}")

    print("\nconnected cross ratio X_11:")
    import math
    rows = []
    for s in (Frac(9, 10), Frac(99, 100)):
        tau = -math.log(float(s))
        rlo, rhi, x = u1_cross_ratio(s)
        pred = -2 * tau
        print(f"  s={s}: U(1) X_11 = {x:+.6f}  (asymptote -2 tau = "
              f"{pred:+.6f})   [SU(2) predicted +6 tau^2 = "
              f"{6*tau*tau:+.6f} — awaits the M->inf resummation]")
        rows.append({"s": str(s), "u1_X11": x, "asymptote": pred,
                     "su2_pred": 6 * tau * tau})

    out = {
        "sigma_L": [[str(x) for x in row] for row in SIGMA_L],
        "face_variances": {k: [str(x) for x in v]
                           for k, v in face_variance_classes().items()},
        "insertion_data": insertion_data(),
        "fusion_variances": {f"{n},{m}": str(fusion_variance(n, m))
                             for n in (1, 2) for m in (1, 2)},
        "u1_cross_ratio": rows,
    }
    with open(OUT_JSON, "w") as fh:
        json.dump(out, fh, indent=1)
    print(f"\nledger written to {OUT_JSON}")
    assert ok1 and ok2 and ok3 and ok4


if __name__ == "__main__":
    main()
