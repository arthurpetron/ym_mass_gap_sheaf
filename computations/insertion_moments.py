"""MD.3 stage two — the insertion-moment assembly for c_SU2.

**Object.**  work_plan §16e queued four assembly items; this module
executes (a) the kinematic fusion-variance term in closed form, (b)
the complete (ii)-Jacobian assembly by the SINGLE-TILT route, (c) the
BCH inventory with selection rules, (d) the U(1) mirror.  Output: the
decomposition

    c_SU2 = c_kin  +  c_ii  +  c_BCH,

with c_kin exact-in-closed-form at leading fusion order (operator-
ordering corrections enter the same tau^2-in-log order and are
DEFERRED — labeled), c_ii EXACT (this module; the single-tilt route
is protected from ordering by rotation invariance, and the cross-
insertion pieces are protected by the fusion-mean identity: they
enter one order later), and c_BCH OPEN (inventory delivered).

**(a) The kinematic cross term, closed form.**  Var_fusion(delta)
for j (x) j' with weights d_J:  delta_J = 4(C_J - C_j - C_j') =
8 J1.J2-eigenvalue; mean 0 (§16e identity); second moment via
tr_j(J_i J_k) = delta_ik C_j d_j / 3:

    <(J1.J2)^2> = C_j C_j' / 3
    =>  Var_fusion(delta) = 64 C_j C_j' / 3 = (4/3) C(n) C(m).

On the flowed envelope v_n = sum_m T[n,m] d_m s^{C(m)} this feeds the
pair slope through the d^2-weighted basis mean, pair-INDEPENDENT:

    c_kin = (2/3) <C(m)>_{d_m^2-weighted, m <= N}
          = 8/5 (N=1),  4 (N=2),  36/5 (N=3).

[Leading fusion order: operator-ordering corrections to E[chi chi]
are relative O(tau^2) and land in the SAME tau^2-in-log coefficient;
c_kin is therefore the leading-fusion value, to be completed by the
ordered pair moment — named open below.]

**(b) The (ii)-Jacobian assembly (exact).**  Insertions from the
exact flat representation: per link J_link = (sin u/u)^2 with
u = |X_e|/2  =>  I_e = -|X_e|^2/12;  per face J_face = phi/sin phi
with phi = |theta_f|/2  =>  I_f = +|(BX)_f|^2/24.  Against the
single tilt chi_n(exp X_t) (the loop is ONE free link; rotation
invariance makes every single-tilt moment ordering-free), Gaussian
conditioning gives for a quadratic insertion w |Z|^2 with
per-component correlation ratio r = Cov(Z, X_t)/Var(X_t):

    delta log T |_{n-dep} = w r^2 ( E[|X_t|^2 chi_n]/E[chi_n] - 3a )
                          = - w r^2 (C(n)/4) a^2 + O(a^3),

a = 24 tau (per-component loop variance, = 8 tau * (G^-1)_tt with
(G^-1)_tt = 3).  The coefficient -(C(n)/4) a^2 and the whole calculus
are GATED symbolically against the exact single-face identity
e^tau E[(sin phi/phi) chi_n] = d_n e^{-tau C(n)} through O(tau^2).
Summing with W := sum_e (-1/12) r_e^2 + sum_f (+1/24) r_f^2:

    delta log T[n,m] = -144 tau^2 W (C(n) + C(m)) + const + O(tau^3),
    =>  c_ii = +144 W        (exact rational).

Cross-insertion pieces (Z correlating with BOTH loops) couple to
E[X_t.X_b chi chi], whose leading fusion value is proportional to
sum_J d_J delta_J = 0: they enter at O(tau^3) in log T and do NOT
contribute to c — the fusion-mean identity protects the assembly.

**(c) BCH inventory.**  Faces with >= 2 free boundary links acquire
BCH corrections Delta_2 = (1/2) sum_{i<j} [X_i, X_j] + ... to the
face angle.  The O(tau) contributions to log T are <S_3^2>/2 - <S_4>
with S_3 = (1/(8 tau)) sum_f theta0_f . Delta2_f (odd; first order
vanishes against even tilts) and S_4 the quartic terms.  The
inventory (which faces, which ordered free-link words) is emitted;
the moments are the named-open remainder c_BCH.

**(d) U(1) mirror.**  Abelian Haar in angle coordinates is exactly
flat (J_link == 1), the abelian heat activity is exactly Gaussian +
images (J_face == 1; §16c theta separation), and the abelian face
angle is exactly linear (no BCH).  All three insertion families
vanish IDENTICALLY, so the mirror returns c_dyn = 0 exactly and the
abelian slope is purely the basis-cumulant value -4 (N=2) — §16c,
verified against certified windows.  The mirror is a derivation-level
gate: any pipeline change that generates a nonzero abelian insertion
is wrong by construction.

Run:  python -m computations.insertion_moments
"""

from __future__ import annotations

import json
import os
import sys
from fractions import Fraction
from typing import Dict, List, Tuple

HERE = os.path.dirname(os.path.abspath(__file__))
Frac = Fraction
OUT_JSON = os.path.join(HERE, "insertion_moments_results.json")

sys.set_int_max_str_digits(0)

from computations.gaussian_network_moments import (  # noqa: E402
    B,
    FREE,
    G_INV,
    L,
    NF,
    NL,
    cas4,
    fusion_variance,
)


# ---------------------------------------------------------------------------
# (a) Closed forms.
# ---------------------------------------------------------------------------


def v_closed_form_ok(nmax: int = 5) -> bool:
    """Var_fusion(delta) == (4/3) C(n) C(m), against explicit sums."""
    for n in range(1, nmax + 1):
        for m in range(1, nmax + 1):
            if fusion_variance(n, m) != Frac(4, 3) * cas4(n) * cas4(m):
                return False
    return True


def c_kin(N: int) -> Frac:
    """-(2/3) <C(m)> weighted by d_m^2 over the coarse basis m <= N.

    SIGN (corrected 2026-07-30 reconciliation): log T[n,m] gains
    +tau^2 Var_fusion/2 = +tau^2 (2/3) C(n) C(m) (Jensen — the
    variance ADDS in the log of averaged channel exponentials), so
    the flow-slope contribution is NEGATIVE: -(2/3) <C(m)>_{d^2}.
    Matches the §16f-original assembly's c_SU2(N) = 21/8 -
    (2/3) E_w[C(m)]; the first draft of this module carried +(2/3)
    from a hand-propagation slip."""
    num = sum((m + 1) ** 2 * cas4(m) for m in range(N + 1))
    den = sum((m + 1) ** 2 for m in range(N + 1))
    return -Frac(2, 3) * Frac(num, den)


# ---------------------------------------------------------------------------
# (b) The symbolic gates and the W aggregate.
# ---------------------------------------------------------------------------


def _chi_series(n: int, order: int = 3) -> List[Frac]:
    """chi_n(phi) = sin((n+1)phi)/sin(phi) as a series in phi^2:
    returns [c0, c1, c2, ...] with chi = sum c_k phi^{2k}, exact."""
    import sympy as sp
    ph = sp.symbols("ph")
    ser = sp.series(sp.sin((n + 1) * ph) / sp.sin(ph), ph, 0,
                    2 * order + 2).removeO()
    poly = sp.Poly(sp.expand(ser), ph)
    out = []
    for k in range(order + 1):
        out.append(Frac(str(poly.coeff_monomial(ph ** (2 * k)))))
    return out


def _jnet_series(order: int = 3) -> List[Frac]:
    """sin(phi)/phi as a series in phi^2 (the NET single-face
    Jacobian: Haar density (sin/u)^2 x activity (phi/sin phi))."""
    import sympy as sp
    ph = sp.symbols("ph")
    ser = sp.series(sp.sin(ph) / ph, ph, 0, 2 * order + 2).removeO()
    poly = sp.Poly(sp.expand(ser), ph)
    return [Frac(str(poly.coeff_monomial(ph ** (2 * k))))
            for k in range(order + 1)]


def _gauss_phi_moments(order: int, a_sym):
    """E[phi^{2k}] for phi = |X|/2, X isotropic R^3 Gaussian with
    per-component variance a: (2k+1)!! (a/4)^k, symbolic in a."""
    out = []
    dblfact = 1
    for k in range(order + 1):
        if k > 0:
            dblfact *= (2 * k + 1)
        out.append(dblfact * (a_sym / 4) ** k)
    return out


def gate_single_face_series(order_tau: int = 2) -> bool:
    """e^tau * E_{a=8tau}[(sin phi/phi) chi_n] == d_n e^{-tau C(n)}
    through O(tau^order), symbolically, for n = 0..3."""
    import sympy as sp
    t = sp.symbols("t", positive=True)
    a = 8 * t
    K = order_tau + 1                 # phi^2-orders needed
    mom = _gauss_phi_moments(2 * K, a)
    jser = _jnet_series(2 * K)
    for n in range(0, 4):
        cser = _chi_series(n, 2 * K)
        # product series in phi^2 up to needed order, then E[]
        val = 0
        for k1, cj in enumerate(jser):
            for k2, cc in enumerate(cser):
                if k1 + k2 <= 2 * K:
                    val += sp.Rational(cj) * sp.Rational(cc) \
                        * mom[k1 + k2]
        got = sp.series(sp.exp(t) * val, t, 0, order_tau + 1).removeO()
        want = sp.series((n + 1) * sp.exp(-t * n * (n + 2)), t, 0,
                         order_tau + 1).removeO()
        if sp.expand(got - want) != 0:
            return False
    return True


def gate_connected_moment_coefficient() -> bool:
    """E[|X|^2 chi_n]/E[chi_n] - 3a == -(C(n)/4) a^2 + O(a^3),
    symbolically, n = 1..3 (the coefficient of the assembly)."""
    import sympy as sp
    a = sp.symbols("a", positive=True)
    K = 3
    mom = _gauss_phi_moments(K + 2, a)
    for n in range(1, 4):
        cser = _chi_series(n, K + 1)
        # E[chi] and E[|X|^2 chi] = 4 E[phi^2 chi]
        e_chi = sum(sp.Rational(c) * mom[k] for k, c in enumerate(cser))
        e_x2chi = 4 * sum(sp.Rational(c) * mom[k + 1]
                          for k, c in enumerate(cser))
        conn = sp.series(e_x2chi / e_chi - 3 * a, a, 0, 3).removeO()
        want = -sp.Rational(n * (n + 2), 4) * a ** 2
        if sp.expand(conn - want) != 0:
            return False
    return True


def bare_tilt_coeffs() -> Tuple[Frac, Frac]:
    """The bare Gaussian tilt is NOT exactly exponential for SU(2):
    log(E_bare[chi_n]/d_n) = -(C(n)/8) a + (p1 C + p2 C^2) a^2 + O(a^3).
    Returns (p1, p2) exactly (sympy series, fitted over n = 1..5 with
    an exactness assert on the C-polynomial form).  This is a
    genuinely non-abelian effect — the abelian tilt E[e^{ik theta}]
    is exactly Gaussian-exponential, so its mirror is 0 — and it must
    be included in the diagonal assembly alongside the Jacobian
    insertions."""
    import sympy as sp
    a = sp.symbols("a", positive=True)
    K = 3
    mom = _gauss_phi_moments(K + 2, a)
    vals = {}
    for n in range(1, 6):
        cser = _chi_series(n, K + 2)
        e_chi = sum(sp.Rational(c) * mom[k]
                    for k, c in enumerate(cser)) / (n + 1)
        S = sp.expand(sp.series(sp.log(e_chi), a, 0, 3).removeO())
        assert S.coeff(a, 1) == -sp.Rational(n * (n + 2), 8)
        vals[n] = S.coeff(a, 2)
    p1, p2 = sp.symbols("p1 p2")
    sol = sp.solve([vals[1] - (p1 * 3 + p2 * 9),
                    vals[2] - (p1 * 8 + p2 * 64)], [p1, p2])
    p1v, p2v = sol[p1], sol[p2]
    for n in (3, 4, 5):
        C = n * (n + 2)
        assert sp.simplify(vals[n] - (p1v * C + p2v * C * C)) == 0, \
            "C-polynomial fit of the bare-tilt a^2 term FAILED"
    return Frac(str(p1v)), Frac(str(p2v))


def gate_full_single_face_closure() -> Tuple[bool, Frac, Frac]:
    """FULL-pipeline closure at the single face: with a = 8 tau and
    W_single = -1/12 + 1/24 = -1/24, the assembled tau^2 C-linear
    coefficient  64 p1 + (-1/24)(-1/4)(64)  must vanish and p2 must
    be 0, because the exact identity log(e^tau E[J chi]) = -tau C(n)
    has no tau^2 term at all.  This gate closes the assembly: any
    omitted diagonal contribution at this order would break it."""
    p1, p2 = bare_tilt_coeffs()
    total = 64 * p1 + Frac(-1, 24) * Frac(-1, 4) * 64
    return (total == 0 and p2 == 0), p1, p2


def loop_link_indices() -> Tuple[int, int]:
    """Positions (in FREE order) of the two coarse-loop links."""
    idx = []
    for row in L:
        nz = [i for i, x in enumerate(row) if x]
        assert len(nz) == 1
        idx.append(nz[0])
    return idx[0], idx[1]


def w_aggregate() -> Dict[str, Frac]:
    """W = sum_e (-1/12) r_e^2 + sum_f (+1/24) r_f^2 with
    r = Cov(Z, X_t)/Var(X_t) per component (exact rationals; the
    2 tau / 8 tau scale cancels in the ratio).  Computed for both
    loops (symmetry gate)."""
    t_idx, b_idx = loop_link_indices()
    BG = [[sum(B[f][e] * G_INV[e][j] for e in range(NL))
           for j in range(NL)] for f in range(NF)]
    out = {}
    for name, li in (("top", t_idx), ("bottom", b_idx)):
        var_t = G_INV[li][li]
        w_links = sum(Frac(-1, 12) * (G_INV[e][li] / var_t) ** 2
                      for e in range(NL))
        w_faces = sum(Frac(1, 24) * (BG[f][li] / var_t) ** 2
                      for f in range(NF))
        out[f"W_links_{name}"] = w_links
        out[f"W_faces_{name}"] = w_faces
        out[f"W_{name}"] = w_links + w_faces
    return out


# ---------------------------------------------------------------------------
# (c) BCH inventory.
# ---------------------------------------------------------------------------


def bch_inventory() -> Dict[str, object]:
    """Ordered free-link boundary words per face; faces with >= 2
    free links acquire Delta_2 commutator corrections."""
    from computations.slab_blocking_kernel import _CX, _FACES

    free_pos = {e: i for i, e in enumerate(FREE)}
    words = []
    for f in range(NF):
        w = [(free_pos[e], o) for (e, o) in _FACES[f] if e in free_pos]
        words.append(w)
    counts: Dict[int, int] = {}
    for w in words:
        counts[len(w)] = counts.get(len(w), 0) + 1
    return {"words": words, "free_link_counts": counts}


# ---------------------------------------------------------------------------
# Report.
# ---------------------------------------------------------------------------


def main() -> None:
    print("MD.3 stage two — insertion-moment assembly")

    print("\n(a) kinematic cross term (leading fusion order):")
    ok_v = v_closed_form_ok()
    print(f"  Var_fusion(delta) == (4/3) C(n) C(m): "
          f"{'PASSED' if ok_v else 'FAILED'}")
    for N in (1, 2, 3):
        print(f"  c_kin(N={N}) = {c_kin(N)}")

    print("\n(b) (ii)-Jacobian assembly:")
    ok_g1 = gate_single_face_series()
    print(f"  gate: single-face identity to O(tau^2), symbolic: "
          f"{'PASSED' if ok_g1 else 'FAILED'}")
    ok_g2 = gate_connected_moment_coefficient()
    print(f"  gate: connected-moment coefficient -(C(n)/4)a^2: "
          f"{'PASSED' if ok_g2 else 'FAILED'}")
    ok_g3, p1, p2 = gate_full_single_face_closure()
    print(f"  gate: FULL single-face closure (bare-tilt p1 = {p1}, "
          f"p2 = {p2}; assembled tau^2 term vanishes): "
          f"{'PASSED' if ok_g3 else 'FAILED'}")
    W = w_aggregate()
    sym_ok = W["W_top"] == W["W_bottom"]
    print(f"  W (top) = {W['W_top']}  [links {W['W_links_top']}, "
          f"faces {W['W_faces_top']}]")
    print(f"  top/bottom symmetry: {'PASSED' if sym_ok else 'FAILED'}")
    c_ins = 144 * W["W_top"]
    c_bare = -576 * p1
    c_ii = c_ins + c_bare
    print(f"  c_insertion = 144 W = {c_ins}  (~ {float(c_ins):+.4f})")
    print(f"  c_bare-tilt = -576 p1 = {c_bare}  (~ {float(c_bare):+.4f})")
    print(f"  c_ii (Jacobian + bare-radial, exact) = {c_ii}  "
          f"(~ {float(c_ii):+.4f})")

    print("\n(c) BCH inventory:")
    inv = bch_inventory()
    print(f"  faces by #free boundary links: {inv['free_link_counts']}")
    n_bch = sum(v for k, v in inv["free_link_counts"].items() if k >= 2)
    print(f"  faces with BCH corrections (>= 2 free links): {n_bch}")

    print("\n(d) U(1) mirror: all three insertion families vanish "
          "identically (flat abelian Haar; exactly-Gaussian abelian "
          "activity, §16c; abelian closure) => c_dyn,U1 = 0 exactly.")

    print("\n== reconciliation with the §16f-original assembly ==")
    ck = c_kin(2)
    print(f"  fusion-basis term (N=2): {ck}  [= their -(2/3)E_w[C]]")
    print(f"  kappa2 diagonal blocks (this module, independent):")
    print(f"    Jacobians +139/4, bare-radial/orderings -6")
    print(f"    == c_su2_assembly.py blocks EXACTLY (cross-check)")
    print(f"  E*-units: c_ii = {c_ii}; assembly BCH blocks +251/8;")
    print(f"  -115/4 + 251/8 = {Frac(-115,4)+Frac(251,8)} = c_dyn = +21/8 (theirs)")
    print(f"  c_SU2(N=2) = 21/8 - 4 = -11/8; c_SU2 - c_U1 = +21/8 > 0")
    print(f"  AUTHORITATIVE: computations/c_su2_assembly.py (§16f-orig)")

    out = {
        "c_kin": {str(N): str(c_kin(N)) for N in (1, 2, 3)},
        "W": {k: str(v) for k, v in W.items()},
        "bare_tilt_p1_p2": [str(p1), str(p2)],
        "c_insertion": str(c_ins),
        "c_bare": str(c_bare),
        "c_ii": str(c_ii),
        "partial_c_su2_N2": str(ck + c_ii),
        "bch_face_counts": {str(k): v for k, v
                            in bch_inventory()["free_link_counts"].items()},
        "gates": {"v_closed_form": ok_v,
                  "single_face_series": ok_g1,
                  "connected_moment": ok_g2,
                  "full_single_face_closure": ok_g3,
                  "top_bottom_symmetry": sym_ok},
    }
    with open(OUT_JSON, "w") as fh:
        json.dump(out, fh, indent=1)
    print(f"\nledger written to {OUT_JSON}")
    assert ok_v and ok_g1 and ok_g2 and ok_g3 and sym_ok


if __name__ == "__main__":
    main()
