"""MD.1 — the observable-matched flow map on the DP.2 slab (definition layer).

**Why this module exists (work_plan §16, Milestone MD.1).**  The 4-vs-1
ambiguity of the marginality dichotomy lives entirely in what "s'" means.
The legacy DP.2 protocol (computations/dp2_measure.py) DEFINES s' by
least-squares fitting log(v_n/d_n) against C(n) on the flowed envelope
v = T e_s — a float fit that projects the blocked kernel back onto
single-plaquette form, building the 2D rule in at tree level and mixing
every channel with its vacuum dressing.  This module replaces the fit
with two OBSERVABLE-matched definitions, both exact:

  **Separator matching (primary).**  The OS Gram of the one-step blocked
  slab (DP.3 pairing: G = T for SU(2), G[n,m] = T[-n,m] for U(1);
  antilinear link reflection theta: z -> 1-z) is a PSD matrix of exact
  rationals at each rational s, expressed in the Haar-orthonormal
  character basis of the coarse loop.  Its two leading eigenvalues
  lambda_0 > lambda_1 give the located one-step separator
  sigma(s) = lambda_1/lambda_0 — the vacuum-orthogonalized (connected)
  transfer content, the finite-matrix analogue of the located second
  eigenvalue (Continuum/LocatedSpectralGap).  The matched coupling s'
  is the coupling at which the FIXED-POINT one-step kernel
  diag(d_n s'^{C(n)}) — the heat-kernel envelope form certified exactly
  by the repo's 2D gates (open-disk and frozen-side schemes) — has the
  same separator:

      SU(2):  d_1 s'^{C(1)} / d_0 = sigma(s)   i.e.  2 s'^3 = sigma(s)
      U(1):   s'^{C(1)}          = sigma(s)   i.e.    s'   = sigma(s)

  Eigenvalues are algebraic, not rational, so the deliverable is a
  CERTIFIED RATIONAL WINDOW: characteristic polynomial (exact
  Faddeev–LeVerrier), Sturm isolation of the two leading roots,
  bisection to prescribed relative width, interval arithmetic for the
  ratio and the C(1)-th root.  No floats anywhere in a window.

  **Pair matching (control).**  On the flowed envelope v = T e_s
  (legacy sector rule kept verbatim), the pairwise matched coupling of
  channels a < b is the exact rational

      s'_{ab}^{C(b)-C(a)} = (v_b d_a) / (v_a d_b),

  i.e. the coupling at which the fixed-point envelope reproduces the
  observed ratio of channels a and b.  The (0,1) pair is the control
  headline (SU(2): s'^3 = v_1/(2 v_0); U(1): s' = v_1/v_0 — for U(1)
  this equals rho_1 * s^4 with rho_1 the banked exact witness of
  DP.6-U1).  The spread of the pairwise ledger is the exact corridor
  content; the legacy float fit is reproduced alongside as comparison,
  never as a claim.

**Scheme-covariance fence (work_plan §16).**  What must agree across
these definitions is the SIGN of the defect against the 2D rule
(s' vs s^4) and the s -> 1 dichotomy class — not the value.  Both
definitions are emitted for both groups in every run (gate g3).

**Gates.**
  g1  the legacy protocol reproduces the banked DP.2/DP.6-U1 numbers to
      the digit (SU(2) floats s'=0.034121 / 1.816737 / 31.8848 at
      s=1/2, 0.249521 / 0.792869 / 12.5124 at s=3/4; U(1) exact
      rationals v_0, v_1, rho_1, rho_2 at M=2, s=1/2), and the two
      saved SU(2) kernel files agree entry by entry;
  g2  the U(1) mirror runs on the identical boundary data (imported
      slab geometry; flip-lattice certificate; z-flip / charge
      conjugation / conjugation-necessity gates), matching the saved
      DP.3 kernels exactly;
  g3  both matchings, both groups, one ledger per run.

**Truncation.**  M is a scheme parameter.  SU(2) M=1 is exact and
complete (N=3; the spin-3 row is exactly zero and is stripped from the
Gram, reported).  SU(2) M=2 entries are loaded from
computations/dp3_m2_entries.json and are PROVISIONAL above each entry's
final window (exact_below_E); matched values at M=2 are tagged so.
U(1) is exact at every M (finite lattice-point count).

Run:  python -m computations.flow_matching            (full ladder)
      python -m computations.flow_matching --quick    (s = 1/2 only)
"""

from __future__ import annotations

import json
import math
import os
import sys
from fractions import Fraction
from typing import Dict, List, Optional, Sequence, Tuple

HERE = os.path.dirname(os.path.abspath(__file__))
SPoly = Dict[int, Fraction]
Frac = Fraction

RP_JSON = os.path.join(HERE, "dp3_rp_results.json")
DP2_JSON = os.path.join(HERE, "dp2_kernel_N3_M1.json")
M2_JSON = os.path.join(HERE, "dp3_m2_entries.json")
OUT_JSON = os.path.join(HERE, "flow_matching_results.json")

# ---------------------------------------------------------------------------
# Group data (kept literal so the two columns of every table are explicit).
# ---------------------------------------------------------------------------


def dim_su2(n: int) -> int:
    return n + 1


def cas_su2(n: int) -> int:
    return n * (n + 2)          # 4x Casimir; s = e^{-t/4}


def dim_u1(m: int) -> int:
    return 1


def cas_u1(m: int) -> int:
    return m * m                # Casimir; s = e^{-t}


# ---------------------------------------------------------------------------
# Exact polynomial / kernel loading.
# ---------------------------------------------------------------------------


def _poly_load(d) -> SPoly:
    return {int(k): Frac(a, b) for k, (a, b) in d.items()}


def p_eval(p: SPoly, s: Frac) -> Frac:
    return sum((c * s ** k for k, c in p.items()), Frac(0))


def load_su2_M1() -> Dict[Tuple[int, int], SPoly]:
    """SU(2) blocked kernel, N=3, M=1, from the DP.3 record; gate:
    byte-equal to the independently saved DP.2 kernel file."""
    D = json.load(open(RP_JSON))
    T: Dict[Tuple[int, int], SPoly] = {}
    for key, poly in D["su2_kernel"].items():
        n, m = map(int, key.split(","))
        e = _poly_load(poly)
        T[(n, m)] = e
        T[(m, n)] = e
    D2 = json.load(open(DP2_JSON))
    for key, poly in D2["T"].items():
        n, m = map(int, key.split(","))
        assert T[(n, m)] == _poly_load(poly), (
            f"g1 cross-file gate FAILED at T[{n},{m}]")
    return T


def load_su2_M2() -> Tuple[Dict[Tuple[int, int], SPoly], Dict[Tuple[int, int], int]]:
    """SU(2) blocked kernel, N=2, M=2, from dp3_m2_entries.json.
    Returns (entries, final_window) where final_window[(n,m)] is the
    exponent below which the entry is FINAL (per-exponent predicate);
    coefficients at or above it are PROVISIONAL (unreached configs)."""
    D = json.load(open(M2_JSON))
    T: Dict[Tuple[int, int], SPoly] = {}
    win: Dict[Tuple[int, int], int] = {}
    for key, rec in D.items():
        n, m = map(int, key.split(","))
        e = _poly_load(rec["poly"])
        T[(n, m)] = e
        T[(m, n)] = e
        w = int(rec["exact_below_E"])
        win[(n, m)] = w
        win[(m, n)] = w
    return T, win


def load_u1_M1() -> Dict[Tuple[int, int], SPoly]:
    D = json.load(open(RP_JSON))
    return {tuple(map(int, k.split(","))): _poly_load(p)
            for k, p in D["u1_kernel"].items()}


def build_u1(N: int, M: int) -> Dict[Tuple[int, int], SPoly]:
    """Fresh U(1) kernel on the identical slab boundary data (gate g2:
    geometry imported from the SU(2) reference; flip-lattice
    certificate; symmetry and conjugation-necessity gates; agreement
    with the saved DP.3 kernels where they overlap)."""
    from computations.dp6_u1_slab_blocking import (
        certify_kernel_basis,
        kernel_entry_u1,
    )

    assert certify_kernel_basis(), "g2: U(1) flip-lattice certificate FAILED"
    T = {(n, m): kernel_entry_u1(n, m, M)
         for n in range(-N, N + 1) for m in range(-N, N + 1)}
    for n in range(-N, N + 1):
        for m in range(-N, N + 1):
            assert T[(n, m)] == T[(m, n)], "g2: U(1) z-flip gate FAILED"
            assert T[(n, m)] == T[(-n, -m)], "g2: U(1) charge-conj FAILED"
    if M >= 1 and N >= 1:
        assert T[(1, 1)] != T[(-1, 1)], "g2: conjugation-necessity FAILED"
    if M == 1:
        saved = load_u1_M1()
        for (n, m), e in T.items():
            if (n, m) in saved:
                assert e == saved[(n, m)], (
                    f"g2: U(1) M=1 mismatch vs DP.3 record at T[{n},{m}]")
    return T


# ---------------------------------------------------------------------------
# OS Grams (DP.3 pairing conventions, verbatim).
# ---------------------------------------------------------------------------


def gram_su2(T, basis: Sequence[int]):
    return [[dict(T[(n, m)]) for m in basis] for n in basis]


def gram_u1(T, basis: Sequence[int]):
    return [[dict(T[(-n, m)]) for m in basis] for n in basis]


def strip_zero_rows(G, basis):
    """Drop exact-zero rows/columns (PSD-neutral; reported)."""
    k = len(G)
    zero = [i for i in range(k) if all(not G[i][j] for j in range(k))]
    keep = [i for i in range(k) if i not in zero]
    Gr = [[G[i][j] for j in keep] for i in keep]
    return Gr, [basis[i] for i in keep], [basis[i] for i in zero]


# ---------------------------------------------------------------------------
# Exact symmetric-matrix spectrum machinery: characteristic polynomial,
# Sturm isolation, certified rational windows.  Coefficient lists are
# dense, low degree first.
# ---------------------------------------------------------------------------


def charpoly(A: List[List[Frac]]) -> List[Frac]:
    """det(lambda I - A) by Faddeev–LeVerrier, exact."""
    k = len(A)
    coeffs = [Frac(0)] * (k + 1)
    coeffs[k] = Frac(1)
    Mmat = [[Frac(0)] * k for _ in range(k)]
    c = Frac(1)
    for i in range(1, k + 1):
        # M <- A (M + c I)
        B = [[Mmat[r][cc] + (c if r == cc else 0) for cc in range(k)]
             for r in range(k)]
        Mmat = [[sum(A[r][t] * B[t][cc] for t in range(k))
                 for cc in range(k)] for r in range(k)]
        tr = sum(Mmat[r][r] for r in range(k))
        c = -tr / i
        coeffs[k - i] = c
    return coeffs


def poly_eval(c: List[Frac], x: Frac) -> Frac:
    out = Frac(0)
    for a in reversed(c):
        out = out * x + a
    return out


def poly_deriv(c: List[Frac]) -> List[Frac]:
    return [i * a for i, a in enumerate(c)][1:] or [Frac(0)]


def _poly_trim(c: List[Frac]) -> List[Frac]:
    while len(c) > 1 and c[-1] == 0:
        c = c[:-1]
    return c


def _poly_mod(a: List[Frac], b: List[Frac]) -> List[Frac]:
    a = a[:]
    b = _poly_trim(b)
    while len(a) >= len(b) and _poly_trim(a) != [Frac(0)]:
        a = _poly_trim(a)
        if len(a) < len(b):
            break
        f = a[-1] / b[-1]
        sh = len(a) - len(b)
        for i in range(len(b)):
            a[sh + i] -= f * b[i]
        a = a[:-1]
    return _poly_trim(a) if a else [Frac(0)]


def _poly_gcd(a: List[Frac], b: List[Frac]) -> List[Frac]:
    a, b = _poly_trim(a), _poly_trim(b)
    while b != [Frac(0)]:
        a, b = b, _poly_mod(a, b)
    if a[-1] != 0:
        a = [x / a[-1] for x in a]
    return a


def squarefree(c: List[Frac]) -> List[Frac]:
    g = _poly_gcd(c, poly_deriv(c))
    if len(g) == 1:
        return _poly_trim(c)
    # exact division c / g
    q, r = _poly_divmod(c, g)
    assert _poly_trim(r) == [Frac(0)]
    return _poly_trim(q)


def _poly_divmod(a: List[Frac], b: List[Frac]):
    a = _poly_trim(a)[:]
    b = _poly_trim(b)
    q = [Frac(0)] * max(1, len(a) - len(b) + 1)
    while len(a) >= len(b) and _poly_trim(a) != [Frac(0)]:
        f = a[-1] / b[-1]
        sh = len(a) - len(b)
        q[sh] = f
        for i in range(len(b)):
            a[sh + i] -= f * b[i]
        a = a[:-1]
        if not a:
            a = [Frac(0)]
    return q, a


def sturm_chain(c: List[Frac]) -> List[List[Frac]]:
    chain = [_poly_trim(c), _poly_trim(poly_deriv(c))]
    while chain[-1] != [Frac(0)] and len(chain[-1]) > 1:
        r = _poly_mod(chain[-2], chain[-1])
        chain.append([-x for x in r])
    if chain[-1] == [Frac(0)]:
        chain.pop()
    return chain


def _sign_changes(chain, x: Frac) -> int:
    signs = []
    for p in chain:
        v = poly_eval(p, x)
        if v:
            signs.append(1 if v > 0 else -1)
    return sum(1 for a, b in zip(signs, signs[1:]) if a != b)


def roots_in(chain, a: Frac, b: Frac) -> int:
    """Distinct real roots in (a, b] (Sturm; chain of a squarefree poly)."""
    return _sign_changes(chain, a) - _sign_changes(chain, b)


def isolate_top_two(A: List[List[Frac]], rel_tol: Frac = Frac(1, 10**30)):
    """Certified windows for the two leading eigenvalues of a symmetric
    rational matrix.  Returns ((lo0,hi0), (lo1,hi1), meta)."""
    cp = charpoly(A)
    sf = squarefree(cp)
    chain = sturm_chain(sf)
    # Cauchy root bound
    lead = sf[-1]
    B = 1 + max(abs(x / lead) for x in sf[:-1])
    total = roots_in(chain, -B, B)
    assert total >= 2, "fewer than two distinct eigenvalues"
    # peel off the largest root's isolating interval, then the second
    windows: List[Tuple[Frac, Frac]] = []
    hi = B
    lo = -B
    # subdivide from the top until the top two roots are isolated
    stack = [(lo, hi)]
    ivs: List[Tuple[Frac, Frac]] = []
    while stack:
        a, b = stack.pop()
        n = roots_in(chain, a, b)
        if n == 0:
            continue
        if n == 1:
            ivs.append((a, b))
            continue
        m = (a + b) / 2
        # ensure m is not a root (perturb if it is)
        while poly_eval(sf, m) == 0:
            m = m + (b - a) / 1000
        stack.append((a, m))
        stack.append((m, b))
    ivs.sort(key=lambda iv: iv[0], reverse=True)
    assert len(ivs) >= 2
    top2 = ivs[:2]

    def refine(iv, tol_abs):
        a, b = iv
        while b - a > tol_abs:
            m = (a + b) / 2
            if poly_eval(sf, m) == 0:
                # a root hit exactly: collapse the window to the point
                return (m, m)
            if roots_in(chain, a, m) == 1:
                b = m
            else:
                a = m
        return (a, b)

    # refine: absolute tolerance scaled to each window's magnitude
    out = []
    for a, b in top2:
        scale = max(abs(a), abs(b), Frac(1, 10**6))
        out.append(refine((a, b), scale * rel_tol))
    # multiplicity honesty: count multiple roots inside the top window
    g = _poly_gcd(cp, poly_deriv(cp))
    mult_flag = False
    if len(g) > 1:
        gch = sturm_chain(squarefree(g))
        mult_flag = roots_in(gch, out[0][0], out[0][1]) > 0
    meta = {"charpoly_degree": len(cp) - 1,
            "distinct_roots": total,
            "top_root_multiple": mult_flag}
    return out[0], out[1], meta


def ratio_window(w1, w0):
    """Interval quotient w1/w0 for positive windows."""
    (lo1, hi1), (lo0, hi0) = w1, w0
    assert lo0 > 0, "leading eigenvalue window not strictly positive"
    lo1 = max(lo1, Frac(0))
    return (lo1 / hi0, hi1 / lo0)


def kth_root_window(w, k: int, rel_tol: Frac = Frac(1, 10**18)):
    """Certified window for w^(1/k), w a positive rational window."""
    lo, hi = w
    assert lo >= 0

    def root(x: Frac, is_lower: bool) -> Tuple[Frac, Frac]:
        if x == 0:
            return (Frac(0), Frac(0))
        a, b = Frac(0), max(Frac(1), x)
        while b ** k < x:
            b *= 2
        while b - a > b * rel_tol:
            m = (a + b) / 2
            if m ** k <= x:
                a = m
            else:
                b = m
        return (a, b)

    rlo = root(lo, True)
    rhi = root(hi, False)
    return (rlo[0], rhi[1])


# ---------------------------------------------------------------------------
# Definition 1: separator matching.
# ---------------------------------------------------------------------------


def separator_match(G_polys, basis, s: Frac, cas1: int, d1: int,
                    rel_tol: Frac = Frac(1, 10**30)) -> dict:
    """Matched coupling window from the one-step OS Gram separator.

    sigma(s) = lambda_1/lambda_0 of G(s); matched s' solves
    d1 * s'^cas1 = sigma(s).  Returns exact windows for sigma, s'^cas1,
    and s' (plus float images, scouting only)."""
    Gr, kept, zero_rows = strip_zero_rows(G_polys, basis)
    A = [[p_eval(Gr[i][j], s) for j in range(len(Gr))]
         for i in range(len(Gr))]
    # symmetry sanity (pairing extracted symmetric; nothing symmetrized)
    for i in range(len(A)):
        for j in range(len(A)):
            assert A[i][j] == A[j][i]
    w0, w1, meta = isolate_top_two(A, rel_tol)
    sig = ratio_window(w1, w0)
    spk = (sig[0] / d1, sig[1] / d1)           # window for s'^cas1
    sp = kth_root_window(spk, cas1)
    return {
        "basis_kept": kept, "zero_rows": zero_rows,
        "lambda0": w0, "lambda1": w1, "sigma": sig,
        "s_prime_pow": spk, "cas1": cas1, "d1": d1,
        "s_prime": sp,
        "s_prime_float": (float(sp[0]) + float(sp[1])) / 2,
        "meta": meta,
    }


# ---------------------------------------------------------------------------
# Definition 2: pair matching on the flowed envelope (control), plus the
# legacy float fit (comparison only).
# ---------------------------------------------------------------------------


def flowed_image(T, cand: Sequence[int], s: Frac, dim_f, cas_f):
    """Legacy sector rule + flowed envelope, verbatim semantics of
    computations/dp2_measure.py / dp6_u1_slab_blocking.measure."""
    idx = [n for n in cand
           if all(p_eval(T[(n, m)], s) > 0 for m in cand)]
    v = {}
    for n in idx:
        v[n] = sum(p_eval(T[(n, m)], s) * Frac(dim_f(m)) * s ** cas_f(m)
                   for m in idx)
    return idx, v


def pair_match(v: Dict[int, Frac], dim_f, cas_f) -> dict:
    """Exact pairwise matched couplings on the flowed image.

    For channels a < b (nonneg labels, v > 0):
        s'_{ab}^{cas(b)-cas(a)} = (v_b * d_a) / (v_a * d_b).
    Root windows are certified; the raw rational powers are exact."""
    labels = sorted(n for n in v if n >= 0)
    pairs = {}
    for i, a in enumerate(labels):
        for b in labels[i + 1:]:
            k = cas_f(b) - cas_f(a)
            if k <= 0:
                continue
            r = (v[b] * dim_f(a)) / (v[a] * dim_f(b))
            w = kth_root_window((r, r), k)
            pairs[f"{a},{b}"] = {
                "power": k, "value_pow": r, "window": w,
                "float": (float(w[0]) + float(w[1])) / 2,
            }
    return pairs


def legacy_fit(v: Dict[int, Frac], dim_f, cas_f):
    """The legacy least-squares fit (dp2_measure protocol) — floats,
    comparison only, never a claim."""
    xs = [cas_f(n) for n in v]
    ys = [math.log(float(val / dim_f(n))) for n, val in v.items()]
    k = len(xs)
    xb, yb = sum(xs) / k, sum(ys) / k
    den = sum((x - xb) ** 2 for x in xs)
    if den == 0:
        return None, None
    slope = sum((x - xb) * (y - yb) for x, y in zip(xs, ys)) / den
    resid = [y - (yb + slope * (x - xb)) for x, y in zip(xs, ys)]
    return math.exp(slope), max(resid) - min(resid)


# ---------------------------------------------------------------------------
# Gate g1: the banked numbers, to the digit.
# ---------------------------------------------------------------------------


def gate_g1_su2(T) -> None:
    cand = [n for n in range(4) if T[(n, n)]]
    for s, want_sp, want_w in [
        (Frac(1, 2), "0.034121", "1.816737"),
        (Frac(3, 4), "0.249521", "0.792869"),
    ]:
        idx, v = flowed_image(T, cand, s, dim_su2, cas_su2)
        assert idx == [0, 1, 2], f"g1: sector at s={s} is {idx}"
        sp, w = legacy_fit(v, dim_su2, cas_su2)
        assert f"{sp:.6f}" == want_sp, (
            f"g1 FAILED: fitted s'={sp:.6f} != {want_sp} at s={s}")
        assert f"{w:.6f}" == want_w, (
            f"g1 FAILED: corridor {w:.6f} != {want_w} at s={s}")
    # whole-cone Birkhoff diameters (banked: 31.8848 / 12.5124)
    for s, want_d in [(Frac(1, 2), "31.8848"), (Frac(3, 4), "12.5124")]:
        idx = [0, 1, 2]
        worst = Frac(1)
        for a in range(len(idx)):
            for b in range(a + 1, len(idx)):
                ca = [p_eval(T[(n, idx[a])], s) for n in idx]
                cb = [p_eval(T[(n, idx[b])], s) for n in idx]
                r1 = max(x / y for x, y in zip(ca, cb))
                r2 = max(y / x for x, y in zip(ca, cb))
                worst = max(worst, r1 * r2)
        d = math.log(float(worst))
        assert f"{d:.4f}" == want_d, (
            f"g1 FAILED: Birkhoff {d:.4f} != {want_d} at s={s}")


def gate_g1_u1(T_M2) -> None:
    """DP.6-U1 banked exact witnesses at M=2, s=1/2 (test pins)."""
    from computations.dp6_u1_slab_blocking import measure
    r = measure(T_M2, 2, Frac(1, 2))
    assert r["sector"] == [-2, -1, 0, 1, 2], "g1-U1: sector"
    assert r["v"][0] == Frac(11258810062447479809, 9223372036854775808)
    assert r["v"][1] == Frac(437335326546529, 4503599627370496)
    assert r["ratios"][1] == Frac(14330603980276662272,
                                  11258810062447479809)
    assert r["ratios"][1] > 1
    assert r["ratios"][2] == Frac(148520413760355041280,
                                  11258810062447479809)


# ---------------------------------------------------------------------------
# One measurement row (both definitions, one group, one s, one M).
# ---------------------------------------------------------------------------


def measure_row(group: str, T, basis, cand, s: Frac, M: int,
                provisional: Optional[Dict] = None) -> dict:
    if group == "su2":
        dim_f, cas_f, d1, c1 = dim_su2, cas_su2, dim_su2(1), cas_su2(1)
        G = gram_su2(T, basis)
    else:
        dim_f, cas_f, d1, c1 = dim_u1, cas_u1, dim_u1(1), cas_u1(1)
        G = gram_u1(T, basis)
    row = {"group": group, "s": str(s), "M": M}
    if provisional:
        row["provisional"] = provisional

    sep = separator_match(G, basis, s, c1, d1)
    row["separator"] = {
        "basis_kept": sep["basis_kept"], "zero_rows": sep["zero_rows"],
        "sigma_window": [str(x) for x in sep["sigma"]],
        "s_prime_pow_window": [str(x) for x in sep["s_prime_pow"]],
        "s_prime_window": [str(x) for x in sep["s_prime"]],
        "s_prime_float": sep["s_prime_float"],
        "meta": sep["meta"],
    }

    idx, v = flowed_image(T, cand, s, dim_f, cas_f)
    row["sector"] = idx
    if len([n for n in idx if n >= 0]) >= 2:
        pairs = pair_match(v, dim_f, cas_f)
        row["pairs"] = {
            k: {"power": p["power"],
                "value_pow": str(p["value_pow"]),
                "float": p["float"]}
            for k, p in pairs.items()}
        row["pair01_float"] = pairs["0,1"]["float"] if "0,1" in pairs else None
        sp, w = legacy_fit(v, dim_f, cas_f)
        row["legacy_fit"] = {"s_prime": sp, "corridor": w}

    s4 = s ** 4
    row["s4"] = str(s4)
    row["s4_float"] = float(s4)
    # defect signs (exact where the quantity is exact)
    verdicts = {}
    spw = sep["s_prime"]
    if spw[1] < s4:
        verdicts["separator_vs_s4"] = "below (super-renormalizing)"
    elif spw[0] > s4:
        verdicts["separator_vs_s4"] = "above (anti-renormalizing)"
    else:
        verdicts["separator_vs_s4"] = "window straddles s^4 — refine"
    if "pairs" in row and "0,1" in row["pairs"]:
        pk = row["pairs"]["0,1"]["power"]
        pv = Frac(row["pairs"]["0,1"]["value_pow"])
        ref = s4 ** pk
        verdicts["pair01_vs_s4"] = (
            "below (super-renormalizing)" if pv < ref
            else "above (anti-renormalizing)" if pv > ref else "equal")
    row["defect_sign"] = verdicts
    # tau'/tau floats (scouting only; the exact objects are the windows)
    ls = math.log(float(s))
    row["tau_ratio_float"] = {
        "separator": math.log(max(sep["s_prime_float"], 1e-300)) / ls,
        "pair01": (math.log(row["pair01_float"]) / ls
                   if row.get("pair01_float") else None),
        "legacy": (math.log(row["legacy_fit"]["s_prime"]) / ls
                   if row.get("legacy_fit", {}).get("s_prime") else None),
        "twoD_rule": 4.0,
    }
    return row


# ---------------------------------------------------------------------------
# Main.
# ---------------------------------------------------------------------------


def run(ladder: Sequence[Frac], u1_Ms=(2, 3), quick=False) -> dict:
    out = {"milestone": "MD.1 observable-matched flow map",
           "date": "2026-07-28",
           "rows": []}

    print("gate g1 (SU2 banked floats; U1 banked exact witnesses)...",
          flush=True)
    T_su2 = load_su2_M1()
    gate_g1_su2(T_su2)
    T_u1_M2 = build_u1(2, 2)
    gate_g1_u1(T_u1_M2)
    print("  g1 PASSED", flush=True)

    print("gate g2 (U1 mirror on identical boundary data)...", flush=True)
    T_u1_M1 = build_u1(3, 1)     # includes saved-kernel equality check
    print("  g2 PASSED", flush=True)

    su2_cand = [n for n in range(4) if T_su2[(n, n)]]
    su2_basis = [0, 1, 2, 3]

    T_su2_M2, win = load_su2_M2()
    su2_M2_basis = [0, 1, 2]
    su2_M2_cand = [0, 1, 2]
    prov = {"final_below_E": {f"{n},{m}": win[(n, m)]
                              for n in range(3) for m in range(n, 3)},
            "note": "SU(2) M=2 entries carry provisional tails above "
                    "their final windows (dp3_m2_entries.json)"}

    for s in ladder:
        print(f"  s = {s} ...", flush=True)
        out["rows"].append(
            measure_row("su2", T_su2, su2_basis, su2_cand, s, 1))
        out["rows"].append(
            measure_row("su2", T_su2_M2, su2_M2_basis, su2_M2_cand, s, 2,
                        provisional=prov))
        for M in u1_Ms:
            T = T_u1_M2 if M == 2 else build_u1(2, M)
            basis = [0, 1, -1, 2, -2]
            cand = list(range(-2, 3))
            out["rows"].append(measure_row("u1", T, basis, cand, s, M))
        if quick:
            break
    return out


def print_table(out: dict) -> None:
    print("=" * 78)
    print("Matched one-step flow (float images of certified windows; "
          "the JSON holds the exact objects)")
    print(f"{'group':5} {'M':>2} {'s':>7} | {'separator':>12} "
          f"{'pair01':>12} {'legacy':>12} {'s^4':>10} | tau'/tau "
          f"(sep, pair01, legacy)")
    for r in out["rows"]:
        tr = r["tau_ratio_float"]
        sep = r["separator"]["s_prime_float"]
        p01 = r.get("pair01_float")
        leg = (r.get("legacy_fit") or {}).get("s_prime")
        print(f"{r['group']:5} {r['M']:>2} {r['s']:>7} | {sep:12.3e} "
              f"{(p01 if p01 else float('nan')):12.3e} "
              f"{(leg if leg else float('nan')):12.3e} "
              f"{r['s4_float']:10.6f} | "
              f"{tr['separator']:.3f}, "
              f"{(tr['pair01'] if tr['pair01'] else float('nan')):.3f}, "
              f"{(tr['legacy'] if tr['legacy'] else float('nan')):.3f}"
              + ("   [prov. tails]" if "provisional" in r else ""))
        print(f"{'':24}defect sign: separator {r['defect_sign'].get('separator_vs_s4')}; "
              f"pair01 {r['defect_sign'].get('pair01_vs_s4')}")


def main() -> None:
    quick = "--quick" in sys.argv
    ladder = [Frac(1, 2)] if quick else [
        Frac(1, 4), Frac(1, 2), Frac(3, 4), Frac(9, 10)]
    out = run(ladder, quick=quick)
    with open(OUT_JSON, "w") as fh:
        json.dump(out, fh, indent=1, default=str)
    print_table(out)
    print(f"\nexact ledger written to {OUT_JSON}")


if __name__ == "__main__":
    main()
