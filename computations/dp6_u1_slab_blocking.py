"""DP.6-U1 — the U(1) contraction-step discriminator on the DP.2 slab.

**Question.**  DP.2 measured the SU(2) one-step blocking kernel on the
2x2x1 slab (owned-boundary scheme) and found s' = 0.0341 < s^4 = 0.0625
at s = 1/2 (flow FASTER than the 2D rule c'_n = c_n^4/d_n^3) with a
narrowing corridor (flowed log-width 1.82 vs the wheel readout's 2.23;
0.79 at s = 3/4).  Banked discriminator prediction: the U(1) analogue
should track its 2D rule s' = s^4 EXACTLY with corridor non-narrowing,
because univalence d_m = 1 kills the d^3 denominator.  This module runs
the identical one-step measurement with U(1) group data and decides.

**Group data.**  U(1) irreps are charges m in Z: d_m = 1,
chi_m(theta) = e^{i m theta}, fusion m (x) n = m + n (single path, no
recoupling, no 6j), Casimir C(m) = m^2, heat-kernel activity s^{m^2}.
Normalization fairness: SU(2) uses s = e^{-t/4} so the activity
exponent is the integer Casimir polynomial n(n+2) = 4 j(j+1); the U(1)
analogue takes s = e^{-t} so the exponent is the integer Casimir m^2.
In BOTH parametrizations the exact 2D blocking rule c'_n = c_n^4/d_n^3
reads s' = s^4 (SU(2): d_n s^{4 n(n+2)}; U(1): s^{4 m^2}), so the
"s' vs s^4" comparison is parametrization-consistent group by group —
the fair statement is the 2D-rule form, and that is what is measured.

**Geometry reuse (∂-consistency).**  The complex, the adapted spanning
tree, the face set (4 top tiles, 4 bottom tiles, 4 interior walls, 8
perimeter walls), and both coarse perimeter loops are IMPORTED from
``computations.slab_blocking_kernel`` (the SU(2) reference): _CX,
_FACES, _TOP, _BOTTOM, _LOOP_TOP, _LOOP_BOT, hilbert_diameter.  Every
U(1) face/loop winding vector is read off the same oriented edge paths
the SU(2) contraction consumes.

**The abelian kernel is a lattice-point count.**  Haar integration of
e^{i k theta} over U(1) gives delta_{k,0}, so the owned-boundary
kernel is exactly

  T_U1[n,m](s) = sum over face charges k in Z^20, |k_f| <= M,
                 with  sum_f k_f w_f + n L_top + m L_bot = 0
                 on every free edge,   of   s^{sum_f k_f^2}.

The constraint system has rank 16 (= #free edges) and its saturated
integer kernel is spanned by the four cube-boundary 2-cycles (Smith
invariants all 1 — certified at import: ``certify_kernel_basis``), so
the solution set is (uniform tiles) + (4-parameter cube-flip lattice)
and the sum is a finite exact enumeration at each truncation M.  Every
coefficient is a positive integer count: the abelian kernel has no
sign problem and no multiplicity structure — no recoupling exists to
interfere.

**Truncation stability (exact statement).**  Any configuration first
admitted at truncation M+1 has a face with |k_f| = M+1, so
T_{M+1} - T_M has minimal s-degree >= (M+1)^2: all monomials of degree
< (M+1)^2 are EXACTLY stable under M -> M+1.  Measured quantities at
the probed s values are reported with their M -> M+1 float agreement.

Run:  python -m computations.dp6_u1_slab_blocking [cutoff] [M]
"""

from __future__ import annotations

import itertools
import math
import sys
from fractions import Fraction
from typing import Dict, List, Sequence, Tuple

from computations.slab_blocking_kernel import (
    _CX,
    _FACES,
    _TOP,
    _BOTTOM,
    _WALLS,
    _LOOP_TOP,
    _LOOP_BOT,
    hilbert_diameter,
)

Frac = Fraction
SPoly = Dict[int, Fraction]

NF = len(_FACES)  # 20
NE = len(_CX.edges)  # 33


def dim_u1(m: int) -> int:
    """Every U(1) irrep is one-dimensional (univalence)."""
    return 1


def casimir_u1(m: int) -> int:
    """U(1) Casimir m^2 (activity exponent; s = e^{-t})."""
    return m * m


# ---------------------------------------------------------------------------
# Winding data read off the SU(2) reference geometry.
# ---------------------------------------------------------------------------


def _wind_all(path) -> List[int]:
    """Winding vector of an oriented edge path over ALL edges."""
    w = [0] * NE
    for ei, o in path:
        w[ei] += o
    return w


_W_FACE = [_wind_all(f) for f in _FACES]
_W_TOP_LOOP = _wind_all(_LOOP_TOP)
_W_BOT_LOOP = _wind_all(_LOOP_BOT)
_FREE = list(_CX.free)


def _coords():
    out = {}
    i = 0
    for x in range(3):
        for y in range(3):
            for z in range(2):
                out[i] = (x, y, z)
                i += 1
    return out


_COORDS = _coords()


def _face_center(fi: int):
    vs = set()
    for ei, _o in _FACES[fi]:
        a, b = _CX.edges[ei]
        vs.add(_COORDS[a])
        vs.add(_COORDS[b])
    return tuple(sum(v[d] for v in vs) / 4 for d in range(3))


def _cube_faces() -> List[List[int]]:
    """The six faces of each of the four unit cubes of the slab."""
    cubes = []
    for cx in (0, 1):
        for cy in (0, 1):
            cc = (cx + 0.5, cy + 0.5, 0.5)
            fs = [fi for fi in range(NF)
                  if sum(abs(a - b) for a, b in zip(_face_center(fi), cc))
                  == 0.5]
            assert len(fs) == 6
            cubes.append(fs)
    return cubes


_CUBES = _cube_faces()


def _cube_boundaries() -> List[List[int]]:
    """Signed 2-chains B_i (one per cube) with boundary ZERO on all 33
    edges — the generators of the charge-conserving flip lattice."""
    cols = []
    for fs in _CUBES:
        found = None
        for signs in itertools.product((1, -1), repeat=5):
            sg = (1,) + signs
            tot = [0] * NE
            for s_, fi in zip(sg, fs):
                for e in range(NE):
                    tot[e] += s_ * _W_FACE[fi][e]
            if all(t == 0 for t in tot):
                found = dict(zip(fs, sg))
                break
        assert found is not None, f"cube {fs}: no closed orientation"
        col = [0] * NF
        for fi, s_ in found.items():
            col[fi] = s_
        cols.append(col)
    return cols


_B = _cube_boundaries()


def _particular_signs() -> Tuple[Dict[int, int], Dict[int, int]]:
    """Signs sigma on the top (resp. bottom) tiles with
    sum sigma_f del(f) = -L on all 33 edges: the uniform-disk
    particular solution of the loop constraint."""
    def disk(tiles, L):
        for signs in itertools.product((1, -1), repeat=4):
            tot = [0] * NE
            for s_, fi in zip(signs, tiles):
                for e in range(NE):
                    tot[e] += s_ * _W_FACE[fi][e]
            if all(t == -l for t, l in zip(tot, L)):
                return dict(zip(tiles, signs))
        raise AssertionError("no signed disk found")

    return disk(_TOP, _W_TOP_LOOP), disk(_BOTTOM, _W_BOT_LOOP)


_SD_TOP, _SD_BOT = _particular_signs()


def certify_kernel_basis() -> bool:
    """Certify (i) the free-edge constraint matrix has rank 16 = #free
    edges, (ii) the four cube boundaries span its integer kernel
    SATURATEDLY (Smith invariant factors all 1), so the enumeration
    over the flip lattice is complete.  Uses sympy exact arithmetic."""
    import sympy
    from sympy.matrices.normalforms import smith_normal_form

    A = sympy.Matrix([[_W_FACE[f][e] for f in range(NF)] for e in _FREE])
    if A.rank() != len(_FREE):
        return False
    B = sympy.Matrix([[_B[c][f] for c in range(4)] for f in range(NF)])
    if not (A * B).is_zero_matrix:
        return False
    snf = smith_normal_form(B)
    invs = [snf[i, i] for i in range(4)]
    return invs == [1, 1, 1, 1]


# ---------------------------------------------------------------------------
# Kernel entries (all exact Fraction s-polynomials).
# ---------------------------------------------------------------------------


def _particular(n: int, m: int) -> List[int]:
    k0 = [0] * NF
    for fi, s_ in _SD_TOP.items():
        k0[fi] = n * s_
    for fi, s_ in _SD_BOT.items():
        k0[fi] = m * s_
    return k0


def kernel_entry_u1(n: int, m: int, M: int) -> SPoly:
    """T_U1[n,m] in the owned-boundary scheme, truncation |k_f| <= M.

    Exact finite enumeration: particular solution (uniform charged
    tiles) plus the cube-flip lattice c in Z^4.  Each cube's top tile
    lies in that cube alone, so |k0_tile + b c_i| <= M bounds every
    c_i completely — the enumeration box provably exhausts the
    solution set."""
    k0 = _particular(n, m)
    rng = []
    for i in range(4):
        fi = next(f for f in _CUBES[i] if f in _TOP)
        b = _B[i][fi]
        lo, hi = -(M + abs(n) + abs(m)) - 2, (M + abs(n) + abs(m)) + 2
        cands = [c for c in range(lo, hi + 1) if abs(k0[fi] + b * c) <= M]
        rng.append(cands)
    out: SPoly = {}
    for c in itertools.product(*rng):
        k = list(k0)
        for i, ci in enumerate(c):
            if ci:
                for fi in _CUBES[i]:
                    k[fi] += _B[i][fi] * ci
        if all(abs(v) <= M for v in k):
            p = sum(v * v for v in k)
            out[p] = out.get(p, Frac(0)) + 1
    return out


def kernel_entry_u1_tiles(n: int, m: int, M: int) -> SPoly:
    """Independent cross-check enumeration: sweep the EIGHT tile
    charges directly, derive the flip coordinates from each cube's top
    tile, and demand full 33-edge charge conservation of the completed
    configuration.  Same mathematical object, different parametrization
    and different (full-boundary) constraint check."""
    out: SPoly = {}
    k0 = _particular(n, m)
    tiles = list(_TOP)
    for kt in itertools.product(range(-M, M + 1), repeat=4):
        # cube flips are determined by the top tiles
        cs = []
        ok = True
        for i in range(4):
            fi = next(f for f in _CUBES[i] if f in _TOP)
            b = _B[i][fi]
            diff = kt[tiles.index(fi)] - k0[fi]
            if diff % b:
                ok = False
                break
            cs.append(diff // b)
        if not ok:
            continue
        k = list(k0)
        for i, ci in enumerate(cs):
            if ci:
                for fi in _CUBES[i]:
                    k[fi] += _B[i][fi] * ci
        if any(abs(v) > M for v in k):
            continue
        # full 33-edge conservation, independently of the lattice claim
        tot = [n * lt + m * lb for lt, lb in zip(_W_TOP_LOOP, _W_BOT_LOOP)]
        for fi in range(NF):
            if k[fi]:
                for e in range(NE):
                    tot[e] += k[fi] * _W_FACE[fi][e]
        if any(tot):
            continue
        p = sum(v * v for v in k)
        out[p] = out.get(p, Frac(0)) + 1
    return out


def kernel_entry_frozen_u1(n: int, m: int, M: int) -> SPoly:
    """Frozen-side scheme: perimeter walls held at charge 0 (they
    belong to the neighboring blocks).  Every cube boundary charges
    its two perimeter walls, so the flip lattice dies entirely —
    univalence at slab thickness one — and the kernel is EXACTLY the
    2D rule s^{4 C(n) + 4 C(m)} (d = 1: c' = c^4)."""
    pwalls = [fi for fi in range(NF)
              if fi not in _TOP and fi not in _BOTTOM and fi not in _WALLS]
    full = kernel_entry_u1(n, m, M)  # then re-derive with the freeze
    k0 = _particular(n, m)
    out: SPoly = {}
    rng = []
    for i in range(4):
        fi = next(f for f in _CUBES[i] if f in _TOP)
        b = _B[i][fi]
        lo, hi = -(M + abs(n) + abs(m)) - 2, (M + abs(n) + abs(m)) + 2
        rng.append([c for c in range(lo, hi + 1)
                    if abs(k0[fi] + b * c) <= M])
    for c in itertools.product(*rng):
        k = list(k0)
        for i, ci in enumerate(c):
            if ci:
                for fi in _CUBES[i]:
                    k[fi] += _B[i][fi] * ci
        if any(k[fi] for fi in pwalls):
            continue
        if all(abs(v) <= M for v in k):
            p = sum(v * v for v in k)
            out[p] = out.get(p, Frac(0)) + 1
    del full
    return out


def kernel_entry_2d_gate_u1(n: int, M: int) -> SPoly:
    """Top tiles + top loop only: must equal s^{4 C(n)} = c_n^4
    exactly for M >= |n| (and vanish below truncation)."""
    out: SPoly = {}
    tiles = list(_TOP)
    for kt in itertools.product(range(-M, M + 1), repeat=4):
        tot = [n * lt for lt in _W_TOP_LOOP]
        for val, fi in zip(kt, tiles):
            if val:
                for e in range(NE):
                    tot[e] += val * _W_FACE[fi][e]
        if any(tot[e] for e in _FREE):
            continue
        p = sum(v * v for v in kt)
        out[p] = out.get(p, Frac(0)) + 1
    return out


def eval_spoly(p: SPoly, s: Fraction) -> Fraction:
    return sum(c * s ** k for k, c in p.items())


# ---------------------------------------------------------------------------
# Measurements — the DP.2 protocol verbatim, with U(1) group data.
# ---------------------------------------------------------------------------


def build_kernel(N: int, M: int) -> Dict[Tuple[int, int], SPoly]:
    T = {}
    for n in range(-N, N + 1):
        for m in range(-N, N + 1):
            T[(n, m)] = kernel_entry_u1(n, m, M)
    return T


def flow_fit_u1(v: Dict[int, Fraction]):
    """Mirror of slab_blocking_kernel.flow_fit with U(1) group data:
    fit log(v_n / d_n) = a + log(s') C(n), d_n = 1, C(n) = n^2;
    return (s', corridor log-width)."""
    xs = [casimir_u1(n) for n in v]
    ys = [math.log(float(val / dim_u1(n))) for n, val in v.items()]
    k = len(xs)
    xb = sum(xs) / k
    yb = sum(ys) / k
    slope = sum((x - xb) * (y - yb) for x, y in zip(xs, ys)) / sum(
        (x - xb) ** 2 for x in xs
    )
    resid = [y - (yb + slope * (x - xb)) for x, y in zip(xs, ys)]
    return math.exp(slope), max(resid) - min(resid)


def measure(T: Dict[Tuple[int, int], SPoly], N: int, sv: Fraction):
    """Positive sector, whole-cone Birkhoff diameter (mirrored
    hilbert_diameter), flowed envelope v = T e_s with e_m = s^{C(m)},
    flow fit, and the exact per-charge 2D-rule ratios
    rho_n = (v_n / v_0) / (s^4)^{C(n)}  (rho == 1 iff exact 2D
    tracking)."""
    cand = list(range(-N, N + 1))
    idx = [n for n in cand
           if all(eval_spoly(T[(n, m)], sv) > 0 for m in cand)]
    out = {"s": sv, "sector": idx}
    if len(idx) < 2:
        return out
    cols = [[eval_spoly(T[(n, m)], sv) for n in idx] for m in idx]
    out["birkhoff_diameter"] = hilbert_diameter(cols)
    v = {}
    for n in idx:
        v[n] = sum(eval_spoly(T[(n, m)], sv)
                   * Frac(dim_u1(m)) * sv ** casimir_u1(m)
                   for m in idx)
    out["v"] = v
    sp, width = flow_fit_u1(v)
    out["s_prime"] = sp
    out["corridor"] = width
    out["ratios"] = {
        n: (v[n] / v[0]) / (sv ** 4) ** casimir_u1(n)
        for n in idx if n >= 0 and 0 in v
    }
    return out


def truncation_min_degree_gap(N: int, M: int) -> int:
    """Smallest s-degree present in T_{M+1} - T_M over all entries;
    must be >= (M+1)^2 (exact-stability certificate)."""
    gap = None
    for n in range(-N, N + 1):
        for m in range(-N, N + 1):
            a = kernel_entry_u1(n, m, M)
            b = kernel_entry_u1(n, m, M + 1)
            d = {p: b.get(p, Frac(0)) - a.get(p, Frac(0))
                 for p in set(a) | set(b)}
            d = {p: c for p, c in d.items() if c}
            if d:
                lo = min(d)
                gap = lo if gap is None else min(gap, lo)
    return gap if gap is not None else 10 ** 9


def main() -> None:
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    M = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    print(f"DP.6-U1 slab blocking, coarse charges |n| <= {N}, "
          f"activity truncation |k| <= {M}")

    print("=" * 72)
    print("GATE 0 — lattice certificate: rank 16, saturated flip basis")
    ok0 = certify_kernel_basis()
    print(f"  constraint rank / Smith invariants: "
          f"{'PASSED' if ok0 else 'FAILED'}")

    print("=" * 72)
    print("GATE 1 — 2D open-disk gate: top tiles + loop = s^{4 n^2}")
    ok1 = True
    for n in range(0, N + 1):
        e = kernel_entry_2d_gate_u1(n, max(M, N))
        want = {4 * casimir_u1(n): Frac(1)}
        good = e == want
        ok1 &= good
        print(f"  c'_{n} = {e}  ({'OK' if good else 'FAIL'})")
    print(f"  gate 1: {'PASSED' if ok1 else 'FAILED'}")

    print("=" * 72)
    print("GATE 2 — frozen-side scheme: univalence kills every flip")
    ok2 = True
    for n in range(0, N + 1):
        for m in range(n, N + 1):
            e = kernel_entry_frozen_u1(n, m, M)
            want = {4 * casimir_u1(n) + 4 * casimir_u1(m): Frac(1)}
            good = e == want
            ok2 &= good
            print(f"  frozen T[{n},{m}] = {e}  "
                  f"({'= s^(4Cn+4Cm), OK' if good else 'FAIL'})")
    print(f"  gate 2 (exact 2D rule, d=1): "
          f"{'PASSED' if ok2 else 'FAILED'}")

    print("=" * 72)
    print("GATE 3 — independent tile-sweep cross-check (M = 2)")
    ok3 = True
    for n in range(-2, 3):
        for m in range(-2, 3):
            ok3 &= kernel_entry_u1(n, m, 2) == kernel_entry_u1_tiles(n, m, 2)
    print(f"  c-lattice vs tile sweep + full 33-edge conservation: "
          f"{'PASSED' if ok3 else 'FAILED'}")

    print("=" * 72)
    print(f"Kernel entries T_U1[n,m], |n|,|m| <= {N}, truncation {M}")
    T = build_kernel(N, M)
    for n in range(0, N + 1):
        for m in range(-N, N + 1):
            e = T[(n, m)]
            print(f"  T[{n},{m}]: {len(e)} terms, "
                  f"low {min(e) if e else '-'} high {max(e) if e else '-'}; "
                  f"all coefficients positive integer counts")

    print("=" * 72)
    print("Truncation stability: min degree of T_{M+1} - T_M vs (M+1)^2")
    for Mp in range(1, M):
        g = truncation_min_degree_gap(N, Mp)
        print(f"  M {Mp} -> {Mp+1}: min new degree {g} "
              f">= {(Mp+1)**2}: {'OK' if g >= (Mp+1)**2 else 'FAIL'}")

    print("=" * 72)
    print("Measurements (2D baseline: s' = s^4, corridor width 0)")
    for sv in (Frac(1, 4), Frac(1, 2), Frac(3, 4)):
        r = measure(T, N, sv)
        if "s_prime" not in r:
            print(f"  s={sv}: sector {r['sector']} too small; skipped")
            continue
        print(f"  s={sv}: sector {r['sector']}")
        print(f"    whole-cone Birkhoff Delta = {r['birkhoff_diameter']:.4f}")
        print(f"    fitted s' = {r['s_prime']:.6f}  "
              f"(s^4 = {float(sv)**4:.6f})  "
              f"corridor log-width = {r['corridor']:.6f}")
        for n, rho in sorted(r["ratios"].items()):
            print(f"    rho_{n} = (v_{n}/v_0)/(s^4)^(n^2) = {float(rho):.8f}"
                  f"  (exactly 1: {rho == 1})")


if __name__ == "__main__":
    main()
