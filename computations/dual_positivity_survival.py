"""Positivity survival of SU(2) dual (character-representation) amplitudes.

The question this module decides, exactly: *where* does positivity of the
dual representation first fail on minimal 3D complexes, and does a local
heat-kernel resummation ("positive channel") restore it?

Background.  Pointwise positivity of blocked weights is trivial (they are
integrals of positive integrands).  What is NOT trivial — and is the known
obstruction to iterating the dual representation (the nonabelian dual
sign problem) — is positivity of the *dual coefficients*: the exact Haar
network values attached to spin assignments.  Sign changes in SU(2)
recoupling can only enter through genuinely 3D incidence (links shared by
more than two plaquettes); every tree-reducible network is manifestly
positive (convolution, fusion, and Clebsch-Gordan moves are each
positivity-preserving).  This module therefore walks up the incidence
ladder:

  P0  single cube            (all links bivalent on the closed surface —
                              2D-like; control: must be all-equal-spin
                              delta with positive values)
  P1  double cube (1x1x2)    (four trivalent links around the shared
                              face; first non-tree object)
  P2  wheel / star of a link (one 4-valent link: 4 'page' plaquettes
                              around a spine + 4 rim loops; the minimal
                              interference geometry, where 6j-type
                              recoupling enters)
  P3  positive-channel door test: wherever P2 shows negative amplitudes,
      sum the page spins against exact heat-kernel activities
      d_n s^{n(n+2)} and decide the sign of the summed channel exactly
      on s in (0,1) (Sturm-certified).  This is the exact-arithmetic
      version of the resummation that dual-simulation folklore
      (Cherrington et al., 3D SU(2)) reports as positive numerically —
      and it is the executable mirror of the 'positive channel
      factorization' spine in lean/YMGap.

Truncation honesty: in P3 the page-spin sum is *exactly* finite: the
X_i-link fusion rule kills every page spin j_i > m_{i-1} + m_i, so
truncating at nmax = 2*max(m) is exact, not approximate.  P0-P2 evaluate
single assignments; no truncation is involved at all.

All arithmetic is Fraction-exact; the coupling s = e^{-t/4} stays
symbolic.  Sign verdicts on (0,1) are exact (square-free factor + Sturm).

Run:  python -m computations.dual_positivity_survival
"""

from __future__ import annotations

import itertools
from fractions import Fraction
from typing import Dict, List, Sequence, Tuple

from computations.exact_haar_network import (
    GaugeFixedComplex,
    SPoly,
    brick_complex,
    casimir4,
    chi,
    contract,
    dim,
    holonomy,
    p_mul,
    p_scale_s,
    q_conj,
    q_link,
    q_mul,
    scalar,
    sign_on_unit_interval,
    sp_str,
)

Frac = Fraction


# ---------------------------------------------------------------------------
# P0 / P1: dual amplitudes of closed brick complexes.
# ---------------------------------------------------------------------------


def brick_dual_amplitude(nx: int, ny: int, nz: int, spins: Sequence[int]) -> SPoly:
    """Exact dual amplitude Z(spin assignment) of a closed brick complex."""
    cx, faces = brick_complex(nx, ny, nz)
    assert len(spins) == len(faces), (len(spins), len(faces))
    factors = [chi(n, cx.holonomy_of(f)) for n, f in zip(spins, faces) if n > 0]
    if not factors:
        factors = [dict()]  # empty product handled by contract via P_ONE
        from computations.exact_haar_network import P_ONE

        factors = [dict(P_ONE)]
    return cx.contract_invariant(factors)


def single_cube_table(nmax: int) -> Dict[Tuple[int, ...], Fraction]:
    """All nonzero dual amplitudes of the 1x1x1 cube, spins <= nmax."""
    cx, faces = brick_complex(1, 1, 1)
    out: Dict[Tuple[int, ...], Fraction] = {}
    for spins in itertools.product(range(nmax + 1), repeat=len(faces)):
        val = brick_dual_amplitude(1, 1, 1, spins)
        if val:
            assert set(val) == {0}
            out[spins] = val[0]
    return out


def double_cube_structured_table(nmax: int, kmax: int):
    """Z(n_A, n_B, k) for the 1x1x2 brick.

    Outer faces of cube A all carry n_A, outer faces of cube B carry n_B,
    the shared interior face carries k.  (The bivalent outer edges force
    exactly this structure; assignments violating it vanish — spot-checked
    separately.)  Returns dict {(nA, nB, k): Fraction}.
    """
    cx, faces = brick_complex(1, 1, 2)
    # classify faces: interior face is the z=1 horizontal face
    interior_idx = None
    cube_a: List[int] = []
    cube_b: List[int] = []
    # Recompute geometry to classify: faces come from brick_complex in
    # deterministic order; identify by vertex coordinates.
    coords: Dict[int, Tuple[int, int, int]] = {}
    vid = {}
    idx = 0
    for x in range(2):
        for y in range(2):
            for z in range(3):
                vid[(x, y, z)] = idx
                coords[idx] = (x, y, z)
                idx += 1
    for fi, f in enumerate(faces):
        # face vertices: tails of its first two oriented edges suffice
        vs = set()
        for ei, _o in f:
            a, b = cx.edges[ei]
            vs.add(coords[a])
            vs.add(coords[b])
        zs = sorted({v[2] for v in vs})
        if zs == [1]:
            interior_idx = fi
        elif max(zs) <= 1:
            cube_a.append(fi)
        else:
            cube_b.append(fi)
    assert interior_idx is not None and len(cube_a) == 5 and len(cube_b) == 5
    out = {}
    for na in range(nmax + 1):
        for nb in range(nmax + 1):
            for k in range(kmax + 1):
                spins = [0] * len(faces)
                for fi in cube_a:
                    spins[fi] = na
                for fi in cube_b:
                    spins[fi] = nb
                spins[interior_idx] = k
                val = brick_dual_amplitude(1, 1, 2, spins)
                if val:
                    assert set(val) == {0}
                    out[(na, nb, k)] = val[0]
    return out


# ---------------------------------------------------------------------------
# P1b: the 2x2x1 slab — first complex with a closed, unanchored
# intertwiner circuit (four interior walls around the central 4-valent
# edge, threading four cubes).  NOT covered by the spin-model
# sum-of-squares argument (plaquette loops are length >= 3 in free
# variables after gauge fixing), so positivity here is a genuine
# computation, not a structural triviality.
# ---------------------------------------------------------------------------


def _slab_geometry():
    cx, faces = brick_complex(2, 2, 1)
    coords = {}
    i = 0
    for x in range(3):
        for y in range(3):
            for z in range(2):
                coords[i] = (x, y, z)
                i += 1

    def face_info(f):
        vs = set()
        for ei, _o in f:
            a, b = cx.edges[ei]
            vs.add(coords[a])
            vs.add(coords[b])
        xs = {v[0] for v in vs}
        ys = {v[1] for v in vs}
        zs = {v[2] for v in vs}
        if len(zs) == 1:
            return ("horiz", min(zs), min(xs), min(ys))
        if len(xs) == 1:
            return ("xwall", min(xs), min(ys))
        return ("ywall", min(ys), min(xs))

    info = [face_info(f) for f in faces]
    interior = [
        i
        for i, (t, *r) in enumerate(info)
        if (t == "xwall" and r[0] == 1) or (t == "ywall" and r[0] == 1)
    ]
    outer = [i for i in range(len(faces)) if i not in interior]
    cyc = []
    for want in [("xwall", 1, 0), ("ywall", 1, 1), ("xwall", 1, 1), ("ywall", 1, 0)]:
        cyc.append(next(i for i in interior if info[i] == want))
    return cx, faces, outer, cyc


def slab_value(n_outer: int, walls: Sequence[int]) -> SPoly:
    """Z(outer shell = n_outer, interior walls = (k1,k2,k3,k4) cyclic)."""
    cx, faces, outer, cyc = _slab_geometry()
    spins = [0] * len(faces)
    for i in outer:
        spins[i] = n_outer
    for i, k in zip(cyc, walls):
        spins[i] = k
    factors = [chi(s, cx.holonomy_of(f)) for s, f in zip(spins, faces) if s > 0]
    if not factors:
        from computations.exact_haar_network import P_ONE

        factors = [dict(P_ONE)]
    return cx.contract_invariant(factors)


def slab_sweep(nmax_outer: int, kmax: int):
    """All nonzero slab amplitudes, outer <= nmax_outer, walls <= kmax."""
    out = {}
    for n in range(nmax_outer + 1):
        for ks in itertools.product(range(kmax + 1), repeat=4):
            val = slab_value(n, ks)
            if val:
                assert set(val) == {0}
                out[(n,) + ks] = val[0]
    return out


# ---------------------------------------------------------------------------
# P2: the wheel (star of a 3D interior link; minimal 4-valent geometry).
#
# Spine e0, pages P_i = e0 X_i (i = 1..4 cyclic), rim loops X_i X_{i+1}^-1.
# Gauge: conjugation invariance removes e0 exactly:
#     W(j; m) = ∫ ΠdX_i  Π chi_{j_i}(X_i)  Π chi_{m_i}(X_i X_{i+1}^-1).
# ---------------------------------------------------------------------------


def wheel_value(j: Sequence[int], m: Sequence[int]) -> SPoly:
    X = [q_link(i) for i in range(4)]
    factors = []
    for i in range(4):
        if j[i] > 0:
            factors.append(chi(j[i], X[i]))
        if m[i] > 0:
            factors.append(chi(m[i], q_mul(X[i], q_conj(X[(i + 1) % 4]))))
    if not factors:
        from computations.exact_haar_network import P_ONE

        factors = [dict(P_ONE)]
    return scalar(contract(factors, [0, 1, 2, 3]))


def wheel_sweep(nmax: int):
    """All nonzero wheel values with page and rim spins <= nmax."""
    out = {}
    for j in itertools.product(range(nmax + 1), repeat=4):
        for m in itertools.product(range(nmax + 1), repeat=4):
            # fusion parity screen at each X_i: j_i + m_{i-1} + m_i even
            if any((j[i] + m[(i - 1) % 4] + m[i]) % 2 for i in range(4)):
                continue
            # triangle screen: j_i <= m_{i-1} + m_i (else exact zero)
            if any(j[i] > m[(i - 1) % 4] + m[i] for i in range(4)):
                continue
            val = wheel_value(j, m)
            if val:
                assert set(val) == {0}
                out[(j, m)] = val[0]
    return out


# ---------------------------------------------------------------------------
# P3: positive-channel door test.
#
# Fix the rim spins m; sum the page spins against exact heat-kernel
# activities (exactly finite by the fusion rule).  The result is an exact
# polynomial in s; its sign on (0,1) is the door/wall verdict for this
# channel at this scale.
# ---------------------------------------------------------------------------


def rim_channel_activity(m: Sequence[int]) -> SPoly:
    nmax = max(m[(i - 1) % 4] + m[i] for i in range(4))
    X = [q_link(i) for i in range(4)]
    factors = []
    from computations.exact_haar_network import heat_activity

    for i in range(4):
        factors.append(heat_activity(X[i], nmax))
    for i in range(4):
        if m[i] > 0:
            factors.append(chi(m[i], q_mul(X[i], q_conj(X[(i + 1) % 4]))))
    return scalar(contract(factors, [0, 1, 2, 3]))


def rim_channel_decomposition(m: Sequence[int]):
    """Per-page-spin contributions to the rim channel (exact ledger)."""
    terms = {}
    nmax = max(m[(i - 1) % 4] + m[i] for i in range(4))
    for j in itertools.product(range(nmax + 1), repeat=4):
        w = wheel_value(j, m)
        if not w:
            continue
        coeff = Frac(1)
        spow = 0
        for ji in j:
            coeff *= dim(ji)
            spow += casimir4(ji)
        terms[j] = {spow: coeff * w[0]}
    return terms


# ---------------------------------------------------------------------------
# Report.
# ---------------------------------------------------------------------------


def main() -> None:
    print("=" * 72)
    print("P0: single cube (control) — spins <= 2")
    tab = single_cube_table(2)
    bad = {k: v for k, v in tab.items() if v < 0}
    nonuniform = {k: v for k, v in tab.items() if len(set(k)) > 1}
    print(f"  nonzero assignments: {len(tab)}; negatives: {len(bad)}; "
          f"non-all-equal nonzero: {len(nonuniform)}")
    for k, v in sorted(tab.items()):
        print(f"    Z{k} = {v}")

    print("=" * 72)
    print("P1: double cube 1x1x2 — Z(n_A, n_B, k), n <= 1, k <= 2")
    print("    (full n <= 2, k <= 4 table takes ~hours; see notes)")
    tab2 = double_cube_structured_table(1, 2)
    neg2 = {k: v for k, v in tab2.items() if v < 0}
    print(f"  nonzero: {len(tab2)}; negatives: {len(neg2)}")
    for k, v in sorted(tab2.items()):
        mark = "  <-- NEGATIVE" if v < 0 else ""
        print(f"    Z{k} = {v}{mark}")

    print("=" * 72)
    print("P1b: 2x2x1 slab — unanchored circuit around the central "
          "4-valent edge; outer <= 2, walls <= 2")
    tabs = slab_sweep(2, 2)
    negs = {k: v for k, v in tabs.items() if v < 0}
    print(f"  nonzero: {len(tabs)}; negatives: {len(negs)}")
    for k, v in sorted(tabs.items()):
        mark = "  <-- NEGATIVE" if v < 0 else ""
        print(f"    Z(outer={k[0]}, walls={k[1:]}) = {v}{mark}")

    print("=" * 72)
    print("P2: wheel (4-valent star) — page/rim spins <= 2")
    w = wheel_sweep(2)
    negw = {k: v for k, v in w.items() if v < 0}
    print(f"  nonzero: {len(w)}; negatives: {len(negw)}")
    for (j, m), v in sorted(negw.items()):
        print(f"    W(j={j}, m={m}) = {v}   <-- NEGATIVE")
    if not negw:
        print("    (no negative wheel values at this cutoff; see the "
              "frozen-hub sum-of-squares theorem in the notes)")

    print("=" * 72)
    print("P3: positive-channel door test — rim channels, exact in s")
    rims = sorted({m for (_j, m) in w.keys()})
    print(f"  {len(rims)} rim channels")
    n_pos = 0
    for m in rims:
        act = rim_channel_activity(m)
        verdict = sign_on_unit_interval(act)
        if verdict == "positive":
            n_pos += 1
            continue
        print(f"  rim m={m}: channel = {sp_str(act)}")
        print(f"      verdict on (0,1): {verdict}   <-- {verdict.upper()}")
    print(f"  positive channels: {n_pos}/{len(rims)}")
    ex = (1, 1, 1, 1)
    print(f"  example, rim m={ex}: {sp_str(rim_channel_activity(ex))}")


if __name__ == "__main__":
    main()
