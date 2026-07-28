"""4D hypercube dual-amplitude survey: surfaces, symmetry orbits, signs.

The 4-cube boundary (16 vertices, 32 edges, 24 plaquettes; every edge
trivalent) is the minimal closed genuinely 4D complex.  This module
packages the machinery used for the exact 4D positivity survey:

- ``kernel_basis`` / ``surfaces``: the parity-admissible binary spin
  assignments are the F2 kernel of the face-edge incidence — the closed
  surfaces mod 2 of the boundary 3-sphere.  Dimension 7 (the eight
  3-cell boundaries modulo the fundamental relation): 128 surfaces.
- 2D-YM factorization: a binary surface with uniform spin n evaluates
  to  d_n^{chi(Sigma) - F(Sigma)}  (spheres d^{2-F}; the three
  coordinate Clifford tori, F = 16, chi = 0, give d^{-16}).  Positive
  by 2D reduction — proved by the bivalence of surface edges.
- ``symmetry_maps``: the 384 hypercube symmetries as face permutations.
  Amplitudes are invariant; contraction *cost* under the fixed gauge
  tree is not, so hard assignments are evaluated in their cheapest
  frame (``evaluate_in_best_frame``).
- ``pair_orbits``: the 8128 intersecting-surface pairs quotient to 109
  orbits.  Pairs are the genuine 4D interference test: where two
  surfaces cross without sharing a face the crossing edges are
  4-valent with four spin-1 faces, Inv(1/2^{x4}) is 2-dimensional, and
  the amplitude carries a closed chain of nontrivial recouplings.

Survey verdict (see notes/dual-positivity-survival.md for the ledger):
every reached amplitude is positive; orbit members evaluated through
different contraction paths agree exactly (a free consistency
certification of the engine).

Run:  python -m computations.hypercube4d_survey   (fast summary only)
"""

from __future__ import annotations

import itertools
from fractions import Fraction
from typing import Dict, List, Optional, Sequence, Tuple

from computations.exact_haar_network import (
    ContractionTooLarge,
    P_ONE,
    SPoly,
    brick_complex_nd,
    chi,
    contract,
    scalar,
)


def hypercube():
    """The 4-cube boundary complex: (cx, faces, meta)."""
    return brick_complex_nd((1, 1, 1, 1))


def kernel_basis(cx, faces) -> List[int]:
    """Basis (as face bitmasks) of the F2 closed-surface space."""
    NF, NE = len(faces), len(cx.edges)
    rows = []
    for ei in range(NE):
        r = 0
        for fi, f in enumerate(faces):
            if any(e == ei for e, _o in f):
                r |= 1 << fi
        rows.append(r)
    pivots: Dict[int, int] = {}
    for r in rows:
        for pc, pr in pivots.items():
            if (r >> pc) & 1:
                r ^= pr
        if r:
            pivots[r.bit_length() - 1] = r
    basis = []
    for fc in [c for c in range(NF) if c not in pivots]:
        v = 1 << fc
        for pc in sorted(pivots, reverse=True):
            if bin(pivots[pc] & v).count("1") % 2:
                v ^= 1 << pc
        basis.append(v)
    return basis


def surfaces(basis: Sequence[int]) -> List[int]:
    """All 2^dim surfaces, in the deterministic sweep order."""
    out = []
    for bits in range(2 ** len(basis)):
        v = 0
        for i in range(len(basis)):
            if (bits >> i) & 1:
                v ^= basis[i]
        out.append(v)
    return out


def symmetry_maps(meta) -> List[List[int]]:
    """The 384 hypercube symmetries as permutations of face indices."""
    fkey = {(p, d1, d2): i for i, (p, d1, d2) in enumerate(meta)}

    def transform_face(i: int, perm, flips) -> int:
        p, d1, d2 = meta[i]
        corners = []
        for (a, b) in ((0, 0), (1, 0), (1, 1), (0, 1)):
            v = list(p)
            v[d1] += a
            v[d2] += b
            w = [0, 0, 0, 0]
            for k in range(4):
                src = v[perm[k]]
                w[k] = (1 - src) if flips[k] else src
            corners.append(tuple(w))
        base = tuple(min(c[k] for c in corners) for k in range(4))
        dirs = sorted(k for k in range(4) if max(c[k] for c in corners) > base[k])
        return fkey[(base, dirs[0], dirs[1])]

    maps = []
    for perm in itertools.permutations(range(4)):
        for fbits in range(16):
            flips = [(fbits >> k) & 1 for k in range(4)]
            maps.append([transform_face(i, perm, flips) for i in range(len(meta))])
    return maps


def act(gmap: Sequence[int], v: int) -> int:
    """Push a face bitmask through a symmetry."""
    out = 0
    x = v
    while x:
        low = x & (-x)
        i = low.bit_length() - 1
        out |= 1 << gmap[i]
        x ^= low
    return out


def pair_orbits(surf: Sequence[int], maps) -> Dict[Tuple[int, int], List[Tuple[int, int]]]:
    """Quotient unordered surface pairs by the symmetry group."""
    orbits: Dict[Tuple[int, int], List[Tuple[int, int]]] = {}
    for ia, ib in itertools.combinations(range(len(surf)), 2):
        va, vb = surf[ia], surf[ib]
        best: Optional[Tuple[int, int]] = None
        for g in maps:
            a2, b2 = act(g, va), act(g, vb)
            key = (a2, b2) if a2 <= b2 else (b2, a2)
            if best is None or key < best:
                best = key
        assert best is not None
        orbits.setdefault(best, []).append((ia, ib))
    return orbits


def evaluate_assignment(cx, faces, spins, budget: int = 200_000_000) -> SPoly:
    factors = [chi(s, cx.holonomy_of(f)) for s, f in zip(spins, faces) if s > 0]
    if not factors:
        factors = [dict(P_ONE)]
    return scalar(contract(factors, cx.free, max_pairprod=budget))


def evaluate_in_best_frame(
    cx, faces, maps, spins, budget: int = 200_000_000
) -> Tuple[Optional[SPoly], Optional[int]]:
    """Try every symmetry frame; return (value, frame index) or (None, None).

    The amplitude is frame-independent; only contraction cost varies.
    A (None, None) return is a *resource* verdict (report UNREACHED).
    """
    for gi, gmap in enumerate(maps):
        moved = [0] * len(faces)
        for i, s in enumerate(spins):
            moved[gmap[i]] = s
        try:
            return evaluate_assignment(cx, faces, moved, budget), gi
        except ContractionTooLarge:
            continue
    return None, None


def main() -> None:
    cx, faces, meta = hypercube()
    basis = kernel_basis(cx, faces)
    surf = surfaces(basis)
    print(f"4-cube boundary: 24 faces, 32 trivalent edges, "
          f"kernel dim {len(basis)}, {len(surf)} binary surfaces")
    maps = symmetry_maps(meta)
    print(f"symmetry group: {len(maps)} elements")
    # small demonstration: a sphere, a torus, and one crossing pair
    from collections import Counter

    sizes = Counter(bin(v).count("1") for v in surf)
    print(f"surface support census: {dict(sorted(sizes.items()))}")
    sphere = next(v for v in surf if bin(v).count("1") == 6)
    torus = next(v for v in surf if bin(v).count("1") == 16)
    for name, v, expect in (
        ("sphere F=6", sphere, Fraction(1, 16)),
        ("Clifford torus F=16", torus, Fraction(1, 65536)),
    ):
        z = evaluate_assignment(cx, faces, [(v >> i) & 1 for i in range(len(faces))])
        print(f"  {name}: Z = {z.get(0)}  (2D-YM predicts {expect})")
    print("full pair-orbit survey: see notes/dual-positivity-survival.md")


if __name__ == "__main__":
    main()
