"""Pins for the 4D hypercube dual amplitude probes.

The 4-cube boundary (16 vertices, 32 edges, 24 plaquettes, all edges
trivalent) is the minimal closed genuinely 4D complex.  Its
parity-admissible binary spin assignments are exactly the closed
surfaces mod 2 of the boundary 3-sphere (kernel dimension 7 = eight
3-cell boundaries modulo one relation), and every binary surface
amplitude factorizes through 2D Yang-Mills on the surface:

    Z(surface, uniform spin n) = d_n^{chi(Sigma) - F(Sigma)}.

Spheres give d^{2-F}; the three coordinate Clifford tori (16 faces,
chi = 0) give d^{-16}.  These pins certify the 4D wiring and the
surface classification; the interference (intersecting-pair) results
live in notes/dual-positivity-survival.md.
"""

from collections import Counter
from fractions import Fraction

from computations.exact_haar_network import P_ONE, brick_complex_nd, chi


def _hypercube():
    cx, faces, meta = brick_complex_nd((1, 1, 1, 1))
    return cx, faces, meta


def _evaluate(cx, faces, spins):
    factors = [chi(s, cx.holonomy_of(f)) for s, f in zip(spins, faces) if s > 0]
    if not factors:
        factors = [dict(P_ONE)]
    return cx.contract_invariant(factors)


def _kernel_basis(cx, faces):
    NF, NE = len(faces), len(cx.edges)
    rows = []
    for ei in range(NE):
        r = 0
        for fi, f in enumerate(faces):
            if any(e == ei for e, _o in f):
                r |= 1 << fi
        rows.append(r)
    pivots = {}
    for r in rows:
        for pc, pr in pivots.items():
            if (r >> pc) & 1:
                r ^= pr
        if r:
            pivots[r.bit_length() - 1] = r
    free_cols = [c for c in range(NF) if c not in pivots]
    basis = []
    for fc in free_cols:
        v = 1 << fc
        for pc in sorted(pivots, reverse=True):
            if bin(pivots[pc] & v).count("1") % 2:
                v ^= 1 << pc
        basis.append(v)
    return basis


def test_hypercube_combinatorics():
    cx, faces, _meta = _hypercube()
    assert len(cx.edges) == 32 and len(faces) == 24 and len(cx.free) == 17
    valence = Counter()
    for f in faces:
        for ei, _o in f:
            valence[ei] += 1
    assert dict(Counter(valence.values())) == {3: 32}


def test_kernel_is_seven_dimensional():
    cx, faces, _meta = _hypercube()
    basis = _kernel_basis(cx, faces)
    assert len(basis) == 7  # eight 3-cells modulo the S^3 fundamental relation


def test_embedded_3cell_reproduces_3d_cube():
    cx, faces, meta = _hypercube()
    cell = [
        i
        for i, (p, d1, d2) in enumerate(meta)
        if d1 != 3 and d2 != 3 and p[3] == 0
    ]
    assert len(cell) == 6
    for n, expect in [(1, Fraction(1, 16)), (2, Fraction(1, 81))]:
        spins = [0] * len(faces)
        for i in cell:
            spins[i] = n
        assert _evaluate(cx, faces, spins) == {0: expect}


def test_binary_surfaces_evaluate_by_2d_yang_mills():
    """Z = d^{chi - F}: spheres d^{2-F}, Clifford tori (F=16) d^{-16}."""
    cx, faces, _meta = _hypercube()
    basis = _kernel_basis(cx, faces)
    # support-size census over the full kernel:
    sizes = Counter()
    vecs = []
    for bits in range(2 ** len(basis)):
        v = 0
        for i in range(len(basis)):
            if (bits >> i) & 1:
                v ^= basis[i]
        vecs.append(v)
        sizes[bin(v).count("1")] += 1
    # one representative per support size, pinned:
    expected = {
        0: Fraction(1),           # empty surface
        6: Fraction(1, 16),       # 3-cell sphere: 2^{2-6}
        10: Fraction(1, 256),     # double-cell sphere: 2^{2-10}
        12: Fraction(1, 1024),    # 2^{2-12}
        14: Fraction(1, 4096),    # 2^{2-14}
        16: Fraction(1, 65536),   # Clifford torus: chi=0 -> 2^{-16}
    }
    assert set(sizes) == set(expected)
    assert sizes[16] >= 3  # at least the three coordinate tori
    done = set()
    for v in vecs:
        k = bin(v).count("1")
        if k in done:
            continue
        spins = [(v >> i) & 1 for i in range(len(faces))]
        assert _evaluate(cx, faces, spins) == (
            {0: expected[k]} if expected[k] != 0 else {}
        ), k
        done.add(k)
        if done == set(expected):
            break


# -- survey module pins ------------------------------------------------------


def test_symmetry_maps_are_permutations():
    from computations.hypercube4d_survey import hypercube, symmetry_maps

    cx, faces, meta = hypercube()
    maps = symmetry_maps(meta)
    assert len(maps) == 384
    for g in maps[:20] + maps[-20:]:
        assert sorted(g) == list(range(24))
    assert maps[0] == list(range(24))  # identity first


def test_survey_module_agrees_with_direct_evaluation():
    from fractions import Fraction

    from computations.hypercube4d_survey import (
        evaluate_assignment,
        hypercube,
        kernel_basis,
        surfaces,
    )

    cx, faces, meta = hypercube()
    basis = kernel_basis(cx, faces)
    assert len(basis) == 7
    surf = surfaces(basis)
    assert len(surf) == 128
    sphere = next(v for v in surf if bin(v).count("1") == 6)
    z = evaluate_assignment(cx, faces, [(sphere >> i) & 1 for i in range(24)])
    assert z == {0: Fraction(1, 16)}
