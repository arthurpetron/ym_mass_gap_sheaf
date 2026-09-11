"""Tests for computations/wigner_6j.py (exact-rational Wigner 6j / Racah).

Every check is exact-rational: known 6j spot values, the smallest-tetrahedron
pin and its Lean ``oneQuarter = 1/4`` Racah kernel, the 24 tetrahedral
symmetries, Delta^2 permutation invariance, the triangle guard, and the exact
Biedenharn-Elliott pentagon / orthogonality sweeps (max residual == 0).
"""

from fractions import Fraction as F
from itertools import permutations

from computations.wigner_6j import (
    QuadRadical,
    SixJValue,
    biedenharn_elliott_residual,
    delta_squared,
    from_doubled,
    orthogonality_residual,
    orthogonality_sweep,
    pentagon_sweep,
    racah_kernel,
    sixj_squared,
    sixj_symbol,
    smallest_tetra_kernel,
    smallest_tetra_pin,
    triangle_ok,
)


def test_smallest_tetra_pin():
    """{1/2 1/2 1; 1/2 1/2 1} = 1/6, square = 1/36, sign = +1."""
    pin = smallest_tetra_pin()
    assert pin.square == F(1, 36)
    assert pin.sign == 1
    assert pin.value_or_none() == F(1, 6)


def test_kernel_matches_lean_oneQuarter():
    """Racah kernel P = dim(e)dim(f){6j}^2 = 3*3*(1/6)^2 = 1/4 (Lean oneQuarter);
    1/4 not in {0,1}, the refutation of every 0/1 permutation surrogate."""
    P = smallest_tetra_kernel()
    assert P == F(1, 4)
    assert P == racah_kernel(F(1, 2), F(1, 2), F(1, 2), F(1, 2), F(1), F(1))
    assert P != 0 and P != 1


def test_known_spot_values():
    """{1/2 1/2 1; 1/2 1/2 1}^2 = 1/36 and {1 1 1; 1 1 1}^2 = 1/36."""
    v1 = sixj_symbol(F(1, 2), F(1, 2), F(1, 2), F(1, 2), F(1), F(1))
    v2 = sixj_symbol(F(1), F(1), F(1), F(1), F(1), F(1))
    assert v1.square == F(1, 36)
    assert v2.square == F(1, 36)
    assert v1.value_or_none() == F(1, 6)
    assert v2.value_or_none() == F(1, 6)


def test_pentagon_sweep_zero():
    """Biedenharn-Elliott pentagon: max exact residual == 0 over the sweep."""
    worst, _ = pentagon_sweep(F(2))
    assert worst == F(0)


def test_orthogonality_sweep_zero():
    """6j orthogonality: max exact residual == 0 over the sweep."""
    worst, _ = orthogonality_sweep(F(2))
    assert worst == F(0)


def test_delta_symmetry():
    """Delta^2(a,b,c) is invariant under all permutations of (a,b,c)."""
    for a, b, c in [(F(1, 2), F(1, 2), F(1)), (F(1), F(1), F(1)),
                    (F(1, 2), F(1), F(3, 2)), (F(2), F(1), F(1))]:
        base = delta_squared(a, b, c)
        for perm in permutations((a, b, c)):
            assert delta_squared(*perm) == base


def test_triangle_guard_returns_zero():
    """A broken triangle zeroes Delta^2 and the 6j (square 0, sign 0)."""
    assert not triangle_ok(F(1, 2), F(1, 2), F(1, 2))  # half-integer sum
    assert delta_squared(F(1, 2), F(1, 2), F(1, 2)) == F(0)
    assert not triangle_ok(F(1), F(1), F(3))  # |a-b|<=c<=a+b fails
    bad = sixj_squared(F(1, 2), F(1, 2), F(1, 2), F(1, 2), F(1, 2), F(1, 2))
    assert bad.square == F(0)
    assert bad.sign == 0
    assert bad.value_or_none() == F(0)


def test_sixj_row_column_permutation_symmetry():
    """The 24 tetrahedral symmetries of {6j}^2.

    The standard 6j ``{j1 j2 j3; j4 j5 j6}`` is invariant under the 24
    tetrahedral symmetries: any permutation of the three columns, and swapping
    the upper/lower entries of any two columns.  We check the squared value
    (invariant, sign not needed) across several spots including irrational-6j
    cases."""
    def cols_and_flips():
        base_cols = (0, 1, 2)
        for cperm in permutations(base_cols):
            # flip masks: which two columns swap upper<->lower (even # of flips
            # among {none, any two}); tetrahedral group = column perms x flips.
            for mask in ((), (0, 1), (0, 2), (1, 2)):
                yield cperm, mask

    def apply(j, cperm, mask):
        top = [j[0], j[1], j[2]]
        bot = [j[3], j[4], j[5]]
        ntop = [top[cperm[0]], top[cperm[1]], top[cperm[2]]]
        nbot = [bot[cperm[0]], bot[cperm[1]], bot[cperm[2]]]
        for k in mask:
            ntop[k], nbot[k] = nbot[k], ntop[k]
        return ntop + nbot

    spots = [
        (F(1, 2), F(1, 2), F(1), F(1, 2), F(1, 2), F(1)),
        (F(1), F(1), F(1), F(1), F(1), F(1)),
        (F(1, 2), F(1), F(3, 2), F(1), F(1, 2), F(1)),  # irrational 6j
        (F(1), F(1), F(2), F(1), F(1), F(2)),
    ]
    distinct: set = set()
    for j in spots:
        base = sixj_squared(*j).square
        for cperm, mask in cols_and_flips():
            jt = apply(j, cperm, mask)
            distinct.add(tuple(jt))
            assert sixj_squared(*jt).square == base
    # non-vacuity: many genuinely distinct symbols were checked
    assert len(distinct) >= 16


def test_from_doubled_adapter():
    """Doubled-int labels s = 2j map back to spins (mk6 convention)."""
    assert from_doubled((1, 1, 1, 1, 2, 2)) == (
        F(1, 2), F(1, 2), F(1, 2), F(1, 2), F(1), F(1),
    )


def test_quadradical_exact_carrier():
    """QuadRadical multiplies/adds exactly and squares to a rational; an
    irrational single 6j has value_or_none() None but exact square."""
    # sqrt(2)*sqrt(2) == 2 (rational)
    r2 = QuadRadical.from_coeff_radicand(F(1), F(2))
    assert r2.value_or_none() is None
    prod = r2 * r2
    assert prod.to_fraction() == F(2)
    # an in-range irrational 6j: {0 0 0; 1/2 1/2 1/2}^2 = 1/2 (not a square)
    irr = sixj_squared(F(0), F(0), F(0), F(1, 2), F(1, 2), F(1, 2))
    assert isinstance(irr, SixJValue)
    assert irr.square == F(1, 2)
    assert irr.value_or_none() is None  # generic 6j is irrational


def test_biedenharn_elliott_spot_zero():
    """A directly-invoked non-vacuous pentagon instance has residual 0."""
    assert biedenharn_elliott_residual(*([F(1, 2)] * 9)) == F(0)
    assert biedenharn_elliott_residual(
        F(1), F(1), F(1), F(1), F(1), F(1), F(1), F(1), F(1)
    ) == F(0)


def test_orthogonality_diagonal_normalization():
    """Diagonal orthogonality sum_x (2x+1){a b x; c d p}^2 = 1/(2p+1) exactly."""
    a, b, c, d, p = F(1, 2), F(1, 2), F(1, 2), F(1, 2), F(1)
    assert orthogonality_residual(a, b, c, d, p, p) == F(0)
