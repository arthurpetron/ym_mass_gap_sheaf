"""Tests for `computations.su3_representations` (Milestone 10.2 seed)."""

from __future__ import annotations

from fractions import Fraction

import pytest

from computations.su3_representations import (
    ADJOINT,
    ANTIFUNDAMENTAL,
    C_2_SU3_ADJOINT,
    C_2_SU3_FUNDAMENTAL,
    FUNDAMENTAL,
    SMALLEST_NONZERO_CASIMIR_SU3,
    Su3Irrep,
    irreps_in_box,
)

# (p, q, dim, C_2) spot values from the standard SU(3) irrep tables
# (Fulton–Harris §13, Georgi Ch. 8).
LITERATURE = [
    (0, 0, 1, Fraction(0)),
    (1, 0, 3, Fraction(4, 3)),     # fundamental
    (0, 1, 3, Fraction(4, 3)),     # anti-fundamental
    (1, 1, 8, Fraction(3)),        # adjoint / octet
    (2, 0, 6, Fraction(10, 3)),    # sextet
    (3, 0, 10, Fraction(6)),       # decuplet
    (2, 1, 15, Fraction(16, 3)),
    (2, 2, 27, Fraction(8)),
    (4, 0, 15, Fraction(28, 3)),
    (3, 3, 64, Fraction(15)),
]


@pytest.mark.parametrize(("p", "q", "dim", "cas"), LITERATURE)
def test_dimension_and_casimir_match_literature(p: int, q: int, dim: int, cas: Fraction) -> None:
    irr = Su3Irrep(p, q)
    assert irr.dimension == dim
    assert irr.casimir == cas
    assert isinstance(irr.casimir, Fraction)  # exact, ℚ′-encodable


def test_dimension_is_always_integer() -> None:
    for p in range(12):
        for q in range(12):
            d = Su3Irrep(p, q).dimension
            assert isinstance(d, int)
            assert d >= 1


def test_conjugate_swaps_labels_preserving_dim_and_casimir() -> None:
    irr = Su3Irrep(3, 1)
    conj = irr.conjugate
    assert (conj.p, conj.q) == (1, 3)
    assert conj.dimension == irr.dimension
    assert conj.casimir == irr.casimir
    assert irr.conjugate.conjugate == irr


def test_spot_constants() -> None:
    assert FUNDAMENTAL == Su3Irrep(1, 0)
    assert ANTIFUNDAMENTAL == Su3Irrep(0, 1)
    assert ADJOINT == Su3Irrep(1, 1)
    assert C_2_SU3_FUNDAMENTAL == Fraction(4, 3)
    assert C_2_SU3_ADJOINT == Fraction(3)
    assert FUNDAMENTAL.casimir == C_2_SU3_FUNDAMENTAL
    assert ADJOINT.casimir == C_2_SU3_ADJOINT


def test_adjoint_casimir_equals_n() -> None:
    # C_2(adjoint) = N = 3, which fixes the one-loop b_0 = (11/3)·3 = 11.
    assert C_2_SU3_ADJOINT == Fraction(3)
    assert (Fraction(11, 3) * C_2_SU3_ADJOINT) == Fraction(11)


def test_smallest_nonzero_casimir_is_fundamental() -> None:
    casimirs = [
        irr.casimir for irr in irreps_in_box(8, 8, include_trivial=False)
    ]
    assert min(casimirs) == Fraction(4, 3)
    assert SMALLEST_NONZERO_CASIMIR_SU3 == Fraction(4, 3)


def test_trivial_irrep() -> None:
    triv = Su3Irrep(0, 0)
    assert triv.is_trivial
    assert triv.dimension == 1
    assert triv.casimir == Fraction(0)
    assert not FUNDAMENTAL.is_trivial


def test_irreps_in_box_counts_and_trivial_exclusion() -> None:
    full = irreps_in_box(3, 3)
    assert len(full) == 16  # 4 × 4
    nontrivial = irreps_in_box(3, 3, include_trivial=False)
    assert len(nontrivial) == 15
    assert Su3Irrep(0, 0) in full
    assert Su3Irrep(0, 0) not in nontrivial


def test_negative_labels_rejected() -> None:
    with pytest.raises(ValueError, match="≥ 0"):
        Su3Irrep(-1, 0)
    with pytest.raises(ValueError, match="≥ 0"):
        irreps_in_box(-1, 2)
