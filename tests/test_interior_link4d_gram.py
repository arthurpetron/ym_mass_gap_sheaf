"""Regression gates for the six-valent composite-surface Gram cone."""

import os
from collections import Counter
from fractions import Fraction

import pytest

from computations.interior_link4d_gram import (
    COMPOSITE_DIAGONAL_RAW_CENSUS,
    COMPOSITE_OFFDIAGONAL_ORBIT_CENSUS,
    COMPOSITE_OFFDIAGONAL_RAW_CENSUS,
    composite_gram_cone_certificate,
    composite_surface_orbits,
    elementary_generator_rank,
    elementary_generator_shell,
    elementary_generator_shell_orbits,
    elementary_generator_shell_pair_orbit_count,
    recompute_composite_diagonal_census,
    recompute_composite_pair_censuses,
)
from computations.interior_link4d_probe import composite_pair_probe_survey


def test_composite_surface_and_pair_census_sizes() -> None:
    assert [len(orbit) for orbit in composite_surface_orbits()] == [
        24,
        12,
        24,
        6,
    ]
    assert sum(count for _value, count in COMPOSITE_DIAGONAL_RAW_CENSUS) == 66
    assert sum(count for _value, count in COMPOSITE_OFFDIAGONAL_ORBIT_CENSUS) == 65
    assert sum(count for _value, count in COMPOSITE_OFFDIAGONAL_RAW_CENSUS) == 2145


def test_elementary_generator_shell_scope_is_exact() -> None:
    assert elementary_generator_rank() == 12
    expected = {
        0: (1, 1, {0}),
        1: (12, 1, {6}),
        2: (66, 4, {10, 12}),
        3: (220, 9, {12, 14, 16, 18}),
        4: (495, 18, {16, 18, 20, 22}),
        5: (792, 24, {20, 22, 24, 26}),
        6: (924, 30, {24, 26, 28, 30}),
    }
    for weight, (shell_size, orbit_count, support_sizes) in expected.items():
        shell = elementary_generator_shell(weight)
        assert len(shell) == shell_size
        assert len(elementary_generator_shell_orbits(weight)) == orbit_count
        assert {mask.bit_count() for mask in shell} == support_sizes

    assert {
        weight: elementary_generator_shell_pair_orbit_count(weight) for weight in (1, 2, 3)
    } == {
        1: 4,
        2: 65,
        3: 568,
    }


def test_composite_gram_has_a_strict_uniform_cp_certificate() -> None:
    certificate = composite_gram_cone_certificate()
    assert certificate.dimension == 66
    assert certificate.diagonal_floor == Fraction(6562, 6561)
    assert certificate.offdiagonal_ceiling == Fraction(31, 3888)
    assert certificate.residual_floor == Fraction(50587, 104976)
    assert certificate.is_strict


def test_diagonal_and_offdiagonal_extrema_are_recomputed_exactly() -> None:
    assert recompute_composite_diagonal_census() == Counter(dict(COMPOSITE_DIAGONAL_RAW_CENSUS))

    # Canonical off-diagonal orbit two is the unique maximum-amplitude orbit.
    maximum_probe = composite_pair_probe_survey((2,))
    assert len(maximum_probe) == 1
    assert maximum_probe[0].value == Fraction(31, 3888)
    assert maximum_probe[0].orbit_size == 24


@pytest.mark.skipif(
    os.environ.get("VERIFY_SLOW_DUAL_CENSUS") != "1",
    reason="set VERIFY_SLOW_DUAL_CENSUS=1 to recompute all 65 exact Haar orbits",
)
def test_opt_in_full_composite_pair_census() -> None:
    orbit_census, raw_census = recompute_composite_pair_censuses()
    assert orbit_census == Counter(dict(COMPOSITE_OFFDIAGONAL_ORBIT_CENSUS))
    assert raw_census == Counter(dict(COMPOSITE_OFFDIAGONAL_RAW_CENSUS))
