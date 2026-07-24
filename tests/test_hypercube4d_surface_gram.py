"""Regression gates for the exact 128-surface four-cube Gram matrix."""

from collections import Counter
from fractions import Fraction

from computations.hypercube4d_surface_gram import (
    build_surface_gram_survey,
    centered_covariance_matrix,
    diagonal_dominance_residuals,
    modular_rank_and_determinant,
    surface_orbit_block_counts,
)


def test_surface_gram_orbit_and_entry_census() -> None:
    survey = build_surface_gram_survey()

    assert len(survey.surface_masks) == 128
    assert [len(orbit) for orbit in survey.surface_orbits] == [
        1,
        8,
        24,
        32,
        8,
        4,
        24,
        24,
        3,
    ]
    assert Counter(record.kind for record in survey.pair_orbits) == {
        "intersecting": 100,
        "disjoint": 9,
        "diagonal": 9,
    }
    assert len(survey.pair_orbits) == 118
    assert sum(record.size for record in survey.pair_orbits) == 8256
    assert len(survey.distinct_entries) == 80
    assert all(value > 0 for value in survey.distinct_entries)
    assert (min(survey.distinct_entries), max(survey.distinct_entries)) == (
        Fraction(1, 65536),
        Fraction(6724, 6561),
    )


def test_diagonal_includes_the_complete_clifford_torus_value() -> None:
    survey = build_surface_gram_survey()
    diagonal = Counter(survey.matrix[index][index] for index in range(len(survey.surface_masks)))
    assert diagonal == {
        Fraction(1): 1,
        Fraction(82, 81): 8,
        Fraction(6562, 6561): 24,
        Fraction(59050, 59049): 40,
        Fraction(6724, 6561): 4,
        Fraction(531442, 531441): 48,
        Fraction(43046722, 43046721): 3,
    }

    clifford_masks = [mask for mask in survey.surface_masks if mask.bit_count() == 16]
    assert len(clifford_masks) == 3
    indices = [survey.surface_masks.index(mask) for mask in clifford_masks]
    assert all(survey.matrix[index][index] == Fraction(1) + Fraction(3) ** -16 for index in indices)
    assert {
        survey.matrix[left][right]
        for position, left in enumerate(indices)
        for right in indices[position + 1 :]
    } == {Fraction(5115985, 11019960576)}


def test_surface_gram_has_exact_nonnegative_coordinate_factorization() -> None:
    survey = build_surface_gram_survey()
    residuals = diagonal_dominance_residuals(survey.matrix)

    # Strict diagonal dominance makes the pair-coordinate factorization in
    # ``diagonal_dominance_residuals`` positive definite and full rank.
    assert all(residual > 0 for residual in residuals)
    assert {residuals[survey.surface_masks.index(orbit[0])] for orbit in survey.surface_orbits} == {
        Fraction(22269, 65536),
        Fraction(136967, 442368),
        Fraction(30091703, 107495424),
        Fraction(65821039, 241864704),
        Fraction(66146263, 241864704),
        Fraction(7419493, 26873856),
        Fraction(2229620875, 8707129344),
        Fraction(565528477, 2176782336),
        Fraction(699638147519, 2821109907456),
    }

    # An independent finite-field certificate pins the exact determinant.
    assert modular_rank_and_determinant(survey.matrix, 1_000_000_007) == (
        128,
        897767826,
    )


def test_centered_surface_observables_form_an_acute_basis() -> None:
    survey = build_surface_gram_survey()
    covariance = centered_covariance_matrix(survey)

    signs = Counter(
        0 if value == 0 else 1 if value > 0 else -1
        for row, values in enumerate(covariance)
        for value in values[row:]
    )
    assert signs == {1: 8124, 0: 132}

    # The constant row accounts for 128 zeros.  The remaining four are
    # factorizing pairs of disjoint six-face cube boundaries.
    assert (
        sum(covariance[row][column] == 0 for row in range(1, 128) for column in range(row, 128))
        == 4
    )
    nonconstant = tuple(
        tuple(covariance[row][column] for column in range(1, 128)) for row in range(1, 128)
    )
    assert modular_rank_and_determinant(nonconstant, 1_000_000_007) == (
        127,
        897767826,
    )


def test_surface_orbit_block_structure() -> None:
    survey = build_surface_gram_survey()
    assert surface_orbit_block_counts(survey) == (
        (1, 1, 1, 1, 1, 1, 1, 1, 1),
        (1, 3, 3, 3, 1, 2, 4, 2, 1),
        (1, 3, 6, 5, 2, 2, 6, 5, 2),
        (1, 3, 5, 7, 2, 2, 5, 4, 1),
        (1, 1, 2, 2, 3, 1, 1, 2, 1),
        (1, 2, 2, 2, 1, 2, 3, 2, 1),
        (1, 4, 6, 5, 1, 3, 8, 5, 2),
        (1, 2, 5, 4, 2, 2, 5, 6, 2),
        (1, 1, 2, 1, 1, 1, 2, 2, 2),
    )
