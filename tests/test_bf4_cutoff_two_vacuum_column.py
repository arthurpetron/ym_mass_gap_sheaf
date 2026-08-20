"""Regression gates for the exact cutoff-two vacuum-column scout."""

from fractions import Fraction
from itertools import product

from computations.bf4_cutoff_two_vacuum_column import (
    EXPECTED_ACTIVE_LINK_SCOPES,
    EXPECTED_LOWER_FACE_IDS,
    EXPECTED_MULTIPLICITY_TABLES,
    coeff_w,
    compute_cutoff_two_vacuum_column,
    lower_geometry,
)
from computations.exact_haar_network import invariant_multiplicity


def test_geometry_matches_the_production_lower_carrier() -> None:
    lower_faces, link_scopes = lower_geometry()

    assert lower_faces == EXPECTED_LOWER_FACE_IDS
    assert len(lower_faces) == 24
    assert len(link_scopes) == 48
    assert link_scopes == EXPECTED_ACTIVE_LINK_SCOPES
    assert max(map(len, link_scopes)) <= 4


def test_cutoff_two_heat_weights_at_half() -> None:
    assert tuple(coeff_w(Fraction(1, 2), spin) for spin in range(3)) == (
        Fraction(1),
        Fraction(1, 4),
        Fraction(3, 256),
    )


def test_local_multiplicity_tables_match_the_cross_language_literals() -> None:
    actual = tuple(
        tuple(
            invariant_multiplicity(labels)
            for labels in product(range(3), repeat=arity)
        )
        for arity in range(5)
    )

    assert actual == EXPECTED_MULTIPLICITY_TABLES


def test_exact_sparse_elimination_is_positive_and_scalar() -> None:
    trace = compute_cutoff_two_vacuum_column(jobs=1)

    assert trace.validates()
    assert trace.exact_sum > 1
    assert trace.induced_width < len(trace.lower_face_ids)
    assert len(trace.sha256) == 64
