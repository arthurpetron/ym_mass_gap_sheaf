"""Regression pins for the corrected-slab local projective census."""

from fractions import Fraction

from computations.local_face_projective_census import (
    local_face_multiplicity_matrix,
    local_face_projective_census,
    physical_local_face_matrix,
    reflected_gram,
)
from computations.rational_projective_diameter import audit_support_components


def test_cutoff_one_literal_fusion_matrix() -> None:
    assert local_face_multiplicity_matrix(1) == (
        (1, 0, 0, 0, 0),
        (0, 1, 0, 0, 0),
        (0, 1, 0, 0, 0),
        (1, 0, 1, 0, 0),
        (0, 1, 0, 0, 0),
        (1, 0, 1, 0, 0),
        (1, 0, 1, 0, 0),
        (0, 2, 0, 1, 0),
        (0, 1, 0, 0, 0),
        (1, 0, 1, 0, 0),
        (1, 0, 1, 0, 0),
        (0, 2, 0, 1, 0),
        (1, 0, 1, 0, 0),
        (0, 2, 0, 1, 0),
        (0, 2, 0, 1, 0),
        (2, 0, 3, 0, 1),
    )


def test_one_step_has_two_parity_components_with_zero_holes() -> None:
    audit = local_face_projective_census(1).one_step
    assert not audit.is_fully_unbranched()
    assert not audit.certificates
    assert tuple(component.columns for component in audit.obstructed_components) == (
        (0, 2, 4),
        (1, 3),
    )


def test_heat_activity_is_only_a_projective_column_gauge() -> None:
    raw = local_face_multiplicity_matrix(1)
    physical = physical_local_face_matrix(1, Fraction(2, 3))
    raw_gram_audit = audit_support_components(reflected_gram(raw))
    physical_gram_audit = audit_support_components(reflected_gram(physical))
    assert tuple(
        certificate.max_cross_ratio
        for certificate in raw_gram_audit.certificates
    ) == tuple(
        certificate.max_cross_ratio
        for certificate in physical_gram_audit.certificates
    )


def test_reflected_gram_is_positive_inside_each_parity_sector() -> None:
    census = local_face_projective_census(1)
    assert census.reflected_gram.is_fully_unbranched()
    assert tuple(
        certificate.columns
        for certificate in census.reflected_gram.certificates
    ) == ((0, 2, 4), (1, 3))
    assert tuple(
        certificate.max_cross_ratio
        for certificate in census.reflected_gram.certificates
    ) == (Fraction(11, 4), Fraction(5, 4))
    assert census.gram_uniform_spread == Fraction(11, 4)
    assert census.gram_uniform_q == Fraction(7, 15)


def test_fixed_cutoff_rates_expose_the_uniformity_gate() -> None:
    expected = {
        1: Fraction(7, 15),
        2: Fraction(19, 25),
        3: Fraction(1333, 1495),
        4: Fraction(2603, 2747),
    }
    observed = {
        cutoff: local_face_projective_census(cutoff).gram_uniform_q
        for cutoff in expected
    }
    assert observed == expected
    assert list(observed.values()) == sorted(observed.values())
