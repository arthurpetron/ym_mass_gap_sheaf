"""Regression tests for the constructive BF4 refresh search instrument."""

from fractions import Fraction

from computations.constructive_refresh_contraction import (
    grouped_refresh_certificates,
    maximal_refresh_certificate,
    normalize_positive_rows,
)
from computations.local_face_projective_census import physical_local_face_matrix


def test_two_state_kernel_has_exact_maximal_refresh_packet() -> None:
    certificate = maximal_refresh_certificate(
        (
            (Fraction(3, 4), Fraction(1, 4)),
            (Fraction(1, 4), Fraction(3, 4)),
        )
    )

    assert certificate.validates()
    assert certificate.common_floor == (Fraction(1, 4), Fraction(1, 4))
    assert certificate.epsilon == Fraction(1, 2)
    assert certificate.reference == (Fraction(1, 2), Fraction(1, 2))
    assert certificate.rate == Fraction(1, 2)
    assert certificate.residual == (
        (Fraction(1), Fraction(0)),
        (Fraction(0), Fraction(1)),
    )
    assert certificate.contraction_holds((1, 0), (0, 1))


def test_grouping_increases_common_mass_and_multiplies_the_sharp_rate() -> None:
    kernel = (
        (Fraction(3, 4), Fraction(1, 4)),
        (Fraction(1, 4), Fraction(3, 4)),
    )
    certificates = grouped_refresh_certificates(kernel, 4)

    assert tuple(certificate.epsilon for certificate in certificates) == (
        Fraction(1, 2),
        Fraction(3, 4),
        Fraction(7, 8),
        Fraction(15, 16),
    )
    assert tuple(certificate.rate for certificate in certificates) == (
        Fraction(1, 2),
        Fraction(1, 4),
        Fraction(1, 8),
        Fraction(1, 16),
    )
    assert all(certificate.validates() for certificate in certificates)


def test_support_holes_fail_closed_without_a_strict_refresh() -> None:
    certificate = maximal_refresh_certificate(((1, 0), (0, 1)))

    assert certificate.validates()
    assert certificate.epsilon == 0
    assert certificate.rate == 1
    assert not certificate.strict_refresh


def test_input_independent_kernel_contracts_at_rate_zero() -> None:
    certificate = maximal_refresh_certificate(
        (
            (Fraction(2, 5), Fraction(3, 5)),
            (Fraction(2, 5), Fraction(3, 5)),
        )
    )

    assert certificate.validates()
    assert certificate.epsilon == 1
    assert certificate.rate == 0
    assert certificate.reference == (Fraction(2, 5), Fraction(3, 5))
    assert certificate.contraction_holds((1, 0), (0, 1))


def test_raw_local_face_fusion_kernel_has_no_common_packet() -> None:
    raw = physical_local_face_matrix(1, Fraction(1, 2))
    certificate = maximal_refresh_certificate(normalize_positive_rows(raw))

    assert certificate.validates()
    assert certificate.common_floor == (0, 0, 0, 0, 0)
    assert certificate.epsilon == 0
    assert certificate.rate == 1
    assert not certificate.strict_refresh
