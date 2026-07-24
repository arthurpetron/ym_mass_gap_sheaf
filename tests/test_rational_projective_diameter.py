"""Regression tests for exact projective-diameter certificates."""

from fractions import Fraction

import pytest

from computations.rational_projective_diameter import (
    audit_support_components,
    certify_positive_sector,
    common_uniform_spread,
)


def test_exact_cross_ratio_and_rate() -> None:
    kernel = ((1, 2), (3, 4))
    certificate = certify_positive_sector(kernel, (0, 1), (0, 1))
    assert certificate.max_cross_ratio == Fraction(3, 2)
    assert certificate.spread == Fraction(3, 2)
    assert certificate.q == Fraction(1, 5)
    assert certificate.validates(kernel)


def test_row_column_scaling_preserves_exact_cross_ratios() -> None:
    kernel = ((1, 2), (3, 4))
    scaled = ((35, 110), (42, 88))
    # scaled[x,y] = row[x] * kernel[x,y] * column[y]
    original = certify_positive_sector(kernel, (0, 1), (0, 1))
    rescaled = certify_positive_sector(scaled, (0, 1), (0, 1))
    assert rescaled.max_cross_ratio == original.max_cross_ratio
    assert rescaled.q == original.q


def test_support_components_separate_unbranched_sectors() -> None:
    kernel = (
        (1, 0, 0),
        (2, 0, 0),
        (0, 3, 4),
        (0, 6, 8),
    )
    audit = audit_support_components(kernel)
    assert audit.is_fully_unbranched()
    assert tuple(certificate.rows for certificate in audit.certificates) == (
        (0, 1),
        (2, 3),
    )
    assert all(certificate.q == 0 for certificate in audit.certificates)
    assert common_uniform_spread(audit.certificates) == (Fraction(1), Fraction(0))


def test_zero_hole_is_reported_not_certified() -> None:
    kernel = ((1, 1), (1, 0))
    audit = audit_support_components(kernel)
    assert not audit.is_fully_unbranched()
    assert not audit.certificates
    assert len(audit.obstructed_components) == 1
    with pytest.raises(ValueError, match="fusion-zero hole"):
        certify_positive_sector(kernel, (0, 1), (0, 1))
