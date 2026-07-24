"""Regression pins for the physical pair-family heat census."""

from fractions import Fraction

from computations.fusion_pair_heat_census import (
    intersecting_pair_heat_census,
    pair_heat_census_certificate,
)


def test_all_intersecting_pair_orbits_are_heat_positive() -> None:
    records = intersecting_pair_heat_census()
    assert len(records) == 100
    assert sum(record.orbit_size for record in records) == 7997
    assert all(record.coefficientwise_positive for record in records)
    assert sum(record.negative_channels > 0 for record in records) == 6


def test_signed_witness_family_has_palindromic_heat_activity() -> None:
    records = intersecting_pair_heat_census()
    witness = next(
        record
        for record in records
        if set(record.representative) == {0x4AB33, 0x6BC6AD}
    )
    assert witness.negative_channels == 4
    assert witness.positive_channels == 12
    assert witness.heat_activity == {
        48: Fraction(1),
        56: Fraction(12),
        64: Fraction(6),
        72: Fraction(12),
        80: Fraction(1),
    }


def test_pair_heat_census_certificate() -> None:
    certificate = pair_heat_census_certificate()
    assert certificate.validates()
    assert certificate.distinct_heat_polynomials == 77
    assert certificate.minimum_positive_coefficient == Fraction(1, 6561)
