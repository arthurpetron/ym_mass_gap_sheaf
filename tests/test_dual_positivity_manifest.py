"""Regression gates for the machine-readable unit-rim certificate."""

import json
from fractions import Fraction

from computations.dual_positivity_manifest import (
    SCHEMA,
    build_unit_rim_manifest,
    canonical_manifest_json,
    manifest_sha256,
)
from computations.dual_positivity_survival import wheel_oriented_words


def _fraction(numerator: int, denominator: int) -> Fraction:
    return Fraction(numerator, denominator)


def test_manifest_carries_the_actual_oriented_wheel_words() -> None:
    manifest = build_unit_rim_manifest()
    page_words, rim_words = wheel_oriented_words()
    assert tuple(word.steps for word in manifest.topology.page_words) == page_words
    assert tuple(word.steps for word in manifest.topology.rim_words) == rim_words
    assert manifest.topology.integrated_links == (0, 1, 2, 3)
    assert manifest.rim_spins == (1, 1, 1, 1)
    assert manifest.page_spin_cutoff == 2


def test_manifest_contains_all_twelve_nonzero_page_sectors() -> None:
    manifest = build_unit_rim_manifest()
    expected_pages = (
        (0, 0, 0, 0),
        (0, 0, 2, 2),
        (0, 2, 0, 2),
        (0, 2, 2, 0),
        (0, 2, 2, 2),
        (2, 0, 0, 2),
        (2, 0, 2, 0),
        (2, 0, 2, 2),
        (2, 2, 0, 0),
        (2, 2, 0, 2),
        (2, 2, 2, 0),
        (2, 2, 2, 2),
    )
    assert tuple(sector.page_spins for sector in manifest.sectors) == expected_pages
    assert all(
        sector.weighted_coefficient.numerator > 0
        for sector in manifest.sectors
    )


def test_manifest_sector_ledger_resums_to_its_activity_row() -> None:
    manifest = build_unit_rim_manifest()
    from_sectors: dict[int, Fraction] = {}
    for sector in manifest.sectors:
        coefficient = _fraction(
            sector.weighted_coefficient.numerator,
            sector.weighted_coefficient.denominator,
        )
        from_sectors[sector.heat_exponent] = (
            from_sectors.get(sector.heat_exponent, Fraction(0)) + coefficient
        )
    from_activity = {
        term.heat_exponent: _fraction(
            term.coefficient.numerator, term.coefficient.denominator
        )
        for term in manifest.activity
    }
    assert from_sectors == from_activity == {
        0: Fraction(1, 4),
        16: Fraction(9, 2),
        24: Fraction(6),
        32: Fraction(21, 4),
    }
    assert {
        term.heat_exponent: term.sector_count for term in manifest.activity
    } == {0: 1, 16: 6, 24: 4, 32: 1}


def test_canonical_json_and_digest_are_stable() -> None:
    manifest = build_unit_rim_manifest()
    encoded = canonical_manifest_json(manifest)
    decoded = json.loads(encoded)
    assert decoded == manifest.to_json_object()
    assert decoded["schema"] == SCHEMA
    assert "\n" not in encoded
    assert manifest_sha256(manifest) == (
        "f7ad2fd06add0c8e5bc51e4aa340bdb0e86687f52d664d3ce3397f21be5d2e52"
    )
    assert canonical_manifest_json() == encoded
