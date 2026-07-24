"""Exact regression pins for the BF1.5 three-strand gate."""

from fractions import Fraction

from computations.three_strand_corrected_slab import (
    EXPECTED_HEAT_ACTIVITY,
    EXPECTED_REFLECTED_GRAM,
    bf15_certificate,
    haar_pushforward_seed,
    minimal_sector_census,
    reflected_gram_audit,
    three_way_haar_audit,
)


def test_minimal_three_strand_sector_is_genuinely_four_dimensional() -> None:
    census = minimal_sector_census()
    assert census.validates()
    assert census.strand_areas == (6, 6, 10)
    assert census.union_area == 15
    assert census.coordinate_plane_count == 6
    assert census.co_minimal_triple_count == 192
    assert dict(census.face_occupancy_counts) == {0: 57, 1: 9, 2: 5, 3: 1}
    assert dict(census.edge_leg_counts) == {0: 91, 2: 10, 4: 11, 6: 4}


def test_direct_left_right_and_heat_activities_agree_exactly() -> None:
    audit = three_way_haar_audit()
    assert audit.validates()
    assert audit.direct_haar == {0: Fraction(83, 5184)}
    assert audit.left_coherent_haar == audit.right_coherent_haar
    assert audit.left_heat_activity == EXPECTED_HEAT_ACTIVITY
    assert audit.negative_fixed_channels == 0


def test_closed_surface_reflection_carrier_has_exact_negative_minor() -> None:
    audit = reflected_gram_audit()
    assert audit.validates_negative_exit()
    assert audit.matrix == EXPECTED_REFLECTED_GRAM
    assert audit.leading_principal_minors[:3] == (
        Fraction(1),
        Fraction(20911, 20736),
        Fraction(-1, 65536),
    )
    assert audit.first_negative_principal_minor == (
        3,
        Fraction(-1, 65536),
    )


def test_unnormalized_path_to_channel_pushforward_is_explicit() -> None:
    seed = haar_pushforward_seed()
    assert seed.validates()
    assert len(seed.fine_path_outputs) == 96
    assert len(seed.coarse_fibres) == 64
    assert seed.total_mass == EXPECTED_HEAT_ACTIVITY
    assert seed.reflected_total_mass == seed.total_mass
    assert seed.reflection_compatible
    assert seed.remainder_outside_carrier == {}


def test_bf15_closes_with_a_negative_reflection_carrier_certificate() -> None:
    certificate = bf15_certificate()
    assert certificate.validates()
    assert certificate.exit_kind == "negative-reflection-carrier"
