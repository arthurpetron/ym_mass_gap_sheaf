"""Regression pins for the physical pair-family heat census."""

from fractions import Fraction

from computations.fusion_pair_heat_census import (
    diagonal_surface_heat_activity,
    diagonal_surface_heat_census,
    intersecting_pair_heat_census,
    pair_heat_census_certificate,
    surface_pair_heat_activity,
)
from computations.hypercube4d_survey import (
    hypercube,
    kernel_basis,
    mask_orbits,
    surface_assignment,
    surface_cell_counts,
    surfaces,
    symmetry_maps,
    vertex_sixj_product,
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


def test_uniform_label_two_surface_has_2d_yang_mills_weight() -> None:
    complex_, faces, meta = hypercube()
    for mask in surfaces(kernel_basis(complex_, faces))[1:]:
        _vertices, _edges, face_count, euler = surface_cell_counts(
            complex_, faces, mask
        )
        amplitude = vertex_sixj_product(
            meta, surface_assignment(mask, label=2)
        )
        assert amplitude * Fraction(3) ** face_count == (
            Fraction(3) ** euler
        )


def test_all_duplicate_surface_orbits_are_structurally_positive() -> None:
    records = diagonal_surface_heat_census()
    assert len(records) == 8
    assert sum(record.orbit_size for record in records) == 127
    assert all(record.coefficientwise_positive for record in records)
    assert len(
        {
            tuple(sorted(record.heat_activity.items()))
            for record in records
        }
    ) == 6

    by_face_count: dict[int, list[dict[int, Fraction]]] = {}
    complex_, faces, _meta = hypercube()
    for record in records:
        face_count = record.representative.bit_count()
        by_face_count.setdefault(face_count, []).append(
            record.heat_activity
        )
    assert {0: Fraction(1), 128: Fraction(1)} in by_face_count[16]
    assert {
        0: Fraction(1),
        48: Fraction(18),
        96: Fraction(81),
    } in by_face_count[12]

    # Directly enumerate the two smallest diagonal ledgers as an independent
    # check of the component formula without paying the 2^16 torus cost.
    representatives = [
        orbit[0]
        for orbit in mask_orbits(
            surfaces(kernel_basis(complex_, faces))[1:],
            symmetry_maps(hypercube()[2]),
        )
    ]
    for mask in representatives[:2]:
        assert surface_pair_heat_activity(
            hypercube()[2], mask, mask
        ) == diagonal_surface_heat_activity(complex_, faces, mask)
