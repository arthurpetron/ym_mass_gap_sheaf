"""Exact regression gates for the BF3.2 fixed-block all-label completion."""

from fractions import Fraction

import pytest

from computations.all_label_whole_slab_tail import (
    WHOLE_SLAB_FACE_COUNT,
    bf32_all_label_frontier,
    computable_all_label_haar_coefficient,
    coupling_dependent_cutoff,
    external_dimension,
    finite_cutoff_whole_slab_haar_coefficient,
    heat_character_sup_term,
    heat_character_tail_ratio,
    single_plaquette_all_label_tail,
    strong_coupling_normalized_cutoff,
    strong_coupling_normalized_tail,
    whole_slab_all_label_cauchy_certificate,
)


def test_exact_heat_character_tail_uses_the_first_omitted_ratio() -> None:
    coupling = Fraction(1, 2)
    tail = single_plaquette_all_label_tail(coupling, 2)

    assert tail.validates()
    assert heat_character_sup_term(coupling, 0) == 1
    assert heat_character_sup_term(coupling, 1) == Fraction(1, 2)
    assert heat_character_sup_term(coupling, 2) == Fraction(9, 256)
    assert tail.first_omitted == Fraction(1, 2048)
    assert tail.ratio == heat_character_tail_ratio(coupling, 2)
    assert tail.ratio == Fraction(25, 8192)


def test_whole_slab_tail_is_uniform_after_external_dimension_weighting() -> None:
    vacuum = whole_slab_all_label_cauchy_certificate(Fraction(1, 2), 5)
    inserted = whole_slab_all_label_cauchy_certificate(
        Fraction(1, 2),
        5,
        (1, 2, 3),
    )

    assert vacuum.validates()
    assert inserted.validates()
    assert inserted.fine_face_count == WHOLE_SLAB_FACE_COUNT == 72
    assert inserted.external_dimension == external_dimension((1, 2, 3)) == 24
    assert (
        inserted.dimension_weighted_tail_bound
        == vacuum.dimension_weighted_tail_bound
    )
    assert (
        inserted.raw_coefficient_tail_bound
        == 24 * vacuum.raw_coefficient_tail_bound
    )
    assert not inserted.arbitrary_volume_uniform


def test_all_label_kernel_has_literal_finite_haar_approximants() -> None:
    vacuum_labels = (0,) * 9
    coefficient = computable_all_label_haar_coefficient(
        Fraction(1, 2),
        vacuum_labels,
    )

    assert coefficient.validates()
    assert coefficient.approximation(0) == 1
    assert (
        finite_cutoff_whole_slab_haar_coefficient(
            Fraction(1, 2),
            0,
            vacuum_labels,
        )
        == 1
    )
    assert coefficient.limit_error_bound(2) > 0
    assert coefficient.weighted_limit_error_bound(2) == (
        coefficient.limit_error_bound(2)
    )


def test_cutoff_schedule_is_constructive_and_coupling_dependent() -> None:
    tolerance = Fraction(1, 100)
    points = tuple(
        coupling_dependent_cutoff(coupling, tolerance)
        for coupling in (Fraction(1, 2), Fraction(3, 4), Fraction(9, 10))
    )

    assert all(point.validates() for point in points)
    assert tuple(point.cutoff for point in points) == tuple(
        sorted(point.cutoff for point in points)
    )
    assert len({point.cutoff for point in points}) == len(points)
    assert all(point.tail_bound <= tolerance for point in points)


def test_strong_coupling_tail_controls_the_normalized_actual_density() -> None:
    certificate = strong_coupling_normalized_tail(Fraction(1, 2), 11)

    assert certificate.validates()
    assert 0 < certificate.plaquette_density_floor < 1
    assert 0 < certificate.partition_floor < 1
    assert certificate.normalized_total_variation_tail > 0
    assert certificate.normalized_total_variation_tail < Fraction(1, 100)
    assert certificate.truncated_density_positive

    schedule = strong_coupling_normalized_cutoff(
        Fraction(1, 2),
        Fraction(1, 100),
    )
    assert schedule.validates()
    assert schedule.cutoff == 11

    with pytest.raises(ValueError, match="outside its positivity corridor"):
        strong_coupling_normalized_tail(Fraction(3, 4), 6)


def test_bf32_frontier_does_not_promote_a_fixed_block_tail_to_bf4() -> None:
    frontier = bf32_all_label_frontier()

    assert frontier.validates()
    assert frontier.fixed_block_all_label_kernel
    assert frontier.computable_haar_cauchy_name
    assert frontier.coupling_dependent_cutoff_constructed
    assert frontier.normalized_strong_coupling_tail
    assert not frontier.bf2_psd_norm_identified
    assert not frontier.arbitrary_volume_uniform
    assert not frontier.actual_rg_remainder_bounded
    assert not frontier.bf32_closed
    assert frontier.next_gate == "BF3.2-remains-before-BF4"
