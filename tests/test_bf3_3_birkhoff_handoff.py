"""Exact regression gates for the BF3.3 Birkhoff handoff audit."""

from fractions import Fraction

from computations.bf3_3_birkhoff_handoff import (
    EXPECTED_FIXED_CUTOFF_RATES,
    bf33_certificate,
    counterexample_to_uniform_rate,
    coupling_uniform_cutoff_fence,
    diagonal_packet_spin_two_multiplicity,
    direct_multiplicity_identity_holds_through,
    local_gram_spread_lower_witness,
    observed_fixed_cutoff_rates,
    restricted_spin_two_corner,
    restricted_spin_two_corner_closed_form,
    whole_slab_density_handoff_audit,
)


def test_whole_slab_density_has_only_componentwise_rank_one_contraction() -> None:
    audit = whole_slab_density_handoff_audit()

    assert audit.validates()
    assert audit.boundary_dimension == 64
    assert audit.support_component_count == 32
    assert audit.component_shape_census == (((2, 2), 32),)
    assert audit.component_rate_census == ((Fraction(0), 32),)
    assert audit.every_component_rank_one
    assert not audit.cut_signature_mixing
    assert not audit.global_positive_rectangle
    assert not audit.global_projective_diameter_finite


def test_diagonal_packet_family_has_a_closed_spin_two_multiplicity() -> None:
    assert diagonal_packet_spin_two_multiplicity(0, 0) == 0
    assert diagonal_packet_spin_two_multiplicity(0, 5) == 1
    assert diagonal_packet_spin_two_multiplicity(3, 3) == 9
    assert diagonal_packet_spin_two_multiplicity(3, 5) == 10
    assert direct_multiplicity_identity_holds_through(7)

    for cutoff in range(1, 20):
        assert restricted_spin_two_corner(cutoff) == (
            restricted_spin_two_corner_closed_form(cutoff)
        )


def test_local_reflected_gram_cross_ratio_grows_quadratically() -> None:
    for cutoff in (1, 2, 3, 7, 20):
        witness = local_gram_spread_lower_witness(cutoff)
        assert witness.validates()
        assert witness.high_corner == 1
        assert witness.mixed_corner == 3 * cutoff
        assert witness.spread_lower_bound >= Fraction(cutoff * cutoff, 6)
        assert witness.rate_lower_bound >= witness.quadratic_rate_floor


def test_no_cutoff_independent_birkhoff_rate_survives_this_primitive() -> None:
    for proposed in (Fraction(0), Fraction(1, 2), Fraction(9, 10), Fraction(99, 100)):
        counterexample = counterexample_to_uniform_rate(proposed)
        assert counterexample.validates()
        assert counterexample.exact_rate_lower_bound > proposed

    assert counterexample_to_uniform_rate(Fraction(1, 2)).counter_cutoff == 5
    assert counterexample_to_uniform_rate(Fraction(9, 10)).counter_cutoff == 11
    assert counterexample_to_uniform_rate(Fraction(99, 100)).counter_cutoff == 35


def test_fixed_cutoff_rates_are_exact_but_tend_toward_one() -> None:
    assert observed_fixed_cutoff_rates() == EXPECTED_FIXED_CUTOFF_RATES
    rates = tuple(rate for _cutoff, rate in EXPECTED_FIXED_CUTOFF_RATES)
    assert rates == tuple(sorted(rates))
    assert rates[-1] == Fraction(1715, 1733)


def test_cutoff_tail_is_not_uniform_over_the_heat_coordinate() -> None:
    for cutoff in (0, 1, 4, 16):
        witness = coupling_uniform_cutoff_fence(cutoff)
        assert witness.validates()
        assert 0 < witness.coupling < 1
        assert witness.leading_feature >= Fraction(cutoff + 2, 2)


def test_bf33_closes_only_the_admissibility_audit() -> None:
    certificate = bf33_certificate()

    assert certificate.validates()
    assert certificate.exit_kind == "exact-obstruction-and-required-repair"
    assert certificate.handoff.retained_signed_intertwiner_transport
    assert not certificate.handoff.ready_for_bf4()
    assert certificate.bf32_status == (
        "open-all-label-physical-kernel-and-remainder"
    )
    assert certificate.next_gate == "BF3.2-before-BF4"
