"""Exact gates for the BF4 finite-cutoff all-label recoupling carrier."""

import pytest

from computations.exact_haar_network import invariant_multiplicity
from computations.grouped_all_label_haar_refresh import (
    transverse_cutoff_one_fusion_audit,
)
from computations.transverse_all_label_recoupling import (
    finite_cutoff_transverse_recoupling_carrier,
    transverse_recoupling_census,
)


def test_cutoff_one_recovers_the_existing_complete_fusion_census() -> None:
    prior = transverse_cutoff_one_fusion_audit()
    census = transverse_recoupling_census(1)
    assert census.validates()
    assert census.internally_admissible_face_assignments == (
        prior.binary_internal_admissible_assignments
    )
    assert census.complete_boundary_channel_paths == (
        prior.complete_core_fusion_paths
    )


def test_exact_small_cutoff_census() -> None:
    expected = {
        0: (1, 1, 1, 1),
        1: (4, 5, 1024, 10673),
        2: (11, 14, 184437, 29647857),
        3: (23, 30, 8114176, 8982556738),
        4: (42, 55, 179406250, 1075792843993),
        5: (69, 91, 2279938752, 54549556261540),
    }
    for cutoff, (
        local_internal,
        local_boundary,
        assignments,
        paths,
    ) in expected.items():
        census = transverse_recoupling_census(cutoff)
        assert census.validates()
        assert census.local_internal_channels_per_link == local_internal
        assert census.local_boundary_channels_per_link == local_boundary
        assert census.internally_admissible_face_assignments == assignments
        assert census.complete_boundary_channel_paths == paths


def test_local_bases_retain_orientations_and_every_channel() -> None:
    carrier = finite_cutoff_transverse_recoupling_carrier(2)
    assert carrier.validates()
    assert len(carrier.internal_bases) == 5
    assert len(carrier.boundary_bases) == 9
    assert all(
        channel.invariant_dimension
        == invariant_multiplicity(channel.leg_labels)
        == 1
        for basis in carrier.internal_bases
        for channel in basis.channels
    )
    assert all(
        leg.orientation in (-1, 1)
        for basis in carrier.internal_bases + carrier.boundary_bases
        for leg in basis.legs
    )

    first_boundary = carrier.boundary_bases[0]
    assert tuple(
        channel.output_label
        for channel in first_boundary.channels
        if channel.leg_labels == (2, 2)
    ) == (0, 2, 4)
    assert max(
        channel.output_label
        for basis in carrier.boundary_bases
        for channel in basis.channels
    ) == 4


def test_successive_cutoffs_are_literal_basis_inclusions() -> None:
    carriers = tuple(
        finite_cutoff_transverse_recoupling_carrier(cutoff)
        for cutoff in range(6)
    )
    assert all(
        smaller.embeds_into(larger)
        for smaller, larger in zip(carriers[:-1], carriers[1:], strict=True)
    )
    assert not carriers[2].embeds_into(carriers[1])


def test_operator_and_limit_claims_remain_fail_closed() -> None:
    census = transverse_recoupling_census(3)
    assert census.compact_factor_graph_used
    assert not census.flat_boundary_profile_ledger_materialized
    assert census.finite_cutoff_basis_inclusion_proved
    assert not census.carrier_amplitude_cutoff_modulus_proved
    assert not census.coherent_all_label_haar_amplitudes_evaluated
    assert not census.global_f_r_transport_evaluated
    assert not census.cp_order_domination_proved


def test_negative_cutoff_is_rejected() -> None:
    with pytest.raises(ValueError):
        finite_cutoff_transverse_recoupling_carrier(-1)
    with pytest.raises(ValueError):
        transverse_recoupling_census(-1)
