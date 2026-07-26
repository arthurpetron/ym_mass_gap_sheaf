"""Exact gates for boundary-conditioned transfer Markovization."""

from fractions import Fraction

import pytest

from computations.boundary_message_markovization import (
    all_label_fine_boundary_transfer,
    coarse_boundary_sufficiency_audit,
    markovize_transfer_chain,
    physical_boundary_message_blueprint,
)


def test_backward_messages_make_every_transfer_row_stochastic() -> None:
    certificate = markovize_transfer_chain(
        (
            ((1, 2), (3, 1)),
            ((2, 1), (1, 4)),
        ),
        (1, 2),
    )

    assert certificate.validates()
    assert certificate.backward_messages == (
        (Fraction(22), Fraction(21)),
        (Fraction(4), Fraction(9)),
        (Fraction(1), Fraction(2)),
    )
    assert all(
        sum(row, start=Fraction(0)) == 1
        for kernel in certificate.markov_kernels
        for row in kernel
    )


def test_markov_composite_is_the_telescoped_raw_endpoint_kernel() -> None:
    certificate = markovize_transfer_chain(
        (
            ((1, 2), (3, 1)),
            ((2, 1), (1, 4)),
        ),
        (1, 2),
    )

    assert certificate.telescoping_endpoint_identity
    assert certificate.markov_composite == (
        (Fraction(2, 11), Fraction(9, 11)),
        (Fraction(1, 3), Fraction(2, 3)),
    )
    assert not certificate.independent_row_normalization_used


def test_physical_blueprint_closes_composition_algebra_but_not_uniformity() -> None:
    blueprint = physical_boundary_message_blueprint()

    assert blueprint.validates()
    assert blueprint.raw_transfer_fiber_product_composition_exact
    assert blueprint.backward_message_markovization_exact
    assert blueprint.finite_horizon_mass_preserving_composition_exact
    assert not (
        blueprint.independent_one_slab_row_normalization_composes_physically
    )
    assert blueprint.all_label_continuous_boundary_transfer_constructed
    assert blueprint.fine_boundary_physical_gluing_channel_constructed
    assert not blueprint.nine_slot_coarse_markov_intertwining_proved
    assert not blueprint.spacing_uniform_boundary_message_ratio_proved
    assert not blueprint.spacing_uniform_grouped_minorization_proved


def test_all_label_fine_boundary_transfer_has_exact_physical_census() -> None:
    transfer = all_label_fine_boundary_transfer(Fraction(1, 2))

    assert transfer.validates()
    assert transfer.source_spatial_face_count == 24
    assert transfer.target_spatial_face_count == 24
    assert transfer.temporal_face_count == 24
    assert transfer.source_boundary_link_count == 48
    assert transfer.target_boundary_link_count == 48
    assert transfer.internal_temporal_link_count == 20
    assert transfer.raw_products_equal_physical_glued_density
    assert transfer.fine_boundary_markov_channel_constructed
    assert not transfer.nine_slot_coarse_markov_intertwining_proved


def test_nine_coarse_loops_miss_an_exact_center_boundary_direction() -> None:
    audit = coarse_boundary_sufficiency_audit(Fraction(1, 2))

    assert audit.validates()
    assert audit.witness_link_id == 7
    assert audit.witness_geometric_link == ((0, 0, 1, 0), 0)
    assert audit.witness_incident_lower_spatial_faces == (1, 9, 10)
    assert audit.identity_and_center_flip_have_same_coarse_holonomies
    assert audit.center_flip_changes_spatial_weight
    assert not audit.raw_transfer_factors_through_nine_coarse_loops
    assert not audit.coarse_markov_lumpability_refuted
    assert audit.enlargement_or_conditional_cancellation_required


def test_invalid_transfer_chains_fail_closed() -> None:
    with pytest.raises(ValueError):
        markovize_transfer_chain((), (1,))
    with pytest.raises(ValueError):
        markovize_transfer_chain((((1, 0), (0, 0)),), (1, 1))
    with pytest.raises(ValueError):
        markovize_transfer_chain((((1, 1),),), (0,))
    with pytest.raises(ValueError):
        all_label_fine_boundary_transfer(Fraction(1))
    with pytest.raises(ValueError):
        coarse_boundary_sufficiency_audit(Fraction(1))
