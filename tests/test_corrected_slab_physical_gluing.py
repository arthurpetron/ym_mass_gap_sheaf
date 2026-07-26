"""Exact gates for adjacent corrected-slab physical gluing."""

from fractions import Fraction

import pytest

from computations.corrected_slab_physical_gluing import (
    fixed_spatial_two_step_slab_plaquettes,
    interface_floor_ceiling_no_go,
    two_slab_physical_gluing_audit,
)


def test_two_adjacent_slabs_form_the_exact_120_face_fiber_product() -> None:
    audit = two_slab_physical_gluing_audit()

    assert audit.validates()
    assert audit.lower_face_count == audit.upper_face_count == 72
    assert audit.shared_interface_face_count == 24
    assert audit.glued_face_count == 120
    assert len(fixed_spatial_two_step_slab_plaquettes()) == 120
    assert audit.shared_interface_link_count == 48
    assert audit.shared_interface_vertex_count == 26


def test_isotropic_extent_two_is_not_fixed_spatial_time_gluing() -> None:
    audit = two_slab_physical_gluing_audit()

    assert audit.isotropic_extent_two_face_count == 405
    assert audit.fixed_spatial_union_is_not_isotropic_extent_two
    assert not audit.independent_probability_convolution_is_physical_gluing


def test_interface_density_is_counted_twice_before_correction() -> None:
    audit = two_slab_physical_gluing_audit()

    assert audit.product_density_interface_multiplicity == 2
    assert audit.physical_density_interface_multiplicity == 1
    assert audit.exact_unnormalized_density_correction == (
        "W_lower*W_upper=W_glued*W_interface"
    )
    assert audit.boundary_fiber_product_required
    assert audit.new_partition_normalization_required
    assert not audit.physical_channel_gluing_identity_proved


def test_worst_holonomy_interface_correction_collapses_as_a_to_the_72() -> None:
    previous = Fraction(1)
    for level in range(1, 6):
        spacing = Fraction(1, 2**level)
        certificate = interface_floor_ceiling_no_go(
            1 - spacing,
            dyadic_spacing=True,
        )

        assert certificate.validates()
        assert certificate.interface_order_coefficient > 0
        assert certificate.collapse_upper_bound <= spacing**72
        assert certificate.dyadic_spacing_power_upper_bound < previous
        assert not certificate.spacing_uniform_interface_comparison_proved
        assert not certificate.direct_integrated_glued_block_comparison_refuted
        previous = certificate.dyadic_spacing_power_upper_bound


def test_invalid_interface_coupling_fails_closed() -> None:
    with pytest.raises(ValueError):
        interface_floor_ceiling_no_go(Fraction(1))
