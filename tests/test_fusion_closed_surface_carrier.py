"""Regression pins for the first fusion-closed physical carrier."""

from fractions import Fraction

import pytest

from computations.corrected_slab_haar_network import (
    embedded_negative_channel_surface_pair,
    embedded_negative_hypercube_assignment,
)
from computations.exact_haar_network import sp_eval
from computations.fusion_closed_surface_carrier import (
    ClosedSurfaceStrand,
    FusionClosedSurfaceFamily,
    audit_surface_family,
    character_product_channels,
    complete_fusion_ledger,
    is_closed_binary_surface,
)


def negative_channel_surface_family() -> FusionClosedSurfaceFamily:
    left, right = embedded_negative_channel_surface_pair()
    return FusionClosedSurfaceFamily(
        1,
        (
            ClosedSurfaceStrand(left, 1),
            ClosedSurfaceStrand(right, 1),
        ),
    )


def test_character_product_retains_fusion_path_multiplicity() -> None:
    assert character_product_channels(()) == {0: 1}
    assert character_product_channels((1, 1)) == {0: 1, 2: 1}
    assert character_product_channels((1, 1, 1)) == {1: 2, 3: 1}


def test_carrier_rejects_an_open_face() -> None:
    assert not is_closed_binary_surface(1, 1)
    with pytest.raises(ValueError, match="nonzero mod-two boundary"):
        FusionClosedSurfaceFamily(
            1, (ClosedSurfaceStrand(1, 1),)
        )


def test_surface_family_carrier_is_closed_under_union() -> None:
    left, right = embedded_negative_channel_surface_pair()
    left_family = FusionClosedSurfaceFamily(
        1, (ClosedSurfaceStrand(left, 1),)
    )
    right_family = FusionClosedSurfaceFamily(
        1, (ClosedSurfaceStrand(right, 1),)
    )
    assert left_family.union(right_family) == negative_channel_surface_family()


def test_negative_fixed_channel_is_retained_by_complete_ledger() -> None:
    family = negative_channel_surface_family()
    ledger = complete_fusion_ledger(family)
    assert len(ledger) == 16
    assert sum(ledger.values()) == 16
    assert embedded_negative_hypercube_assignment() in ledger
    assert ledger[embedded_negative_hypercube_assignment()] == 1


def test_complete_physical_family_is_exactly_heat_positive() -> None:
    audit = audit_surface_family(negative_channel_surface_family())
    assert audit.validates()
    assert audit.ledger_size == audit.fusion_path_count == 16
    assert audit.negative_fixed_channels == 4
    assert audit.direct_haar_amplitude == {
        0: Fraction(31, 331776)
    }
    assert audit.resummed_haar_amplitude == audit.direct_haar_amplitude
    assert audit.heat_activity == {
        48: Fraction(1),
        56: Fraction(12),
        64: Fraction(6),
        72: Fraction(12),
        80: Fraction(1),
    }
    assert audit.heat_sign == "positive"
    assert sp_eval(audit.heat_activity, Fraction(1, 2)) > 0
