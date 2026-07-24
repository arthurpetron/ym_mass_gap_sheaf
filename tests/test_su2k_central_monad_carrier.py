"""Exact tests for the finite SU(2)_k central-monad campaign."""

from fractions import Fraction

from computations.fusion_closed_surface_carrier import (
    character_product_channels,
)
from computations.su2k_central_monad_carrier import (
    central_comonad,
    central_induction,
    central_monad,
    central_monad_campaign_audit,
    central_vacuum_basis,
    comonad_counit_diagonal_multiplicity,
    degree_zero_adjunction_holds,
    forget_central,
    fusion_word_is_classically_stable,
    heat_transport_module_defect,
    pure_fusion_transport_is_module_morphism,
    su2k_fusion_labels,
    su2k_word_channels,
)


def test_su2k_affine_wall_and_classical_stable_range() -> None:
    assert su2k_fusion_labels(2, 2, 2) == (0,)
    assert su2k_fusion_labels(4, 2, 2) == (0, 2, 4)
    for level in range(3, 13):
        labels = (1, 1, 1)
        assert fusion_word_is_classically_stable(level, labels)
        assert su2k_word_channels(
            level, labels
        ) == character_product_channels(labels)


def test_current_pair_face_ledger_is_stable_from_level_two() -> None:
    for level in range(2, 13):
        assert fusion_word_is_classically_stable(level, (1, 1))
        assert su2k_word_channels(level, (1, 1)) == {0: 1, 2: 1}


def test_central_induction_is_the_exact_degree_zero_adjunction() -> None:
    for level in range(1, 9):
        for physical_label in range(level + 1):
            physical = {physical_label: 1}
            for left in range(level + 1):
                for right in range(level + 1):
                    central = {(left, right): 1}
                    assert degree_zero_adjunction_holds(
                        level, physical, central
                    )


def test_central_monad_and_comonad_are_uf_and_fu_on_objects() -> None:
    for level in range(1, 8):
        physical = {0: 1, min(2, level): 2}
        central = {(0, 0): 1, (level, level): 1}
        assert central_monad(level, physical) == forget_central(
            level, central_induction(level, physical)
        )
        assert central_comonad(level, central) == central_induction(
            level, forget_central(level, central)
        )


def test_pure_fusion_transport_lifts_as_a_module_morphism() -> None:
    for level in range(1, 10):
        for action_label in range(level + 1):
            for physical_label in range(level + 1):
                assert pure_fusion_transport_is_module_morphism(
                    level, action_label, {physical_label: 1}
                )


def test_physical_heat_weight_breaks_ordinary_module_naturality() -> None:
    after, before = heat_transport_module_defect(
        3, 1, 0, Fraction(1, 2)
    )
    assert after == {1: Fraction(1, 4)}
    assert before == {1: Fraction(1)}
    assert after != before


def test_object_level_counit_is_ambiguous_on_first_crossing() -> None:
    for level in range(2, 12):
        assert comonad_counit_diagonal_multiplicity(
            level, (1, 1)
        ) == 2


def test_central_vacuum_never_stabilizes_with_level() -> None:
    for level in range(0, 13):
        assert central_vacuum_basis(level) == {
            (label, label): 1 for label in range(level + 1)
        }
        assert len(central_vacuum_basis(level)) == level + 1


def test_campaign_audit_pins_the_adjudication() -> None:
    for level in range(3, 9):
        audit = central_monad_campaign_audit(level)
        assert audit.validates()
        assert audit.ledger == {1: 2, 3: 1}
        assert audit.degree_zero_adjunction
        assert audit.pure_transport_module_morphism
        assert not audit.heat_transport_module_morphism
        assert audit.counit_diagonal_multiplicity == 2
        assert audit.vacuum_basis_rank == level + 1
