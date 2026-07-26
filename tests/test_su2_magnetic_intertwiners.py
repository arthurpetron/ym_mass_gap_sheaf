"""Exact regression gates for open SU(2) magnetic-index tensors."""

from fractions import Fraction

import pytest
import sympy
from sympy.physics.wigner import clebsch_gordan

from computations.su2_magnetic_intertwiners import (
    RadicalSum,
    clebsch_gordan_basis_audit,
    clebsch_gordan_doubled,
    magnetic_indices,
    transverse_magnetic_tensor_packet,
    trivalent_invariance_audit,
    trivalent_invariant_component,
)
from computations.wigner_6j import QuadRadical


def test_arbitrary_label_formula_matches_independent_sympy_values() -> None:
    for left in range(5):
        for right in range(5):
            for output in range(abs(left - right), left + right + 1, 2):
                for left_magnetic in magnetic_indices(left):
                    for right_magnetic in magnetic_indices(right):
                        output_magnetic = left_magnetic + right_magnetic
                        if output_magnetic not in magnetic_indices(output):
                            continue
                        exact = clebsch_gordan_doubled(
                            left,
                            left_magnetic,
                            right,
                            right_magnetic,
                            output,
                            output_magnetic,
                        )
                        reference = clebsch_gordan(
                            sympy.Rational(left, 2),
                            sympy.Rational(right, 2),
                            sympy.Rational(output, 2),
                            sympy.Rational(left_magnetic, 2),
                            sympy.Rational(right_magnetic, 2),
                            sympy.Rational(output_magnetic, 2),
                        )
                        assert sympy.simplify(
                            reference**2
                            - sympy.Rational(
                                exact.square.numerator,
                                exact.square.denominator,
                            )
                        ) == 0
                        if reference:
                            assert (reference > 0) == (exact.coeff > 0)


def test_fundamental_singlet_and_triplet_phase_pin() -> None:
    root_half = QuadRadical.from_coeff_radicand(
        Fraction(1),
        Fraction(1, 2),
    )
    assert clebsch_gordan_doubled(1, 1, 1, -1, 0, 0) == root_half
    assert clebsch_gordan_doubled(1, -1, 1, 1, 0, 0) == -root_half
    assert clebsch_gordan_doubled(1, 1, 1, -1, 2, 0) == root_half
    assert clebsch_gordan_doubled(1, -1, 1, 1, 2, 0) == root_half


def test_arbitrary_label_path_is_not_limited_by_old_prime_table() -> None:
    assert clebsch_gordan_doubled(60, 60, 60, 60, 120, 120) == (
        QuadRadical(Fraction(1), 1)
    )
    coefficient = clebsch_gordan_doubled(50, 0, 52, 0, 2, 0)
    assert coefficient.square > 0


def test_clebsch_gordan_bases_are_exactly_orthonormal_and_complete() -> None:
    expected = {
        1: (9, 25),
        2: (36, 196),
        3: (100, 900),
    }
    for cutoff, (vectors, entries) in expected.items():
        audit = clebsch_gordan_basis_audit(cutoff)
        assert audit.validates()
        assert audit.coupled_basis_vectors == vectors
        assert audit.product_basis_vectors == vectors
        assert audit.orthonormality_entries_checked == entries
        assert audit.completeness_entries_checked == entries
        assert audit.nonzero_orthonormality_residuals == 0
        assert audit.nonzero_completeness_residuals == 0


def test_normalized_trivalent_invariants_include_oriented_legs() -> None:
    for labels in ((0, 0, 0), (1, 1, 0), (1, 1, 2), (2, 3, 3)):
        for orientations in (
            (1, 1, 1),
            (-1, -1, 1),
            (1, -1, -1),
            (-1, -1, -1),
        ):
            norm = sum(
                (
                    trivalent_invariant_component(
                        labels,
                        (first, second, third),
                        orientations,
                    ).square
                    for first in magnetic_indices(labels[0])
                    for second in magnetic_indices(labels[1])
                    for third in magnetic_indices(labels[2])
                ),
                start=Fraction(0),
            )
            assert norm == 1


def test_trivalent_tensors_are_annihilated_by_exact_lie_generators() -> None:
    expected = {
        1: (4, 13),
        2: (11, 103),
        3: (23, 439),
    }
    for cutoff, (triples, components) in expected.items():
        audit = trivalent_invariance_audit(cutoff)
        assert audit.validates()
        assert audit.admissible_label_triples == triples
        assert audit.magnetic_components_checked == components
        assert audit.nonzero_jz_residuals == 0
        assert audit.nonzero_raising_residuals == 0
        assert audit.nonzero_lowering_residuals == 0


def test_transverse_packets_materialize_every_local_channel() -> None:
    expected = {
        1: (20, 45),
        2: (55, 126),
        3: (115, 270),
    }
    for cutoff, (internal_tensors, boundary_tensors) in expected.items():
        packet = transverse_magnetic_tensor_packet(cutoff)
        assert packet.validates()
        assert len(packet.internal_tensors) == internal_tensors
        assert len(packet.boundary_tensors) == boundary_tensors
        assert packet.nonzero_internal_components > 0
        assert packet.nonzero_boundary_components > 0


def test_global_operator_claims_remain_fail_closed() -> None:
    packet = transverse_magnetic_tensor_packet(3)
    assert packet.arbitrary_label_factorial_formula_exposed
    assert packet.fixed_condon_shortley_phase
    assert packet.every_local_tensor_exact
    assert not packet.global_tensor_network_contracted
    assert not packet.global_f_r_transport_evaluated
    assert not packet.carrier_amplitude_cutoff_modulus_proved
    assert not packet.cp_order_domination_proved


def test_radical_sum_retains_unlike_squarefree_parts() -> None:
    root_two = RadicalSum.from_quad(
        QuadRadical.from_coeff_radicand(Fraction(1), Fraction(2))
    )
    root_three = RadicalSum.from_quad(
        QuadRadical.from_coeff_radicand(Fraction(1), Fraction(3))
    )
    assert (root_two + root_three).terms == (
        (2, Fraction(1)),
        (3, Fraction(1)),
    )
    assert (root_two * root_two) == RadicalSum.rational(2)


def test_invalid_labels_are_rejected_or_zero() -> None:
    with pytest.raises(ValueError):
        magnetic_indices(-1)
    with pytest.raises(ValueError):
        clebsch_gordan_doubled(-1, 0, 0, 0, 0, 0)
    assert clebsch_gordan_doubled(1, 0, 1, 0, 0, 0).is_zero()
