"""Exact gates for the BF4 cutoff-one open-index spin network."""

from collections import Counter
from fractions import Fraction
from itertools import product
from typing import cast

import sympy
from sympy.physics.wigner import clebsch_gordan, wigner_3j

from computations.exact_haar_network import (
    fusion_labels,
    invariant_multiplicity,
)
from computations.su2_magnetic_intertwiners import (
    clebsch_gordan_doubled,
    trivalent_invariant_component,
)
from computations.transverse_open_index_network import (
    cutoff_one_cg_coefficient,
    cutoff_one_open_index_network,
    cutoff_one_three_j_coefficient,
    duality_coefficient,
    four_fundamental_transport_census,
    magnetic_indices,
    pair_pair_invariant_coefficient,
)
from computations.wigner_6j import QuadRadical


def _sympy_radical(value: QuadRadical) -> sympy.Expr:
    return (
        sympy.Rational(value.coeff.numerator, value.coeff.denominator)
        * sympy.sqrt(value.rad)
    )


def test_open_index_incidence_connects_every_local_tensor_port() -> None:
    network = cutoff_one_open_index_network()
    assert network.validates()
    assert len(network.face_cycles) == 15
    assert sum(len(cycle.incidences) for cycle in network.face_cycles) == 33
    assert network.magnetic_corner_count == 33
    assert network.every_corner_has_degree_two
    assert len(network.internal_nodes) == 5
    assert len(network.boundary_nodes) == 9
    assert network.local_internal_channel_records == 20
    assert network.local_boundary_channel_records == 45
    assert network.complete_internal_assignment_count == 1024
    assert network.complete_boundary_channel_path_count == 10673


def test_cutoff_one_cg_and_three_j_tables_match_sympy_exactly() -> None:
    for left, right in product(range(2), repeat=2):
        for left_magnetic, right_magnetic in product(
            magnetic_indices(left),
            magnetic_indices(right),
        ):
            for output in fusion_labels(left, right):
                for output_magnetic in magnetic_indices(output):
                    expected = clebsch_gordan(
                        sympy.Rational(left, 2),
                        sympy.Rational(right, 2),
                        sympy.Rational(output, 2),
                        sympy.Rational(left_magnetic, 2),
                        sympy.Rational(right_magnetic, 2),
                        sympy.Rational(output_magnetic, 2),
                    )
                    actual = cutoff_one_cg_coefficient(
                        left,
                        left_magnetic,
                        right,
                        right_magnetic,
                        output,
                        output_magnetic,
                    )
                    assert sympy.simplify(_sympy_radical(actual) - expected) == 0

    for labels in product(range(2), repeat=3):
        if invariant_multiplicity(labels) != 1:
            continue
        for magnetics in product(
            *(magnetic_indices(label) for label in labels)
        ):
            expected = wigner_3j(
                *(sympy.Rational(label, 2) for label in labels),
                *(sympy.Rational(magnetic, 2) for magnetic in magnetics),
            )
            actual = cutoff_one_three_j_coefficient(
                cast(tuple[int, int, int], labels),
                cast(tuple[int, int, int], magnetics),
            )
            assert sympy.simplify(_sympy_radical(actual) - expected) == 0


def test_cutoff_one_tables_agree_with_arbitrary_label_implementation() -> None:
    for left, right in product(range(2), repeat=2):
        for left_magnetic, right_magnetic in product(
            magnetic_indices(left),
            magnetic_indices(right),
        ):
            for output in fusion_labels(left, right):
                for output_magnetic in magnetic_indices(output):
                    assert cutoff_one_cg_coefficient(
                        left,
                        left_magnetic,
                        right,
                        right_magnetic,
                        output,
                        output_magnetic,
                    ) == clebsch_gordan_doubled(
                        left,
                        left_magnetic,
                        right,
                        right_magnetic,
                        output,
                        output_magnetic,
                    )

    for labels in product(range(2), repeat=3):
        if invariant_multiplicity(labels) != 1:
            continue
        labels_three = cast(tuple[int, int, int], labels)
        for magnetics in product(
            *(magnetic_indices(label) for label in labels)
        ):
            magnetics_three = cast(tuple[int, int, int], magnetics)
            assert cutoff_one_three_j_coefficient(
                labels_three,
                magnetics_three,
            ) == trivalent_invariant_component(
                labels_three,
                magnetics_three,
            )


def test_pair_pair_shared_channel_basis_is_exactly_orthonormal() -> None:
    for labels in product(range(2), repeat=4):
        labels_four = cast(tuple[int, int, int, int], labels)
        channels = tuple(
            sorted(
                set(fusion_labels(labels[0], labels[1]))
                & set(fusion_labels(labels[2], labels[3]))
            )
        )
        for left_channel in channels:
            for right_channel in channels:
                overlap = sympy.simplify(
                    sum(
                        (
                            _sympy_radical(
                                pair_pair_invariant_coefficient(
                                    labels_four,
                                    cast(
                                        tuple[int, int, int, int],
                                        magnetics,
                                    ),
                                    left_channel,
                                )
                            )
                            * _sympy_radical(
                                pair_pair_invariant_coefficient(
                                    labels_four,
                                    cast(
                                        tuple[int, int, int, int],
                                        magnetics,
                                    ),
                                    right_channel,
                                )
                            )
                        )
                        for magnetics in product(
                            *(magnetic_indices(label) for label in labels)
                        )
                    )
                )
                assert overlap == (1 if left_channel == right_channel else 0)


def test_protected_links_share_exact_pair_outputs_and_dimension_factors() -> None:
    network = cutoff_one_open_index_network()
    assert len(network.core_shared_interfaces) == 9
    channel_census = Counter(
        output
        for interface in network.core_shared_interfaces
        for _residual, _selected, output, _weight in (
            interface.shared_channel_records
        )
    )
    assert channel_census == {0: 36, 1: 36, 2: 9}
    assert all(
        weight == Fraction(1, output + 1)
        for interface in network.core_shared_interfaces
        for _residual, _selected, output, weight in (
            interface.shared_channel_records
        )
    )

    transport = four_fundamental_transport_census()
    assert sorted(count for _matrix, count in transport) == [1, 3, 5]
    assert any(
        matrix
        == (
            (((Fraction(1), 1)), ((Fraction(0), 1))),
            (((Fraction(0), 1)), ((Fraction(1), 1))),
        )
        and count == 1
        for matrix, count in transport
    )
    assert any(
        value == (Fraction(1, 2), 3)
        for matrix, _count in transport
        for row in matrix
        for value in row
    )


def test_decoration_gluing_is_selected_pair_output_equals_residual_label() -> None:
    network = cutoff_one_open_index_network()
    assert len(network.decoration_shared_interfaces) == 9
    assert all(
        residual in fusion_labels(*selected)
        and weight == Fraction(1, residual + 1)
        and phase.square == 1
        for interface in network.decoration_shared_interfaces
        for selected, residual, weight, phase in interface.channel_records
    )
    assert all(
        len(interface.channel_records) == 4
        for interface in network.decoration_shared_interfaces
    )


def test_duality_and_global_operator_claims_are_fail_closed() -> None:
    network = cutoff_one_open_index_network()
    for magnetic in magnetic_indices(1):
        square = sum(
            duality_coefficient(1, magnetic, middle)
            * duality_coefficient(1, middle, magnetic)
            for middle in magnetic_indices(1)
        )
        assert square == -1
    assert network.fundamental_frobenius_schur_indicator == -1
    assert network.rank_one_haar_kraus_factorization_pinned
    assert network.open_boundary_cg_isometries_pinned
    assert network.shared_channel_dimension_factors_pinned
    assert network.signed_f_r_transport_pinned_at_cutoff_one
    assert not network.flat_global_path_table_materialized
    assert not network.physical_source_indexed_choi_contracted
    assert not network.cp_order_domination_proved
