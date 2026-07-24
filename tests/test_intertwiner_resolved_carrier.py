"""Regression pins for the BF1.5 intertwiner-resolved carrier."""

from fractions import Fraction

from computations.intertwiner_resolved_carrier import (
    IntertwinerResolvedFamily,
    fundamental_exchange_phase,
    sequential_fusion_paths,
    triple_fundamental_f_matrix,
    triple_recoupling_audit,
)
from computations.three_strand_corrected_slab import minimal_three_strand_family
from computations.wigner_6j import QuadRadical


def test_three_fundamentals_retain_both_multiplicity_paths() -> None:
    left = sequential_fusion_paths((1, 1, 1), association="left")
    right = sequential_fusion_paths((1, 1, 1), association="right")

    assert tuple((path.output, path.intermediates) for path in left) == (
        (1, (0, 1)),
        (1, (2, 1)),
        (3, (2, 3)),
    )
    assert tuple(path.output for path in right) == (1, 1, 3)


def test_resolved_paths_forget_exactly_to_the_fusion_ledger() -> None:
    resolved = IntertwinerResolvedFamily.build(minimal_three_strand_family())
    assert resolved.fusion_path_count == 96
    assert len(resolved.path_ledger()) == 64
    assert sum(resolved.path_ledger().values()) == 96

    dimensions = resolved.edge_invariant_dimensions
    assert dimensions.count(2) == 11
    assert dimensions.count(5) == 4
    assert dimensions.count(1) == 101


def test_signed_f_and_r_data_are_exactly_unitary() -> None:
    root_three = QuadRadical(Fraction(1, 2), 3)
    assert triple_fundamental_f_matrix(1) == (
        (QuadRadical(Fraction(-1, 2), 1), root_three),
        (root_three, QuadRadical(Fraction(1, 2), 1)),
    )
    assert triple_fundamental_f_matrix(3) == (
        (QuadRadical(Fraction(1), 1),),
    )
    assert fundamental_exchange_phase(0) == -1
    assert fundamental_exchange_phase(2) == 1
    assert triple_recoupling_audit().validates()
