"""Exact gates for the complete BF4 cutoff-one residual loop tensors."""

from fractions import Fraction

from computations.transverse_cutoff_one_loop_tensor import (
    cutoff_one_core_geometry,
)
from computations.transverse_cutoff_one_residual_tensor import (
    DECORATION_FACE_IDS,
    cutoff_one_decoration_geometry,
    cutoff_one_residual_loop_tensor_audit,
    fundamental_residual_loop_tensor,
    residual_loop_tensor_matches_direct,
)


def test_six_decoration_words_are_exact_disjoint_boundary_factors() -> None:
    geometry = cutoff_one_decoration_geometry()
    assert geometry.validates()
    assert geometry.face_ids == DECORATION_FACE_IDS
    assert geometry.word_length_census == ((1, 3), (2, 3))
    assert len(geometry.protected_links) == 9
    assert set(geometry.protected_links).isdisjoint(
        cutoff_one_core_geometry().protected_links
    )
    assert geometry.link_sets_pairwise_disjoint
    assert geometry.every_link_corridor_protected


def test_all_decorations_append_six_traces_without_new_haar_integrals() -> None:
    tensor = fundamental_residual_loop_tensor(0, 0x3F)
    assert tensor.validates()
    assert tensor.active_face_count == 6
    assert tensor.active_decoration_count == 6
    assert tensor.candidate_internal_pairs == 0
    assert tensor.effective_integrations == 0
    assert tensor.coefficient == Fraction(1)
    assert len(tensor.boundary_loops) == 6
    assert tensor.total_trace_word_length == 9


def test_full_residual_census_is_exact_and_fail_closed() -> None:
    audit = cutoff_one_residual_loop_tensor_audit()
    assert audit.validates()
    assert audit.admissible_core_assignment_count == 1024
    assert audit.decoration_profile_count == 64
    assert audit.residual_assignment_count == 65536
    assert audit.distinct_compact_trace_record_count == 65536
    assert audit.coefficient_census == (
        (Fraction(1, 32), 12288),
        (Fraction(1, 16), 28672),
        (Fraction(1, 8), 12288),
        (Fraction(1, 4), 8192),
        (Fraction(1), 4096),
    )
    assert audit.maximum_active_face_count == 18
    assert audit.maximum_boundary_loop_count == 14
    assert audit.maximum_trace_word_length == 7
    assert audit.maximum_total_trace_word_length == 27
    assert audit.decoration_tensor_factorization_proved_at_cutoff_one
    assert audit.coherent_residual_haar_tensors_constructed
    assert not audit.all_label_completion_proved
    assert not audit.cp_order_domination_proved


def test_distinguished_residual_tensors_match_direct_haar_moments() -> None:
    for core_mask, decoration_mask in (
        (0, 0),
        (0, 0x3F),
        (0x800, 0x15),
        (0x1088, 0x3F),
    ):
        tensor = fundamental_residual_loop_tensor(
            core_mask,
            decoration_mask,
        )
        assert tensor.validates()
        assert residual_loop_tensor_matches_direct(
            core_mask,
            decoration_mask,
        )


def test_maximal_compact_residual_record_stays_small() -> None:
    tensor = fundamental_residual_loop_tensor(0x1EFF, 0x3F)
    assert tensor.validates()
    assert tensor.active_face_count == 18
    assert tensor.active_decoration_count == 6
    assert tensor.coefficient == Fraction(1, 16)
    assert len(tensor.boundary_loops) == 14
    assert max(map(len, tensor.boundary_loops)) == 6
    assert tensor.total_trace_word_length == 27
