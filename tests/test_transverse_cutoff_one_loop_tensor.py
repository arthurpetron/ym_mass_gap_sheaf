"""Exact gates for the compact BF4 cutoff-one partial Haar tensors."""

from fractions import Fraction

from computations.grouped_all_label_haar_refresh import (
    _corridor_face_ids,
    transverse_cutoff_one_fusion_audit,
)
from computations.transverse_cutoff_one_loop_tensor import (
    CONNECTED_CORE_FACE_IDS,
    CORRIDOR_FACE_IDS,
    canonical_trace_word,
    cutoff_one_core_geometry,
    cutoff_one_loop_tensor_audit,
    free_reduce_trace_word,
    fundamental_partial_loop_tensor,
    loop_tensor_matches_direct,
)


def test_pinned_geometry_agrees_with_the_prior_fusion_audit() -> None:
    geometry = cutoff_one_core_geometry()
    fusion = transverse_cutoff_one_fusion_audit()
    assert geometry.validates()
    assert CONNECTED_CORE_FACE_IDS == fusion.connected_core_faces
    assert CORRIDOR_FACE_IDS == _corridor_face_ids()


def test_trace_word_reduction_and_canonicalization() -> None:
    assert free_reduce_trace_word(((7, 1), (7, -1))) == ()
    assert free_reduce_trace_word(
        ((7, 1), (8, 1), (8, -1), (7, -1))
    ) == ()
    word = ((11, 1), (7, -1), (8, 1))
    inverse = tuple((link, -orientation) for link, orientation in reversed(word))
    assert canonical_trace_word(word) == canonical_trace_word(inverse)
    assert canonical_trace_word(word) == canonical_trace_word(word[1:] + word[:1])


def test_all_admissible_assignments_have_compact_coherent_tensors() -> None:
    audit = cutoff_one_loop_tensor_audit()
    assert audit.validates()
    assert audit.admissible_tensor_count == 1024
    assert audit.distinct_compact_trace_record_count == 1024
    assert audit.coefficient_census == (
        (Fraction(1, 32), 192),
        (Fraction(1, 16), 448),
        (Fraction(1, 8), 192),
        (Fraction(1, 4), 128),
        (Fraction(1), 64),
    )
    assert audit.boundary_loop_count_census == (
        (0, 1),
        (1, 20),
        (2, 100),
        (3, 236),
        (4, 310),
        (5, 236),
        (6, 100),
        (7, 20),
        (8, 1),
    )
    assert audit.maximum_trace_word_length == 7
    assert audit.every_assignment_orientable
    assert audit.every_tensor_uses_only_protected_links
    assert audit.coherent_partial_haar_tensors_constructed
    assert not audit.all_label_completion_proved
    assert not audit.cp_order_domination_proved


def test_distinguished_compact_tensors_match_direct_haar_moments() -> None:
    for face_mask in (0x0, 0x800, 0x1088, 0x7E00, 0x6CFF):
        tensor = fundamental_partial_loop_tensor(face_mask)
        assert tensor.validates()
        assert loop_tensor_matches_direct(face_mask)


def test_maximal_face_tensor_is_still_compact() -> None:
    tensor = fundamental_partial_loop_tensor(0x6CFF)
    assert tensor.active_face_count == 12
    assert tensor.effective_integrations == 5
    assert tensor.coefficient == Fraction(1, 32)
    assert len(tensor.boundary_loops) == 7
    assert max(map(len, tensor.boundary_loops)) == 7
