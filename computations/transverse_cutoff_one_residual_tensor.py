"""Coherent cutoff-one Haar tensors for the full BF4 21-face residual.

The connected 15-face component is contracted by
``transverse_cutoff_one_loop_tensor``.  The six remaining residual faces are
one-face decorations.  After maximal-tree gauge fixing, they carry three
one-letter and three two-letter Wilson words on nine corridor-protected
links.  Those links are pairwise disjoint and are disjoint from the nine
protected links of the connected core.

Consequently the complete cutoff-one residual tensor is an exact tensor
product: choose one of the 1024 admissible core fillings and independently
choose any subset of the six decorations.  Each active decoration appends
one boundary Wilson trace and introduces no additional Haar integration.
This gives 65536 distinct compact assignment records.

This is a cutoff-one contraction only.  It does not prove an all-label
completion, complete-positive corridor domination, or a physical gap.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from functools import cache

from computations.corrected_slab_haar_network import corrected_slab_haar_complex
from computations.exact_haar_network import (
    GaugeFixedComplex,
    Poly,
    chi,
    contract_pairing_aware,
    holonomy,
    p_const,
    p_equal_on_group,
    p_mul,
)
from computations.transverse_cutoff_one_loop_tensor import (
    CORRIDOR_FACE_IDS,
    TraceWord,
    canonical_trace_word,
    cutoff_one_core_geometry,
    fundamental_partial_loop_tensor,
)

DECORATION_FACE_IDS = (31, 32, 47, 50, 56, 58)


@dataclass(frozen=True)
class CutoffOneDecorationGeometry:
    """Pinned gauge-fixed words of the six isolated residual faces."""

    complex: GaugeFixedComplex
    face_ids: tuple[int, ...]
    full_face_paths: tuple[TraceWord, ...]
    face_words: tuple[TraceWord, ...]
    protected_links: tuple[int, ...]
    word_length_census: tuple[tuple[int, int], ...]
    link_sets_pairwise_disjoint: bool
    disjoint_from_core_boundary: bool
    every_link_corridor_protected: bool

    def validates(self) -> bool:
        return (
            self.face_ids == DECORATION_FACE_IDS
            and self.face_words
            == (
                ((27, 1), (31, -1)),
                ((32, -1),),
                ((55, 1), (59, -1)),
                ((61, -1),),
                ((67, 1), (71, -1)),
                ((72, -1),),
            )
            and self.protected_links
            == (27, 31, 32, 55, 59, 61, 67, 71, 72)
            and self.word_length_census == ((1, 3), (2, 3))
            and self.link_sets_pairwise_disjoint
            and self.disjoint_from_core_boundary
            and self.every_link_corridor_protected
        )


@cache
def cutoff_one_decoration_geometry() -> CutoffOneDecorationGeometry:
    """Construct the isolated decoration words after maximal-tree fixing."""

    complex_, faces, _plaquettes = corrected_slab_haar_complex(1)
    free_links = set(complex_.free)
    face_words = tuple(
        tuple(
            (link, orientation)
            for link, orientation in faces[face_id]
            if link in free_links
        )
        for face_id in DECORATION_FACE_IDS
    )
    link_sets = tuple(
        {link for link, _orientation in word}
        for word in face_words
    )
    all_links = set().union(*link_sets)
    corridor_faces = {
        face_id
        for corridor in CORRIDOR_FACE_IDS
        for face_id in corridor
    }
    corridor_protected = {
        link
        for face_id in corridor_faces
        for link, _orientation in faces[face_id]
        if link in free_links
    }
    core_protected = set(cutoff_one_core_geometry().protected_links)
    geometry = CutoffOneDecorationGeometry(
        complex=complex_,
        face_ids=DECORATION_FACE_IDS,
        full_face_paths=tuple(
            tuple(faces[face_id])
            for face_id in DECORATION_FACE_IDS
        ),
        face_words=face_words,
        protected_links=tuple(sorted(all_links)),
        word_length_census=tuple(
            sorted(Counter(map(len, face_words)).items())
        ),
        link_sets_pairwise_disjoint=(
            len(all_links) == sum(map(len, link_sets))
        ),
        disjoint_from_core_boundary=all_links.isdisjoint(core_protected),
        every_link_corridor_protected=all_links <= corridor_protected,
    )
    if not geometry.validates():
        raise AssertionError("the cutoff-one decoration geometry drifted")
    return geometry


def _active_decoration_loops(decoration_mask: int) -> tuple[TraceWord, ...]:
    """Return canonical boundary traces for one six-bit decoration mask."""

    geometry = cutoff_one_decoration_geometry()
    if decoration_mask < 0 or decoration_mask >> len(geometry.face_words):
        raise ValueError("the decoration mask leaves the six-face residual")
    return tuple(
        canonical_trace_word(geometry.face_words[position])
        for position in range(len(geometry.face_words))
        if (decoration_mask >> position) & 1
    )


@dataclass(frozen=True)
class FundamentalResidualLoopTensor:
    """One exact coherent tensor for a cutoff-one 21-face assignment."""

    core_face_mask: int
    decoration_mask: int
    active_face_count: int
    active_decoration_count: int
    candidate_internal_pairs: int
    effective_integrations: int
    cancelled_internal_pairs: int
    vacuum_trace_loops: int
    coefficient: Fraction
    boundary_loops: tuple[TraceWord, ...]
    total_trace_word_length: int
    decoration_tensor_factorization_used: bool

    def validates(self) -> bool:
        try:
            core_tensor = fundamental_partial_loop_tensor(self.core_face_mask)
            decoration_loops = _active_decoration_loops(self.decoration_mask)
        except ValueError:
            return False
        all_protected = (
            set(cutoff_one_core_geometry().protected_links)
            | set(cutoff_one_decoration_geometry().protected_links)
        )
        expected_loops = tuple(
            sorted(core_tensor.boundary_loops + decoration_loops)
        )
        return (
            self.active_decoration_count == self.decoration_mask.bit_count()
            and self.active_face_count
            == core_tensor.active_face_count + self.active_decoration_count
            and self.candidate_internal_pairs
            == core_tensor.candidate_internal_pairs
            and self.effective_integrations
            == core_tensor.effective_integrations
            and self.cancelled_internal_pairs
            == core_tensor.cancelled_internal_pairs
            and self.vacuum_trace_loops == core_tensor.vacuum_trace_loops
            and self.coefficient == core_tensor.coefficient
            and self.boundary_loops == expected_loops
            and self.total_trace_word_length
            == sum(map(len, self.boundary_loops))
            and all(
                link in all_protected
                for loop in self.boundary_loops
                for link, _orientation in loop
            )
            and self.decoration_tensor_factorization_used
        )


def fundamental_residual_loop_tensor(
    core_face_mask: int,
    decoration_mask: int,
) -> FundamentalResidualLoopTensor:
    """Append the selected decoration traces to one coherent core tensor."""

    core_tensor = fundamental_partial_loop_tensor(core_face_mask)
    decoration_loops = _active_decoration_loops(decoration_mask)
    boundary_loops = tuple(
        sorted(core_tensor.boundary_loops + decoration_loops)
    )
    tensor = FundamentalResidualLoopTensor(
        core_face_mask=core_face_mask,
        decoration_mask=decoration_mask,
        active_face_count=(
            core_tensor.active_face_count + decoration_mask.bit_count()
        ),
        active_decoration_count=decoration_mask.bit_count(),
        candidate_internal_pairs=core_tensor.candidate_internal_pairs,
        effective_integrations=core_tensor.effective_integrations,
        cancelled_internal_pairs=core_tensor.cancelled_internal_pairs,
        vacuum_trace_loops=core_tensor.vacuum_trace_loops,
        coefficient=core_tensor.coefficient,
        boundary_loops=boundary_loops,
        total_trace_word_length=sum(map(len, boundary_loops)),
        decoration_tensor_factorization_used=True,
    )
    if not tensor.validates():
        raise AssertionError("the cutoff-one residual loop tensor drifted")
    return tensor


def residual_loop_tensor_polynomial(
    tensor: FundamentalResidualLoopTensor,
) -> Poly:
    """Expand one compact residual tensor in exact quaternion coordinates."""

    if not tensor.validates():
        raise ValueError("an invalid residual loop tensor cannot be expanded")
    polynomial = p_const({0: tensor.coefficient})
    for loop in tensor.boundary_loops:
        polynomial = p_mul(polynomial, chi(1, holonomy(loop)))
    return polynomial


def direct_residual_polynomial(
    core_face_mask: int,
    decoration_mask: int,
) -> Poly:
    """Directly evaluate the same 21-face assignment before compact gluing."""

    core_geometry = cutoff_one_core_geometry()
    decoration_geometry = cutoff_one_decoration_geometry()
    fundamental_partial_loop_tensor(core_face_mask)
    _active_decoration_loops(decoration_mask)
    factors = tuple(
        chi(
            1,
            core_geometry.complex.holonomy_of(
                core_geometry.full_face_paths[position]
            ),
        )
        for position in range(len(core_geometry.face_words))
        if (core_face_mask >> position) & 1
    ) + tuple(
        chi(
            1,
            decoration_geometry.complex.holonomy_of(
                decoration_geometry.full_face_paths[position]
            ),
        )
        for position in range(len(decoration_geometry.face_words))
        if (decoration_mask >> position) & 1
    )
    return contract_pairing_aware(factors, core_geometry.internal_links)


def residual_loop_tensor_matches_direct(
    core_face_mask: int,
    decoration_mask: int,
) -> bool:
    """Compare compact factorization with independent exact Haar moments."""

    tensor = fundamental_residual_loop_tensor(
        core_face_mask,
        decoration_mask,
    )
    return bool(
        p_equal_on_group(
            residual_loop_tensor_polynomial(tensor),
            direct_residual_polynomial(core_face_mask, decoration_mask),
        )
    )


@dataclass(frozen=True)
class CutoffOneResidualLoopTensorAudit:
    """Complete compact-tensor census of the cutoff-one 21-face residual."""

    admissible_core_assignment_count: int
    decoration_profile_count: int
    residual_assignment_count: int
    distinct_compact_trace_record_count: int
    face_count_census: tuple[tuple[int, int], ...]
    coefficient_census: tuple[tuple[Fraction, int], ...]
    effective_integration_census: tuple[tuple[int, int], ...]
    boundary_loop_count_census: tuple[tuple[int, int], ...]
    total_trace_word_length_census: tuple[tuple[int, int], ...]
    maximum_active_face_count: int
    maximum_boundary_loop_count: int
    maximum_trace_word_length: int
    maximum_total_trace_word_length: int
    every_record_uses_only_eighteen_protected_links: bool
    decoration_tensor_factorization_proved_at_cutoff_one: bool
    coherent_residual_haar_tensors_constructed: bool
    all_label_completion_proved: bool
    cp_order_domination_proved: bool
    first_open_obligation: str

    def validates(self) -> bool:
        return (
            self.admissible_core_assignment_count == 1024
            and self.decoration_profile_count == 64
            and self.residual_assignment_count == 65536
            and self.distinct_compact_trace_record_count == 65536
            and self.face_count_census
            == (
                (0, 1),
                (1, 12),
                (2, 66),
                (3, 222),
                (4, 522),
                (5, 966),
                (6, 1638),
                (7, 2886),
                (8, 5148),
                (9, 8294),
                (10, 11154),
                (11, 12090),
                (12, 10374),
                (13, 6930),
                (14, 3522),
                (15, 1314),
                (16, 339),
                (17, 54),
                (18, 4),
            )
            and self.coefficient_census
            == (
                (Fraction(1, 32), 12288),
                (Fraction(1, 16), 28672),
                (Fraction(1, 8), 12288),
                (Fraction(1, 4), 8192),
                (Fraction(1), 4096),
            )
            and self.effective_integration_census
            == (
                (0, 4096),
                (2, 8192),
                (3, 12288),
                (4, 28672),
                (5, 12288),
            )
            and self.boundary_loop_count_census
            == (
                (0, 1),
                (1, 26),
                (2, 235),
                (3, 1156),
                (4, 3641),
                (5, 7942),
                (6, 12507),
                (7, 14520),
                (8, 12507),
                (9, 7942),
                (10, 3641),
                (11, 1156),
                (12, 235),
                (13, 26),
                (14, 1),
            )
            and self.total_trace_word_length_census
            == (
                (0, 1),
                (1, 6),
                (2, 22),
                (3, 65),
                (4, 162),
                (5, 356),
                (6, 708),
                (7, 1282),
                (8, 2127),
                (9, 3242),
                (10, 4538),
                (11, 5839),
                (12, 6908),
                (13, 7512),
                (14, 7512),
                (15, 6908),
                (16, 5839),
                (17, 4538),
                (18, 3242),
                (19, 2127),
                (20, 1282),
                (21, 708),
                (22, 356),
                (23, 162),
                (24, 65),
                (25, 22),
                (26, 6),
                (27, 1),
            )
            and self.maximum_active_face_count == 18
            and self.maximum_boundary_loop_count == 14
            and self.maximum_trace_word_length == 7
            and self.maximum_total_trace_word_length == 27
            and self.every_record_uses_only_eighteen_protected_links
            and self.decoration_tensor_factorization_proved_at_cutoff_one
            and self.coherent_residual_haar_tensors_constructed
            and not self.all_label_completion_proved
            and not self.cp_order_domination_proved
            and self.first_open_obligation
            == "evaluate-open-index-all-label-haar-amplitudes"
        )


@cache
def cutoff_one_residual_loop_tensor_audit() -> CutoffOneResidualLoopTensorAudit:
    """Enumerate all 1024 times 64 coherent residual assignment records."""

    records: set[tuple[Fraction, tuple[TraceWord, ...]]] = set()
    face_counts: Counter[int] = Counter()
    coefficients: Counter[Fraction] = Counter()
    effective_integrations: Counter[int] = Counter()
    boundary_loop_counts: Counter[int] = Counter()
    total_word_lengths: Counter[int] = Counter()
    maximum_trace_word_length = 0
    every_record_protected = True
    residual_count = 0
    core_count = 0
    all_protected = (
        set(cutoff_one_core_geometry().protected_links)
        | set(cutoff_one_decoration_geometry().protected_links)
    )

    for core_face_mask in range(1 << 15):
        try:
            fundamental_partial_loop_tensor(core_face_mask)
        except ValueError:
            continue
        core_count += 1
        for decoration_mask in range(1 << len(DECORATION_FACE_IDS)):
            tensor = fundamental_residual_loop_tensor(
                core_face_mask,
                decoration_mask,
            )
            residual_count += 1
            records.add((tensor.coefficient, tensor.boundary_loops))
            face_counts[tensor.active_face_count] += 1
            coefficients[tensor.coefficient] += 1
            effective_integrations[tensor.effective_integrations] += 1
            boundary_loop_counts[len(tensor.boundary_loops)] += 1
            total_word_lengths[tensor.total_trace_word_length] += 1
            maximum_trace_word_length = max(
                maximum_trace_word_length,
                max(map(len, tensor.boundary_loops), default=0),
            )
            every_record_protected = (
                every_record_protected
                and all(
                    link in all_protected
                    for loop in tensor.boundary_loops
                    for link, _orientation in loop
                )
            )

    audit = CutoffOneResidualLoopTensorAudit(
        admissible_core_assignment_count=core_count,
        decoration_profile_count=1 << len(DECORATION_FACE_IDS),
        residual_assignment_count=residual_count,
        distinct_compact_trace_record_count=len(records),
        face_count_census=tuple(sorted(face_counts.items())),
        coefficient_census=tuple(sorted(coefficients.items())),
        effective_integration_census=tuple(
            sorted(effective_integrations.items())
        ),
        boundary_loop_count_census=tuple(
            sorted(boundary_loop_counts.items())
        ),
        total_trace_word_length_census=tuple(
            sorted(total_word_lengths.items())
        ),
        maximum_active_face_count=max(face_counts, default=0),
        maximum_boundary_loop_count=max(boundary_loop_counts, default=0),
        maximum_trace_word_length=maximum_trace_word_length,
        maximum_total_trace_word_length=max(total_word_lengths, default=0),
        every_record_uses_only_eighteen_protected_links=(
            len(all_protected) == 18 and every_record_protected
        ),
        decoration_tensor_factorization_proved_at_cutoff_one=True,
        coherent_residual_haar_tensors_constructed=True,
        all_label_completion_proved=False,
        cp_order_domination_proved=False,
        first_open_obligation=(
            "evaluate-open-index-all-label-haar-amplitudes"
        ),
    )
    if not audit.validates():
        raise AssertionError("the full cutoff-one residual tensor census drifted")
    return audit
