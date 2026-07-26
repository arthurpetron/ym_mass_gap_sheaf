"""Compact coherent Haar tensors for the BF4 cutoff-one transverse core.

The 15-face connected residual from the grouped-corridor audit has only five
unprotected free Haar links.  At representation cutoff one, every internally
admissible face assignment meets each such link in either zero or two
fundamental strands.  All 1024 assignments admit compatible face
orientations, so the two-strand Haar identity can be applied without a signed
or frustrated pairing:

    integral chi_1(U A) chi_1(U^-1 B) dU = (1/2) chi_1(A B).

When both occurrences lie in one trace, the same identity splits that trace
into two.  Repeating it produces an exact compact product of boundary Wilson
traces.  This avoids the coordinate-polynomial blow-up of multiplying all 15
heat factors at once while preserving the coherent boundary words.

The result is still cutoff one.  It does not prove all-label completion,
complete-positive corridor domination, or a physical transfer gap.
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

OrientedStep = tuple[int, int]
TraceWord = tuple[OrientedStep, ...]

CONNECTED_CORE_FACE_IDS = (
    9,
    11,
    13,
    15,
    19,
    20,
    23,
    25,
    29,
    39,
    40,
    41,
    44,
    49,
    59,
)

CORRIDOR_FACE_IDS = (
    (0, 18, 36, 54),
    (1, 10, 37, 46),
    (3, 12, 21, 30),
    (6, 24, 42, 60),
    (7, 16, 43, 52),
    (8, 17, 26, 35),
    (2, 38),
    (4, 22),
    (5, 14),
)


@dataclass(frozen=True)
class CutoffOneCoreGeometry:
    """Pinned free-link words and incidence of the connected 15-face core."""

    complex: GaugeFixedComplex
    full_face_paths: tuple[TraceWord, ...]
    face_words: tuple[TraceWord, ...]
    protected_links: tuple[int, ...]
    internal_links: tuple[int, ...]
    internal_incidence: tuple[
        tuple[int, tuple[tuple[int, int], ...]],
        ...,
    ]

    def validates(self) -> bool:
        return (
            len(self.full_face_paths) == len(self.face_words) == 15
            and self.protected_links == (7, 8, 11, 12, 19, 23, 25, 53, 54)
            and self.internal_links == (26, 30, 56, 60, 73)
            and tuple(
                (link, tuple(orientation for _position, orientation in incident))
                for link, incident in self.internal_incidence
            )
            == (
                (26, (-1, -1, 1)),
                (30, (-1, -1, -1)),
                (56, (1, -1, 1)),
                (60, (1, -1, -1)),
                (73, (1, 1, -1)),
            )
            and all(len(incident) == 3 for _link, incident in self.internal_incidence)
        )


@cache
def cutoff_one_core_geometry() -> CutoffOneCoreGeometry:
    """Construct the pinned connected-core words after maximal-tree gauge fixing."""

    complex_, faces, _plaquettes = corrected_slab_haar_complex(1)
    free_links = set(complex_.free)
    selected_faces = {
        face_id
        for corridor in CORRIDOR_FACE_IDS
        for face_id in corridor
    }
    protected_links = {
        link
        for face_id in selected_faces
        for link, _orientation in faces[face_id]
        if link in free_links
    }
    face_words = tuple(
        tuple(
            (link, orientation)
            for link, orientation in faces[face_id]
            if link in free_links
        )
        for face_id in CONNECTED_CORE_FACE_IDS
    )
    used_links = {
        link
        for word in face_words
        for link, _orientation in word
    }
    internal_links = tuple(sorted(used_links - protected_links))
    internal_incidence = tuple(
        (
            link,
            tuple(
                (position, orientation)
                for position, word in enumerate(face_words)
                for word_link, orientation in word
                if word_link == link
            ),
        )
        for link in internal_links
    )
    geometry = CutoffOneCoreGeometry(
        complex=complex_,
        full_face_paths=tuple(
            tuple(faces[face_id])
            for face_id in CONNECTED_CORE_FACE_IDS
        ),
        face_words=face_words,
        protected_links=tuple(sorted(used_links & protected_links)),
        internal_links=internal_links,
        internal_incidence=internal_incidence,
    )
    if not geometry.validates():
        raise AssertionError("the cutoff-one loop-tensor geometry drifted")
    return geometry


def free_reduce_trace_word(word: TraceWord) -> TraceWord:
    """Cancel adjacent inverse letters, including across the cyclic boundary."""

    reduced = list(word)
    while reduced:
        changed = False
        linear: list[OrientedStep] = []
        for step in reduced:
            if (
                linear
                and linear[-1][0] == step[0]
                and linear[-1][1] == -step[1]
            ):
                linear.pop()
                changed = True
            else:
                linear.append(step)
        reduced = linear
        if (
            len(reduced) >= 2
            and reduced[0][0] == reduced[-1][0]
            and reduced[0][1] == -reduced[-1][1]
        ):
            reduced = reduced[1:-1]
            changed = True
        if not changed:
            break
    return tuple(reduced)


def canonical_trace_word(word: TraceWord) -> TraceWord:
    """Canonicalize using trace cyclicity and ``chi_1(g) = chi_1(g^-1)``."""

    reduced = free_reduce_trace_word(word)
    if not reduced:
        return ()
    inverse = tuple((link, -orientation) for link, orientation in reversed(reduced))
    candidates = tuple(
        candidate[index:] + candidate[:index]
        for candidate in (reduced, inverse)
        for index in range(len(candidate))
    )
    return min(candidates)


def _active_internal_pairs(
    face_mask: int,
    geometry: CutoffOneCoreGeometry,
) -> tuple[tuple[int, int, int, int], ...]:
    """Return ``(link, left, right, flip_product)`` for active internal pairs."""

    if face_mask < 0 or face_mask >> len(geometry.face_words):
        raise ValueError("the face mask leaves the connected transverse core")
    pairs: list[tuple[int, int, int, int]] = []
    for link, incident in geometry.internal_incidence:
        active = tuple(
            (position, orientation)
            for position, orientation in incident
            if (face_mask >> position) & 1
        )
        if len(active) not in (0, 2):
            raise ValueError("the cutoff-one assignment is not internally admissible")
        if len(active) == 2:
            (left, left_orientation), (right, right_orientation) = active
            pairs.append(
                (
                    link,
                    left,
                    right,
                    -left_orientation * right_orientation,
                )
            )
    return tuple(pairs)


def _orientation_flips(
    face_mask: int,
    geometry: CutoffOneCoreGeometry,
    pairs: tuple[tuple[int, int, int, int], ...],
) -> tuple[int, ...]:
    """Solve the face-orientation constraints on every active component."""

    active_faces = tuple(
        position
        for position in range(len(geometry.face_words))
        if (face_mask >> position) & 1
    )
    flips: dict[int, int] = {}
    for root in active_faces:
        if root in flips:
            continue
        flips[root] = 1
        stack = [root]
        while stack:
            face = stack.pop()
            for _link, left, right, required_product in pairs:
                if left == face:
                    neighbor = right
                elif right == face:
                    neighbor = left
                else:
                    continue
                required = required_product * flips[face]
                existing = flips.get(neighbor)
                if existing is not None and existing != required:
                    raise ValueError("the active transverse surface is non-orientable")
                if existing is None:
                    flips[neighbor] = required
                    stack.append(neighbor)
    return tuple(
        flips.get(position, 0)
        for position in range(len(geometry.face_words))
    )


def _oriented_face_word(word: TraceWord, flip: int) -> TraceWord:
    """Apply one whole-face orientation flip."""

    if flip not in (-1, 1):
        raise ValueError("an active face orientation must be +1 or -1")
    if flip == 1:
        return word
    return tuple((link, -orientation) for link, orientation in reversed(word))


def _normalize_loop_family(
    loops: list[TraceWord],
) -> tuple[list[TraceWord], int]:
    """Free-reduce loops and count empty traces ``Tr(I) = 2``."""

    normalized: list[TraceWord] = []
    vacuum_loops = 0
    for loop in loops:
        reduced = free_reduce_trace_word(loop)
        if reduced:
            normalized.append(reduced)
        else:
            vacuum_loops += 1
    return normalized, vacuum_loops


@dataclass(frozen=True)
class FundamentalPartialLoopTensor:
    """One exact coherent partial Haar tensor in a compact trace-word basis."""

    face_mask: int
    active_face_count: int
    candidate_internal_pairs: int
    effective_integrations: int
    cancelled_internal_pairs: int
    vacuum_trace_loops: int
    coefficient: Fraction
    boundary_loops: tuple[TraceWord, ...]
    all_orientation_constraints_solved: bool

    def validates(self) -> bool:
        geometry = cutoff_one_core_geometry()
        if self.face_mask < 0 or self.face_mask >> len(geometry.face_words):
            return False
        try:
            pairs = _active_internal_pairs(self.face_mask, geometry)
        except ValueError:
            return False
        protected = set(geometry.protected_links)
        return (
            self.active_face_count == self.face_mask.bit_count()
            and self.candidate_internal_pairs == len(pairs)
            and self.effective_integrations + self.cancelled_internal_pairs
            == self.candidate_internal_pairs
            and self.coefficient
            == Fraction(
                2**self.vacuum_trace_loops,
                2**self.effective_integrations,
            )
            and self.coefficient > 0
            and all(self.boundary_loops)
            and self.boundary_loops
            == tuple(sorted(map(canonical_trace_word, self.boundary_loops)))
            and all(
                link in protected
                for loop in self.boundary_loops
                for link, _orientation in loop
            )
            and self.all_orientation_constraints_solved
        )


@cache
def fundamental_partial_loop_tensor(
    face_mask: int,
) -> FundamentalPartialLoopTensor:
    """Contract one admissible core assignment by exact two-strand Haar gluing."""

    geometry = cutoff_one_core_geometry()
    pairs = _active_internal_pairs(face_mask, geometry)
    flips = _orientation_flips(face_mask, geometry, pairs)
    loops = [
        _oriented_face_word(geometry.face_words[position], flips[position])
        for position in range(len(geometry.face_words))
        if (face_mask >> position) & 1
    ]
    loops, initial_vacuum = _normalize_loop_family(loops)
    coefficient = Fraction(2**initial_vacuum)
    effective_integrations = 0
    vacuum_trace_loops = initial_vacuum

    for link, _left, _right, _required_product in pairs:
        occurrences = tuple(
            (loop_index, step_index, orientation)
            for loop_index, loop in enumerate(loops)
            for step_index, (word_link, orientation) in enumerate(loop)
            if word_link == link
        )
        if not occurrences:
            # A prior gluing made the pair adjacent as U U^-1, so the word
            # reduced before this Haar variable was reached.
            continue
        if (
            len(occurrences) != 2
            or {orientation for _loop, _step, orientation in occurrences}
            != {-1, 1}
        ):
            raise AssertionError("an oriented internal Haar pair drifted")

        plus = next(item for item in occurrences if item[2] == 1)
        minus = next(item for item in occurrences if item[2] == -1)
        coefficient /= 2
        effective_integrations += 1

        if plus[0] != minus[0]:
            plus_loop = loops[plus[0]]
            minus_loop = loops[minus[0]]
            plus_rest = plus_loop[plus[1] + 1 :] + plus_loop[: plus[1]]
            minus_rest = minus_loop[minus[1] + 1 :] + minus_loop[: minus[1]]
            for loop_index in sorted((plus[0], minus[0]), reverse=True):
                loops.pop(loop_index)
            loops.append(plus_rest + minus_rest)
        else:
            loop_index = plus[0]
            loop = loops[loop_index]
            rotated = loop[plus[1] :] + loop[: plus[1]]
            minus_index = next(
                index
                for index, step in enumerate(rotated)
                if index and step == (link, -1)
            )
            loops.pop(loop_index)
            loops.extend(
                (
                    rotated[1:minus_index],
                    rotated[minus_index + 1 :],
                )
            )

        loops, new_vacuum = _normalize_loop_family(loops)
        coefficient *= 2**new_vacuum
        vacuum_trace_loops += new_vacuum

    tensor = FundamentalPartialLoopTensor(
        face_mask=face_mask,
        active_face_count=face_mask.bit_count(),
        candidate_internal_pairs=len(pairs),
        effective_integrations=effective_integrations,
        cancelled_internal_pairs=len(pairs) - effective_integrations,
        vacuum_trace_loops=vacuum_trace_loops,
        coefficient=coefficient,
        boundary_loops=tuple(sorted(canonical_trace_word(loop) for loop in loops)),
        all_orientation_constraints_solved=True,
    )
    if not tensor.validates():
        raise AssertionError("the fundamental partial loop tensor drifted")
    return tensor


def loop_tensor_polynomial(tensor: FundamentalPartialLoopTensor) -> Poly:
    """Expand one compact loop tensor into the exact quaternion polynomial."""

    if not tensor.validates():
        raise ValueError("an invalid compact loop tensor cannot be expanded")
    polynomial = p_const({0: tensor.coefficient})
    for loop in tensor.boundary_loops:
        polynomial = p_mul(polynomial, chi(1, holonomy(loop)))
    return polynomial


def direct_partial_polynomial(face_mask: int) -> Poly:
    """Directly integrate the same assignment in quaternion coordinates."""

    geometry = cutoff_one_core_geometry()
    _active_internal_pairs(face_mask, geometry)
    factors = tuple(
        chi(1, geometry.complex.holonomy_of(geometry.full_face_paths[position]))
        for position in range(len(geometry.face_words))
        if (face_mask >> position) & 1
    )
    return contract_pairing_aware(factors, geometry.internal_links)


def loop_tensor_matches_direct(face_mask: int) -> bool:
    """Independently compare compact gluing with exact coordinate Haar moments."""

    tensor = fundamental_partial_loop_tensor(face_mask)
    return bool(
        p_equal_on_group(
            loop_tensor_polynomial(tensor),
            direct_partial_polynomial(face_mask),
        )
    )


@dataclass(frozen=True)
class CutoffOneLoopTensorAudit:
    """Complete compact-tensor census over every admissible core assignment."""

    admissible_tensor_count: int
    distinct_compact_trace_record_count: int
    face_count_census: tuple[tuple[int, int], ...]
    coefficient_census: tuple[tuple[Fraction, int], ...]
    effective_integration_census: tuple[tuple[int, int], ...]
    boundary_loop_count_census: tuple[tuple[int, int], ...]
    maximum_trace_word_length: int
    every_assignment_orientable: bool
    every_tensor_uses_only_protected_links: bool
    coherent_partial_haar_tensors_constructed: bool
    all_label_completion_proved: bool
    cp_order_domination_proved: bool
    first_open_obligation: str

    def validates(self) -> bool:
        return (
            self.admissible_tensor_count == 1024
            and self.distinct_compact_trace_record_count == 1024
            and self.face_count_census
            == (
                (0, 1),
                (1, 6),
                (2, 15),
                (3, 22),
                (4, 30),
                (5, 60),
                (6, 126),
                (7, 204),
                (8, 237),
                (9, 190),
                (10, 99),
                (11, 30),
                (12, 4),
            )
            and self.coefficient_census
            == (
                (Fraction(1, 32), 192),
                (Fraction(1, 16), 448),
                (Fraction(1, 8), 192),
                (Fraction(1, 4), 128),
                (Fraction(1), 64),
            )
            and self.effective_integration_census
            == ((0, 64), (2, 128), (3, 192), (4, 448), (5, 192))
            and self.boundary_loop_count_census
            == (
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
            and self.maximum_trace_word_length == 7
            and self.every_assignment_orientable
            and self.every_tensor_uses_only_protected_links
            and self.coherent_partial_haar_tensors_constructed
            and not self.all_label_completion_proved
            and not self.cp_order_domination_proved
            and self.first_open_obligation
            == "evaluate-open-index-all-label-haar-amplitudes"
        )


@cache
def cutoff_one_loop_tensor_audit() -> CutoffOneLoopTensorAudit:
    """Construct and census all 1024 compact coherent partial tensors."""

    geometry = cutoff_one_core_geometry()
    tensors: list[FundamentalPartialLoopTensor] = []
    for face_mask in range(1 << len(geometry.face_words)):
        try:
            tensor = fundamental_partial_loop_tensor(face_mask)
        except ValueError:
            continue
        tensors.append(tensor)

    protected = set(geometry.protected_links)
    audit = CutoffOneLoopTensorAudit(
        admissible_tensor_count=len(tensors),
        distinct_compact_trace_record_count=len(
            {
                (tensor.coefficient, tensor.boundary_loops)
                for tensor in tensors
            }
        ),
        face_count_census=tuple(
            sorted(Counter(tensor.active_face_count for tensor in tensors).items())
        ),
        coefficient_census=tuple(
            sorted(Counter(tensor.coefficient for tensor in tensors).items())
        ),
        effective_integration_census=tuple(
            sorted(
                Counter(
                    tensor.effective_integrations
                    for tensor in tensors
                ).items()
            )
        ),
        boundary_loop_count_census=tuple(
            sorted(Counter(len(tensor.boundary_loops) for tensor in tensors).items())
        ),
        maximum_trace_word_length=max(
            (
                len(loop)
                for tensor in tensors
                for loop in tensor.boundary_loops
            ),
            default=0,
        ),
        every_assignment_orientable=all(
            tensor.all_orientation_constraints_solved
            for tensor in tensors
        ),
        every_tensor_uses_only_protected_links=all(
            link in protected
            for tensor in tensors
            for loop in tensor.boundary_loops
            for link, _orientation in loop
        ),
        coherent_partial_haar_tensors_constructed=True,
        all_label_completion_proved=False,
        cp_order_domination_proved=False,
        first_open_obligation=(
            "evaluate-open-index-all-label-haar-amplitudes"
        ),
    )
    if not audit.validates():
        raise AssertionError("the complete cutoff-one loop-tensor census drifted")
    return audit
