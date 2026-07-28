"""Joint-channel carrier scout for the binary-multicover counterexample.

The closed-binary-sheet carrier is too small, but the physical outer BF4
kernel retains a coarse face label, one positive pair channel at every
coarse face, and compatible link intertwiners.  This module searches that
larger carrier for the literal seventeen-face cutoff-two Lean witness.

All validation after the search uses exact integer SU(2) fusion rules.  The
result is still only a scout until its displayed certificate is checked in
Lean.
"""

from __future__ import annotations

from dataclasses import dataclass

from computations.dual_half_time_reflection_route import (
    boundary_complete_slab_plaquettes,
)
from computations.dual_positivity_geometry_bridge import (
    Link4,
    Plaquette4,
)
from computations.exact_haar_network import (
    fusion_labels,
    invariant_multiplicity,
)
from computations.general_cutoff_coherence_scout import (
    dyadic_face_preimages,
    slab_link_incidence,
)

PairChannel = tuple[tuple[int, int], int]


NORMALITY_COUNTER_SUPPORT: tuple[Plaquette4, ...] = (
    ((0, 0, 0, 0), (0, 1)),
    ((0, 0, 0, 0), (0, 2)),
    ((0, 0, 0, 0), (1, 3)),
    ((0, 0, 0, 0), (2, 3)),
    ((0, 0, 0, 1), (0, 1)),
    ((0, 0, 0, 1), (0, 2)),
    ((0, 0, 1, 0), (0, 1)),
    ((0, 0, 1, 0), (1, 3)),
    ((0, 0, 1, 1), (0, 1)),
    ((0, 1, 0, 0), (0, 2)),
    ((0, 1, 0, 0), (2, 3)),
    ((0, 1, 0, 1), (0, 2)),
    ((1, 0, 0, 0), (1, 2)),
    ((1, 0, 0, 0), (1, 3)),
    ((1, 0, 0, 0), (2, 3)),
    ((1, 0, 1, 0), (1, 3)),
    ((1, 1, 0, 0), (2, 3)),
)


def fine_label(face: Plaquette4) -> int:
    """Twice-spin label of the formal counterexample."""

    return 2 if face in NORMALITY_COUNTER_SUPPORT else 0


def face_packet(coarse_face: Plaquette4) -> tuple[int, int, int, int]:
    """The ordered four-label packet used by the BF4 face kernel."""

    values = tuple(fine_label(face) for face in dyadic_face_preimages(coarse_face))
    if len(values) != 4:
        raise AssertionError("dyadic face packet must have four entries")
    first, second, third, fourth = values
    return first, second, third, fourth


def positive_pair_channels(
    packet: tuple[int, int, int, int],
) -> tuple[PairChannel, ...]:
    """All pair channels with nonzero exact SU(2) fusion coefficient."""

    a, b, c, d = packet
    return tuple(
        ((left, right), final)
        for left in fusion_labels(a, b)
        for right in fusion_labels(c, d)
        for final in fusion_labels(left, right)
    )


@dataclass(frozen=True)
class JointCarrierCertificate:
    """One globally link-admissible coarse target and local face channels."""

    coarse_labels: tuple[tuple[Plaquette4, int], ...]
    face_channels: tuple[tuple[Plaquette4, PairChannel], ...]
    link_multiplicities: tuple[tuple[Link4, int], ...]

    def validates(self) -> bool:
        labels = dict(self.coarse_labels)
        channels = dict(self.face_channels)
        faces = tuple(boundary_complete_slab_plaquettes(1))
        if tuple(labels) != faces or tuple(channels) != faces:
            return False
        if any(label < 0 or label > 8 for label in labels.values()):
            return False
        for face in faces:
            packet = face_packet(face)
            channel = channels[face]
            if channel not in positive_pair_channels(packet):
                return False
            if channel[1] != labels[face]:
                return False
        observed = tuple(
            (
                link,
                invariant_multiplicity(
                    tuple(labels[face] for face in incident)
                ),
            )
            for link, incident in slab_link_incidence(1).items()
        )
        return (
            observed == self.link_multiplicities
            and all(multiplicity > 0 for _, multiplicity in observed)
        )


def _face_domains() -> dict[Plaquette4, tuple[PairChannel, ...]]:
    return {
        face: positive_pair_channels(face_packet(face))
        for face in boundary_complete_slab_plaquettes(1)
    }


def _partial_links_admissible(
    assignment: dict[Plaquette4, PairChannel],
    incidence: dict[Link4, tuple[Plaquette4, ...]],
) -> bool:
    """Reject a link as soon as all its face labels have been assigned."""

    for incident in incidence.values():
        if all(face in assignment for face in incident):
            labels = tuple(assignment[face][1] for face in incident)
            if invariant_multiplicity(labels) == 0:
                return False
    return True


def find_joint_carrier_certificate() -> JointCarrierCertificate:
    """Find a deterministic enlarged-carrier certificate by backtracking."""

    domains = _face_domains()
    incidence = slab_link_incidence(1)
    variable_faces = tuple(
        face
        for face, domain in domains.items()
        if len({channel[1] for channel in domain}) > 1
    )
    fixed: dict[Plaquette4, PairChannel] = {
        face: domain[0]
        for face, domain in domains.items()
        if face not in variable_faces
    }
    final_domains = {
        face: tuple(
            next(channel for channel in domains[face] if channel[1] == final)
            for final in sorted({channel[1] for channel in domains[face]})
        )
        for face in variable_faces
    }

    # Most-constrained variables first makes this tiny for the pinned row.
    ordered = tuple(
        sorted(
            variable_faces,
            key=lambda face: (
                len(final_domains[face]),
                -sum(face in incident for incident in incidence.values()),
                face,
            ),
        )
    )

    def search(
        index: int,
        assignment: dict[Plaquette4, PairChannel],
    ) -> dict[Plaquette4, PairChannel] | None:
        if index == len(ordered):
            return assignment if _partial_links_admissible(assignment, incidence) else None
        face = ordered[index]
        for channel in final_domains[face]:
            following = dict(assignment)
            following[face] = channel
            if _partial_links_admissible(following, incidence):
                found = search(index + 1, following)
                if found is not None:
                    return found
        return None

    assignment = search(0, fixed)
    if assignment is None:
        raise RuntimeError("no joint coarse carrier found")
    faces = tuple(boundary_complete_slab_plaquettes(1))
    coarse_labels = tuple((face, assignment[face][1]) for face in faces)
    face_channels = tuple((face, assignment[face]) for face in faces)
    labels = dict(coarse_labels)
    link_multiplicities = tuple(
        (
            link,
            invariant_multiplicity(
                tuple(labels[face] for face in incident)
            ),
        )
        for link, incident in incidence.items()
    )
    certificate = JointCarrierCertificate(
        coarse_labels,
        face_channels,
        link_multiplicities,
    )
    if not certificate.validates():
        raise AssertionError("joint carrier certificate drifted")
    return certificate


if __name__ == "__main__":
    witness = find_joint_carrier_certificate()
    print("nonzero coarse labels:")
    print(tuple(item for item in witness.coarse_labels if item[1]))
    print("nonvacuum face channels:")
    print(
        tuple(
            item
            for item in witness.face_channels
            if item[1] != ((0, 0), 0)
        )
    )
    print(
        "link multiplicity profile:",
        tuple(
            (multiplicity, sum(value == multiplicity for _, value in witness.link_multiplicities))
            for multiplicity in sorted({value for _, value in witness.link_multiplicities})
        ),
    )
