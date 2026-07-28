"""Exact scout for globally coherent all-cutoff coarse face choices.

The most obvious general-cutoff witness chooses, on every coarse face, the
stretched final spin equal to the sum of its four fine preimage spins.  This
is always a positive *local* fusion channel.  It need not be a positive
globally link-glued coarse state.

This module pins the smallest corrected-slab counterexample found by the
exact geometry scout.  A single spin-one (doubled label one) fine unit-cube
boundary is link-admissible.  Its independently stretched dyadic face image
contains one isolated coarse face of label two, whose boundary links have
zero invariant multiplicity.

Consequently all-cutoff coherence must transport the fine intertwiner field
jointly across the block.  Independent positive face-channel choices are not
enough.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations, product

from computations.dual_half_time_reflection_route import (
    boundary_complete_slab_plaquettes,
)
from computations.dual_positivity_geometry_bridge import (
    Link4,
    Plaquette4,
    Vertex4,
    add_e,
    edges_of,
)
from computations.exact_haar_network import invariant_multiplicity

SpinLabelling = dict[Plaquette4, int]


def dyadic_face_preimages(coarse: Plaquette4) -> tuple[Plaquette4, ...]:
    """Mirror Lean's four nondegenerate dyadic face preimages."""

    vertex, plane = coarse
    first, second = plane
    transverse = tuple(axis for axis in range(4) if axis not in plane)
    preimages: list[Plaquette4] = []
    for bits in product((0, 1), repeat=2):
        fine_vertex = [2 * coordinate for coordinate in vertex]
        fine_vertex[first] += 1
        fine_vertex[second] += 1
        for axis, bit in zip(transverse, bits, strict=True):
            fine_vertex[axis] += bit
        preimages.append((tuple(fine_vertex), plane))  # type: ignore[arg-type]
    return tuple(preimages)


def unit_cube_boundary(
    base: Vertex4,
    directions: tuple[int, int, int],
) -> tuple[Plaquette4, ...]:
    """The six plaquettes bounding one coordinate unit cube."""

    if len(set(directions)) != 3 or any(axis not in range(4) for axis in directions):
        raise ValueError("cube directions must be three distinct Z4 axes")
    faces: list[Plaquette4] = []
    for pair in combinations(directions, 2):
        missing = next(axis for axis in directions if axis not in pair)
        first, second = pair
        plane = (first, second)
        faces.extend(((base, plane), (add_e(base, missing), plane)))
    return tuple(faces)


def slab_link_incidence(
    extent: int,
) -> dict[Link4, tuple[Plaquette4, ...]]:
    """Incident corrected-slab faces at every physical link."""

    incidence: dict[Link4, list[Plaquette4]] = {}
    for plaquette in boundary_complete_slab_plaquettes(extent):
        for link in edges_of(plaquette):
            incidence.setdefault(link, []).append(plaquette)
    return {link: tuple(faces) for link, faces in incidence.items()}


def link_multiplicities(
    extent: int,
    labelling: SpinLabelling,
) -> dict[Link4, int]:
    """Exact SU(2) invariant multiplicity at every corrected-slab link."""

    return {
        link: invariant_multiplicity(
            tuple(
                labelling.get(face, 0)
                for face in incident
                if labelling.get(face, 0)
            )
        )
        for link, incident in slab_link_incidence(extent).items()
    }


def stretched_coarse_labelling(
    coarse_extent: int,
    fine_labelling: SpinLabelling,
) -> SpinLabelling:
    """Choose the independently stretched final spin on every coarse face."""

    return {
        coarse: sum(
            fine_labelling.get(fine, 0)
            for fine in dyadic_face_preimages(coarse)
        )
        for coarse in boundary_complete_slab_plaquettes(coarse_extent)
    }


@dataclass(frozen=True)
class StretchedCoherenceCounterexample:
    """One positive fine state whose stretched coarse target is inadmissible."""

    coarse_extent: int
    fine_extent: int
    fine_cutoff: int
    coarse_cutoff: int
    cube_base: Vertex4
    cube_directions: tuple[int, int, int]
    fine_faces: tuple[Plaquette4, ...]
    coarse_nonzero_faces: tuple[tuple[Plaquette4, int], ...]
    bad_coarse_links: tuple[Link4, ...]

    def validates(self) -> bool:
        fine_state = {face: self.fine_cutoff for face in self.fine_faces}
        fine_space = set(boundary_complete_slab_plaquettes(self.fine_extent))
        if not set(self.fine_faces).issubset(fine_space):
            return False
        if any(value <= 0 for value in link_multiplicities(
            self.fine_extent, fine_state
        ).values()):
            return False

        coarse_state = stretched_coarse_labelling(
            self.coarse_extent, fine_state
        )
        observed_nonzero = tuple(
            (face, value) for face, value in coarse_state.items() if value
        )
        if observed_nonzero != self.coarse_nonzero_faces:
            return False
        if any(value > self.coarse_cutoff for value in coarse_state.values()):
            return False
        multiplicities = link_multiplicities(self.coarse_extent, coarse_state)
        observed_bad = tuple(
            link for link, multiplicity in multiplicities.items()
            if multiplicity == 0
        )
        return observed_bad == self.bad_coarse_links


def minimal_stretched_coherence_counterexample() -> StretchedCoherenceCounterexample:
    """Return the exact one-cube obstruction on the `1 -> 3` slab pair."""

    coarse_extent = 1
    fine_extent = 2 * coarse_extent + 1
    fine_cutoff = 1
    coarse_cutoff = 4 * fine_cutoff
    base: Vertex4 = (0, 0, 1, 1)
    directions = (0, 2, 3)
    fine_faces = unit_cube_boundary(base, directions)
    fine_state = {face: fine_cutoff for face in fine_faces}
    coarse_state = stretched_coarse_labelling(coarse_extent, fine_state)
    coarse_nonzero = tuple(
        (face, value) for face, value in coarse_state.items() if value
    )
    bad_links = tuple(
        link
        for link, multiplicity in link_multiplicities(
            coarse_extent, coarse_state
        ).items()
        if multiplicity == 0
    )
    witness = StretchedCoherenceCounterexample(
        coarse_extent=coarse_extent,
        fine_extent=fine_extent,
        fine_cutoff=fine_cutoff,
        coarse_cutoff=coarse_cutoff,
        cube_base=base,
        cube_directions=directions,
        fine_faces=fine_faces,
        coarse_nonzero_faces=coarse_nonzero,
        bad_coarse_links=bad_links,
    )
    if not witness.validates():
        raise AssertionError("the pinned stretched-coherence witness drifted")
    return witness


if __name__ == "__main__":
    print(minimal_stretched_coherence_counterexample())
