"""Physical 4+2 page geometry behind the four-page wheel candidate.

The production Lean geometry enumerates every base vertex in ``[0,n)^4``,
then the six coordinate planes in the order ``01,02,03,12,13,23``.  A
genuinely interior direction-0 link is incident to six plaquettes: forward
and backward pages in each of transverse directions 1, 2, and 3.

The positivity wheel has only four pages.  This module pins the only direct
physical interpretation currently justified: choose the 01 and 02 pages as
active and put the two 03 pages in the vacuum representation.  It verifies
that the resulting six-valent invariant multiplicity equals the active
four-valent multiplicity for every tested label, as required by tensoring
with two copies of the trivial representation.

This closes the physical page-carrier slice.  It does not identify the four
cyclic rim words with the reflected boundary packet, and therefore does not
claim that the whole wheel geometry is pinned.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import TypeAlias, cast

from computations.exact_haar_network import invariant_multiplicity

Vertex4: TypeAlias = tuple[int, int, int, int]
Plane4: TypeAlias = tuple[int, int]
Link4: TypeAlias = tuple[Vertex4, int]
Plaquette4: TypeAlias = tuple[Vertex4, Plane4]

Z4_PLANES: tuple[Plane4, ...] = (
    (0, 1),
    (0, 2),
    (0, 3),
    (1, 2),
    (1, 3),
    (2, 3),
)


def add_e(vertex: Vertex4, direction: int) -> Vertex4:
    """Increment one coordinate, mirroring Lean ``addE``."""

    if direction not in range(4):
        raise ValueError("a Z4 direction must lie in range(4)")
    return cast(
        Vertex4,
        tuple(
            coordinate + int(axis == direction)
            for axis, coordinate in enumerate(vertex)
        ),
    )


def edges_of(plaquette: Plaquette4) -> tuple[Link4, Link4, Link4, Link4]:
    """Return the four unoriented boundary links in Lean enumeration order."""

    vertex, (first, second) = plaquette
    return (
        (vertex, first),
        (vertex, second),
        (add_e(vertex, second), first),
        (add_e(vertex, first), second),
    )


def box_vertices(extent: int) -> tuple[Vertex4, ...]:
    """Mirror the production corner-anchored ``boxVertices`` enumeration."""

    if extent < 0:
        raise ValueError("a box extent must be nonnegative")
    return tuple(
        cast(Vertex4, vertex)
        for vertex in product(range(extent), repeat=4)
    )


def box_plaquettes(extent: int) -> tuple[Plaquette4, ...]:
    """Mirror ``boxPlaquettes`` exactly."""

    return tuple(
        (vertex, plane)
        for vertex in box_vertices(extent)
        for plane in Z4_PLANES
    )


def box_links(extent: int) -> tuple[Link4, ...]:
    """Return physical boundary-link occurrences, including duplicates."""

    return tuple(
        link
        for plaquette in box_plaquettes(extent)
        for link in edges_of(plaquette)
    )


def distinct_box_links(extent: int) -> tuple[Link4, ...]:
    """Mirror Lean ``eraseDups`` while preserving first occurrence order."""

    seen: set[Link4] = set()
    distinct: list[Link4] = []
    for link in box_links(extent):
        if link not in seen:
            seen.add(link)
            distinct.append(link)
    return tuple(distinct)


def enumerated_links(extent: int) -> tuple[tuple[int, Link4], ...]:
    """Enumerate the physical links exactly as ``CompactDualPhysicalData``."""

    return tuple(enumerate(distinct_box_links(extent)))


def incident_plaquette_ids(extent: int, link: Link4) -> tuple[int, ...]:
    """Mirror the filtered production ``incidentPlaqIds`` list."""

    return tuple(
        face_id
        for face_id, plaquette in enumerate(box_plaquettes(extent))
        if link in edges_of(plaquette)
    )


@dataclass(frozen=True)
class FourPagePhysicalSlice:
    """One pinned four-active/two-vacuum slice of a physical six-valent link."""

    extent: int
    central_link: Link4
    central_link_id: int
    incident_face_ids: tuple[int, ...]
    active_face_ids: tuple[int, ...]
    vacuum_face_ids: tuple[int, ...]
    active_local_positions: tuple[int, ...]
    vacuum_local_positions: tuple[int, ...]

    def six_labels(self, active_labels: tuple[int, int, int, int]) -> tuple[int, ...]:
        """Insert four active labels and two vacuum labels in physical order."""

        if any(label < 0 for label in active_labels):
            raise ValueError("doubled spins must be nonnegative")
        labels = [0] * len(self.incident_face_ids)
        for position, label in zip(
            self.active_local_positions, active_labels, strict=True
        ):
            labels[position] = label
        return tuple(labels)

    def vacuum_reduction_holds(
        self, active_labels: tuple[int, int, int, int]
    ) -> bool:
        """Check ``Inv(active tensor 0 tensor 0) = Inv(active)`` exactly."""

        return invariant_multiplicity(
            self.six_labels(active_labels)
        ) == invariant_multiplicity(active_labels)

    def exhaustive_vacuum_reduction(self, maximum_label: int) -> bool:
        """Falsify the 4+2 reduction on the complete requested label cube."""

        if maximum_label < 0:
            raise ValueError("a maximum label must be nonnegative")
        return all(
            self.vacuum_reduction_holds(
                (labels[0], labels[1], labels[2], labels[3])
            )
            for labels in product(range(maximum_label + 1), repeat=4)
        )

    def is_physical_page_slice(self) -> bool:
        """Check every page and local position against the physical lists."""

        plaquettes = box_plaquettes(self.extent)
        links = enumerated_links(self.extent)
        return (
            len(self.incident_face_ids) == 6
            and len(self.active_face_ids) == 4
            and len(self.vacuum_face_ids) == 2
            and set(self.active_face_ids).isdisjoint(self.vacuum_face_ids)
            and set(self.active_face_ids) | set(self.vacuum_face_ids)
            == set(self.incident_face_ids)
            and tuple(
                self.incident_face_ids[position]
                for position in self.active_local_positions
            )
            == self.active_face_ids
            and tuple(
                self.incident_face_ids[position]
                for position in self.vacuum_local_positions
            )
            == self.vacuum_face_ids
            and (self.central_link_id, self.central_link) in links
            and all(
                0 <= face_id < len(plaquettes)
                and self.central_link in edges_of(plaquettes[face_id])
                for face_id in self.incident_face_ids
            )
        )


@dataclass(frozen=True)
class PhysicalWheelGeometryFrontier:
    """Honest status of the wheel-to-physical-geometry identification."""

    six_valent_link_pinned: bool
    four_active_page_slice_pinned: bool
    vacuum_reduction_verified: bool
    cyclic_rim_words_embedded: bool = False
    reflection_orientation_pinned: bool = False

    def is_full_geometry_pinned(self) -> bool:
        """Require the rim and reflection data, not only the page carrier."""

        return (
            self.six_valent_link_pinned
            and self.four_active_page_slice_pinned
            and self.vacuum_reduction_verified
            and self.cyclic_rim_words_embedded
            and self.reflection_orientation_pinned
        )

    def first_open_field(self) -> str | None:
        """Return the next missing geometry datum."""

        ordered = (
            ("six_valent_link_pinned", self.six_valent_link_pinned),
            ("four_active_page_slice_pinned", self.four_active_page_slice_pinned),
            ("vacuum_reduction_verified", self.vacuum_reduction_verified),
            ("cyclic_rim_words_embedded", self.cyclic_rim_words_embedded),
            ("reflection_orientation_pinned", self.reflection_orientation_pinned),
        )
        for name, closed in ordered:
            if not closed:
                return name
        return None


def build_four_page_physical_slice(extent: int = 2) -> FourPagePhysicalSlice:
    """Construct the canonical 01/02 active slice at the first interior link."""

    if extent < 2:
        raise ValueError("the canonical interior-link slice requires extent at least 2")
    central_link: Link4 = ((1, 1, 1, 1), 0)
    links = enumerated_links(extent)
    central_link_id = next(
        (identifier for identifier, link in links if link == central_link),
        -1,
    )
    if central_link_id < 0:
        raise AssertionError("the canonical central link is absent from the box")

    plaquettes = box_plaquettes(extent)
    incident = incident_plaquette_ids(extent, central_link)
    active = tuple(
        face_id
        for face_id in incident
        if plaquettes[face_id][1] in ((0, 1), (0, 2))
    )
    vacuum = tuple(
        face_id
        for face_id in incident
        if plaquettes[face_id][1] == (0, 3)
    )
    active_positions = tuple(incident.index(face_id) for face_id in active)
    vacuum_positions = tuple(incident.index(face_id) for face_id in vacuum)
    result = FourPagePhysicalSlice(
        extent=extent,
        central_link=central_link,
        central_link_id=central_link_id,
        incident_face_ids=incident,
        active_face_ids=active,
        vacuum_face_ids=vacuum,
        active_local_positions=active_positions,
        vacuum_local_positions=vacuum_positions,
    )
    if not result.is_physical_page_slice():
        raise AssertionError("the canonical 4+2 slice failed its physical incidence audit")
    return result


def current_wheel_geometry_frontier(
    maximum_checked_label: int = 3,
) -> PhysicalWheelGeometryFrontier:
    """Return the exact page-carrier result without inflating rim geometry."""

    physical_slice = build_four_page_physical_slice()
    return PhysicalWheelGeometryFrontier(
        six_valent_link_pinned=len(physical_slice.incident_face_ids) == 6,
        four_active_page_slice_pinned=physical_slice.is_physical_page_slice(),
        vacuum_reduction_verified=physical_slice.exhaustive_vacuum_reduction(
            maximum_checked_label
        ),
    )
