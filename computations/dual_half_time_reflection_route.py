"""Executable geometry audit for the CD-2 half-time reflection route.

The legacy physical box enumerates plaquette *basepoints* in ``[0,n)^4``.
Reflecting the bottom spatial plaquette across maximum vertex time ``n``
places its basepoint at time ``n``, outside that list.  Thus the legacy
``CompactDualPhysicalData.physicalTerm`` has no geometry-respecting face
reindex at nonzero extent.

The production Lean development already defines the correct replacement:
spatial plaquettes on all time slices ``0,...,M`` and temporal plaquettes on
``0,...,M-1``.  This module mirrors that boundary-complete slab, constructs
its exact face reflection permutation, and pins the reflection partner of the
four-active/two-temporal page carrier.

The result changes the CD-2 target: reflection intertwining must be stated for
the corrected slab physical term, or a separate exact bridge from the legacy
box term to that slab must be supplied.
"""

from __future__ import annotations

from dataclasses import dataclass

from computations.dual_positivity_geometry_bridge import (
    Link4,
    Plaquette4,
    Vertex4,
    box_plaquettes,
    edges_of,
)

SPATIAL_PLANES = ((0, 1), (0, 2), (1, 2))
TEMPORAL_PLANES = ((0, 3), (1, 3), (2, 3))


def _nat_sub(left: int, right: int) -> int:
    """Mirror truncated natural subtraction."""

    return max(left - right, 0)


def time_reflect_vertex(extent: int, vertex: Vertex4) -> Vertex4:
    """Reflect a vertex across maximum time ``extent``."""

    if extent < 0:
        raise ValueError("a reflection extent must be nonnegative")
    a, b, c, time = vertex
    return (a, b, c, _nat_sub(extent, time))


def time_reflect_link(extent: int, link: Link4) -> Link4:
    """Reflect a positive link, including the time-link base shift."""

    vertex, direction = link
    a, b, c, time = vertex
    if direction not in range(4):
        raise ValueError("a Z4 direction must lie in range(4)")
    reflected_time = (
        _nat_sub(extent, time + 1)
        if direction == 3
        else _nat_sub(extent, time)
    )
    return ((a, b, c, reflected_time), direction)


def time_reflect_plaquette(extent: int, plaquette: Plaquette4) -> Plaquette4:
    """Reflect a plaquette, shifting bases exactly in time-oriented planes."""

    vertex, plane = plaquette
    a, b, c, time = vertex
    if plane not in SPATIAL_PLANES + TEMPORAL_PLANES:
        raise ValueError("unknown Z4 coordinate plane")
    reflected_time = (
        _nat_sub(extent, time + 1)
        if plane in TEMPORAL_PLANES
        else _nat_sub(extent, time)
    )
    return ((a, b, c, reflected_time), plane)


def legacy_box_reflection_is_closed(extent: int) -> bool:
    """Decide reflection closure of the old base-coordinate box."""

    if extent <= 0:
        raise ValueError("the nonempty legacy-box audit requires positive extent")
    plaquettes = set(box_plaquettes(extent))
    return all(
        time_reflect_plaquette(extent, plaquette) in plaquettes
        for plaquette in plaquettes
    )


def legacy_bottom_spatial_reflection_witness(extent: int) -> tuple[Plaquette4, Plaquette4]:
    """Return the exact old-box nonclosure witness."""

    if extent <= 0:
        raise ValueError("the nonempty legacy-box audit requires positive extent")
    source: Plaquette4 = ((0, 0, 0, 0), (0, 1))
    reflected = time_reflect_plaquette(extent, source)
    if source not in box_plaquettes(extent):
        raise AssertionError("the legacy bottom plaquette is unexpectedly absent")
    if reflected in box_plaquettes(extent):
        raise AssertionError("the legacy reflection obstruction disappeared")
    return source, reflected


def boundary_complete_slab_plaquettes(extent: int) -> tuple[Plaquette4, ...]:
    """Mirror the corrected production slab face enumeration."""

    if extent < 0:
        raise ValueError("a corrected slab extent must be nonnegative")
    return tuple(
        plaquette
        for plaquette in box_plaquettes(extent + 1)
        if (
            plaquette[0][3] <= extent
            if plaquette[1] in SPATIAL_PLANES
            else plaquette[0][3] < extent
        )
    )


def slab_face_reflection_permutation(extent: int) -> tuple[int, ...]:
    """Return the corrected slab's exact numerical face involution."""

    plaquettes = boundary_complete_slab_plaquettes(extent)
    index = {plaquette: face_id for face_id, plaquette in enumerate(plaquettes)}
    if len(index) != len(plaquettes):
        raise AssertionError("the corrected slab face list has duplicates")
    try:
        return tuple(
            index[time_reflect_plaquette(extent, plaquette)]
            for plaquette in plaquettes
        )
    except KeyError as error:
        raise AssertionError("the corrected slab is not reflection closed") from error


def corrected_slab_reflection_is_involutive(extent: int) -> bool:
    """Check the numerical face permutation squares to the identity."""

    permutation = slab_face_reflection_permutation(extent)
    return all(
        permutation[permutation[face_id]] == face_id
        for face_id in range(len(permutation))
    )


def slab_incident_face_ids(extent: int, link: Link4) -> tuple[int, ...]:
    """Return corrected-slab face identifiers incident to a physical link."""

    return tuple(
        face_id
        for face_id, plaquette in enumerate(
            boundary_complete_slab_plaquettes(extent)
        )
        if link in edges_of(plaquette)
    )


@dataclass(frozen=True)
class CorrectedPageReflectionPair:
    """Lower/upper partners of the four-active/two-temporal page carrier."""

    half: int
    extent: int
    lower_link: Link4
    upper_link: Link4
    lower_incident_face_ids: tuple[int, ...]
    upper_incident_face_ids: tuple[int, ...]
    lower_active_face_ids: tuple[int, ...]
    upper_active_face_ids: tuple[int, ...]
    lower_temporal_face_ids: tuple[int, ...]
    upper_temporal_face_ids: tuple[int, ...]
    reflected_lower_face_ids: tuple[int, ...]

    def is_closed(self) -> bool:
        """Check exact page incidence and the face/link reflection map."""

        plaquettes = boundary_complete_slab_plaquettes(self.extent)
        permutation = slab_face_reflection_permutation(self.extent)
        return (
            self.extent == self.half + self.half + 1
            and self.upper_link == time_reflect_link(self.extent, self.lower_link)
            and len(self.lower_incident_face_ids) == 6
            and len(self.upper_incident_face_ids) == 6
            and len(self.lower_active_face_ids) == 4
            and len(self.upper_active_face_ids) == 4
            and len(self.lower_temporal_face_ids) == 2
            and len(self.upper_temporal_face_ids) == 2
            and self.reflected_lower_face_ids
            == tuple(
                permutation[face_id] for face_id in self.lower_incident_face_ids
            )
            and set(self.reflected_lower_face_ids)
            == set(self.upper_incident_face_ids)
            and all(
                self.lower_link in edges_of(plaquettes[face_id])
                for face_id in self.lower_incident_face_ids
            )
            and all(
                self.upper_link in edges_of(plaquettes[face_id])
                for face_id in self.upper_incident_face_ids
            )
            and set(
                permutation[face_id] for face_id in self.lower_active_face_ids
            )
            == set(self.upper_active_face_ids)
            and set(
                permutation[face_id] for face_id in self.lower_temporal_face_ids
            )
            == set(self.upper_temporal_face_ids)
        )


@dataclass(frozen=True)
class CD2ReflectionRouteFrontier:
    """The exact geometry choice required before a reflection-preserving block."""

    legacy_physical_term_reflection_closed: bool
    corrected_slab_face_permutation_pinned: bool
    corrected_page_pair_pinned: bool
    corrected_slab_spin_foam_term_pinned: bool = False
    legacy_to_corrected_term_bridge_pinned: bool = False

    def viable_physical_term_route_selected(self) -> bool:
        """Require one honest way to put the physical weight on corrected faces."""

        return (
            self.corrected_slab_spin_foam_term_pinned
            or self.legacy_to_corrected_term_bridge_pinned
        )

    def first_open_field(self) -> str | None:
        """Return the next missing reflection-route field."""

        if not self.corrected_slab_face_permutation_pinned:
            return "corrected_slab_face_permutation_pinned"
        if not self.corrected_page_pair_pinned:
            return "corrected_page_pair_pinned"
        if not self.viable_physical_term_route_selected():
            return "corrected_slab_term_or_legacy_bridge"
        return None

    def is_reflection_route_closed(self) -> bool:
        """Reject the legacy term unless a corrected physical route exists."""

        return (
            not self.legacy_physical_term_reflection_closed
            and self.first_open_field() is None
        )


def build_corrected_page_reflection_pair(half: int = 1) -> CorrectedPageReflectionPair:
    """Pin the first nondegenerate central page carrier and its reflection."""

    if half < 1:
        raise ValueError("the four-page central carrier requires half at least one")
    extent = half + half + 1
    lower_link: Link4 = ((1, 1, 1, half), 0)
    upper_link = time_reflect_link(extent, lower_link)
    plaquettes = boundary_complete_slab_plaquettes(extent)
    lower_incident = slab_incident_face_ids(extent, lower_link)
    upper_incident = slab_incident_face_ids(extent, upper_link)
    lower_active = tuple(
        face_id
        for face_id in lower_incident
        if plaquettes[face_id][1] in ((0, 1), (0, 2))
    )
    upper_active = tuple(
        face_id
        for face_id in upper_incident
        if plaquettes[face_id][1] in ((0, 1), (0, 2))
    )
    lower_temporal = tuple(
        face_id
        for face_id in lower_incident
        if plaquettes[face_id][1] == (0, 3)
    )
    upper_temporal = tuple(
        face_id
        for face_id in upper_incident
        if plaquettes[face_id][1] == (0, 3)
    )
    permutation = slab_face_reflection_permutation(extent)
    result = CorrectedPageReflectionPair(
        half=half,
        extent=extent,
        lower_link=lower_link,
        upper_link=upper_link,
        lower_incident_face_ids=lower_incident,
        upper_incident_face_ids=upper_incident,
        lower_active_face_ids=lower_active,
        upper_active_face_ids=upper_active,
        lower_temporal_face_ids=lower_temporal,
        upper_temporal_face_ids=upper_temporal,
        reflected_lower_face_ids=tuple(
            permutation[face_id] for face_id in lower_incident
        ),
    )
    if not result.is_closed():
        raise AssertionError("the corrected central page reflection audit failed")
    return result


def current_cd2_reflection_route_frontier() -> CD2ReflectionRouteFrontier:
    """Return the honest route after the corrected finite geometry is pinned."""

    page_pair = build_corrected_page_reflection_pair()
    return CD2ReflectionRouteFrontier(
        legacy_physical_term_reflection_closed=legacy_box_reflection_is_closed(1),
        corrected_slab_face_permutation_pinned=corrected_slab_reflection_is_involutive(
            page_pair.extent
        ),
        corrected_page_pair_pinned=page_pair.is_closed(),
    )
