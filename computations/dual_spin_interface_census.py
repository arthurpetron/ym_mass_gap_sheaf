"""Exact first-branching census for the two-four-cube SU(2) dual.

The two-cell brick has 8,192 closed binary surfaces and 234 genus-one
surfaces which use at least one plaquette in the shared three-face.  Each
such torus is the symmetric difference of 4,096 unordered binary-surface
pairs, giving 958,464 physical pairs.

This module quotients that finite family by the full 96-element cuboid
symmetry group.  The first branching filtration consists of pairs with at
most five overlap faces: five is the first order at which the relative
mod-two boundary can terminate at an admissible trivalent spin-one packet.
The stratum has 58,878 pairs, 1,219 pair orbits, and 2,166 admissible
resolved-channel orbits.  Exactly 14 of those orbits have nonzero relative
boundary defect.  Their exact Haar amplitudes are all positive.

The cutoff at overlap five is an explicit filtration boundary, not a claim
about the remaining pair space.  Direct quaternion-polynomial integration
does not scale across all 2,166 representatives; the next gate must contract
the decorated interface packets in a fusion basis.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from functools import cache
from itertools import permutations, product
from math import prod
from random import Random
from typing import TypeAlias, cast

from computations.dual_spin_gluing import (
    InterfaceEdgePacket,
    build_two_cell_spin_gluing,
    decorated_interface_carrier,
    permute_face_mask,
    relative_boundary_defect,
    two_cell_brick,
)
from computations.exact_haar_network import (
    GaugeFixedComplex,
    Poly,
    chi,
    contract_pairing_aware,
    invariant_multiplicity,
    scalar,
)
from computations.hypercube4d_survey import (
    coordinate_clifford_torus_mask,
    edge_cycles_homologous_mod2,
    face_chain_boundary_mask,
    kernel_basis,
    surface_betti_numbers_mod2,
    surfaces,
    vertex_sixj_product,
)

FacePermutation: TypeAlias = tuple[int, ...]
ResolvedChannel: TypeAlias = tuple[int, int]
SurfacePair: TypeAlias = tuple[int, int]
TorusClass: TypeAlias = tuple[int, int]

FIRST_BRANCHING_OVERLAP = 5
GAUGE_TREE_CANDIDATES = 12
GAUGE_TREE_SEED = 20260723


@dataclass(frozen=True)
class InterfacePairCensus:
    """Pinned cardinalities for the interface-bearing pair filtration."""

    closed_surfaces: int
    genus_one_surfaces: int
    interface_genus_one_surfaces: int
    physical_pairs: int
    overlap_census: tuple[tuple[int, int], ...]
    filtered_pairs: int
    filtered_pair_orbits: int
    raw_orbit_representative_channels: int
    admissible_orbit_representative_channels: int
    resolved_channel_orbits: int
    nonzero_defect_channel_orbits: int


@dataclass(frozen=True)
class ResolvedChannelQuotient:
    """Symmetry quotient of a bounded-overlap resolved-channel family."""

    raw_representative_channels: int
    admissible_representative_channels: int
    representatives: tuple[ResolvedChannel, ...]


def _permute_surface_pair(
    pair: SurfacePair,
    permutation: FacePermutation,
) -> SurfacePair:
    return cast(
        SurfacePair,
        tuple(
            sorted(
                (
                    permute_face_mask(pair[0], permutation),
                    permute_face_mask(pair[1], permutation),
                )
            )
        ),
    )


@cache
def brick_symmetry_face_maps() -> tuple[FacePermutation, ...]:
    """Return the full 96-element face action of the ``(2,1,1,1)`` brick."""

    _complex, _faces, meta = two_cell_brick()
    shape = (2, 1, 1, 1)
    lookup = {face: index for index, face in enumerate(meta)}
    maps: list[FacePermutation] = []
    for transverse_permutation in permutations((1, 2, 3)):
        axis_map = (0, *transverse_permutation)
        for reflections in product((False, True), repeat=4):
            permutation: list[int] = []
            for point, first, second in meta:
                transformed_point = [0, 0, 0, 0]
                for old_axis, coordinate in enumerate(point):
                    transformed_coordinate = (
                        shape[old_axis]
                        - coordinate
                        - int(old_axis in (first, second))
                        if reflections[old_axis]
                        else coordinate
                    )
                    transformed_point[axis_map[old_axis]] = transformed_coordinate
                new_first, new_second = sorted((axis_map[first], axis_map[second]))
                permutation.append(
                    lookup[
                        (
                            cast(tuple[int, int, int, int], tuple(transformed_point)),
                            new_first,
                            new_second,
                        )
                    ]
                )
            maps.append(tuple(permutation))
    result = tuple(sorted(set(maps)))
    if len(result) != 96:
        raise AssertionError("the two-cell cuboid symmetry action is not faithful")
    return result


@cache
def closed_surface_masks() -> tuple[int, ...]:
    """Return all closed binary surfaces in the two-cell brick."""

    complex_, faces, _meta = two_cell_brick()
    result = tuple(surfaces(kernel_basis(complex_, faces)))
    if len(result) != 8192:
        raise AssertionError("the two-cell binary cycle space changed dimension")
    return result


@cache
def genus_one_surface_masks() -> tuple[int, ...]:
    """Return every connected mod-two genus-one surface in the brick."""

    complex_, faces, _meta = two_cell_brick()
    return tuple(
        surface
        for surface in closed_surface_masks()
        if surface_betti_numbers_mod2(complex_, faces, surface) == (1, 2, 1)
    )


@cache
def interface_genus_one_surface_masks() -> tuple[int, ...]:
    """Return genus-one surfaces which use the shared three-face."""

    interface = build_two_cell_spin_gluing().interface_face_mask
    return tuple(surface for surface in genus_one_surface_masks() if surface & interface)


@cache
def interface_pair_overlap_census() -> tuple[tuple[int, int], ...]:
    """Count all physical pairs by their number of coincident faces."""

    counts: Counter[int] = Counter()
    for surface in interface_genus_one_surface_masks():
        for left in closed_surface_masks():
            right = left ^ surface
            if left < right:
                counts[(left & right).bit_count()] += 1
    return tuple(sorted(counts.items()))


@cache
def bounded_overlap_pair_orbit_representatives(
    maximum_overlap: int = FIRST_BRANCHING_OVERLAP,
) -> tuple[SurfacePair, ...]:
    """Classify physical interface pairs through a fixed overlap order."""

    if maximum_overlap < 0:
        raise ValueError("the overlap cutoff must be nonnegative")
    pairs = {
        (left, right)
        for surface in interface_genus_one_surface_masks()
        for left in closed_surface_masks()
        for right in (left ^ surface,)
        if left < right and (left & right).bit_count() <= maximum_overlap
    }
    maps = brick_symmetry_face_maps()
    representatives: list[SurfacePair] = []
    while pairs:
        representative = min(pairs)
        orbit = {
            _permute_surface_pair(representative, permutation)
            for permutation in maps
        }
        if not orbit <= pairs:
            raise AssertionError("bounded-overlap pair family is not symmetry stable")
        pairs.difference_update(orbit)
        representatives.append(representative)
    return tuple(representatives)


@cache
def _edge_face_indices() -> tuple[tuple[int, ...], ...]:
    complex_, faces, _meta = two_cell_brick()
    return tuple(
        tuple(
            face_index
            for face_index, face in enumerate(faces)
            if any(face_edge == edge for face_edge, _orientation in face)
        )
        for edge in range(len(complex_.edges))
    )


@cache
def _face_count() -> int:
    _complex, faces, _meta = two_cell_brick()
    return len(faces)


def resolved_channel_is_admissible(surface: int, selected: int) -> bool:
    """Test every local SU(2) invariant without invoking the Haar integrator."""

    face_count = _face_count()
    if (
        surface < 0
        or selected < 0
        or surface & selected
        or (surface | selected) >> face_count
    ):
        raise ValueError("surface and selected masks must be disjoint brick masks")
    labels = tuple(
        1 if (surface >> face) & 1 else 2 if (selected >> face) & 1 else 0
        for face in range(face_count)
    )
    return all(
        invariant_multiplicity(tuple(labels[face] for face in incident if labels[face])) > 0
        for incident in _edge_face_indices()
    )


@cache
def bounded_overlap_resolved_channel_quotient(
    maximum_overlap: int = FIRST_BRANCHING_OVERLAP,
) -> ResolvedChannelQuotient:
    """Quotient all admissible resolved channels in the bounded pair family."""

    maps = brick_symmetry_face_maps()
    representatives: set[ResolvedChannel] = set()
    raw_count = 0
    admissible_count = 0
    for left, right in bounded_overlap_pair_orbit_representatives(maximum_overlap):
        surface = left ^ right
        overlap_faces = [
            face
            for face in range(max((left | right).bit_length(), 1))
            if ((left & right) >> face) & 1
        ]
        for selection in range(1 << len(overlap_faces)):
            raw_count += 1
            selected = sum(
                1 << face
                for index, face in enumerate(overlap_faces)
                if (selection >> index) & 1
            )
            if not resolved_channel_is_admissible(surface, selected):
                continue
            admissible_count += 1
            representatives.add(
                min(
                    (
                        permute_face_mask(surface, permutation),
                        permute_face_mask(selected, permutation),
                    )
                    for permutation in maps
                )
            )
    return ResolvedChannelQuotient(
        raw_representative_channels=raw_count,
        admissible_representative_channels=admissible_count,
        representatives=tuple(sorted(representatives)),
    )


@cache
def nonzero_defect_channel_representatives(
    maximum_overlap: int = FIRST_BRANCHING_OVERLAP,
) -> tuple[ResolvedChannel, ...]:
    """Return the genuinely branched resolved-channel orbit representatives."""

    return tuple(
        (surface, selected)
        for surface, selected in bounded_overlap_resolved_channel_quotient(
            maximum_overlap
        ).representatives
        if relative_boundary_defect(surface, selected)
    )


def channel_interface_carrier(
    channel: ResolvedChannel,
) -> tuple[InterfaceEdgePacket, ...]:
    """Return the decorated interface state of a resolved-channel orbit."""

    return decorated_interface_carrier(*channel)


@cache
def _cell_face_indices(cell: int) -> tuple[int, ...]:
    if cell not in (0, 1):
        raise ValueError("the two-cell brick has cells zero and one")
    mask = build_two_cell_spin_gluing().cell_face_masks[cell]
    return tuple(face for face in range(_face_count()) if (mask >> face) & 1)


@cache
def _cell_local_meta(
    cell: int,
) -> tuple[tuple[tuple[int, int, int, int], int, int], ...]:
    _complex, _faces, meta = two_cell_brick()
    return tuple(
        (
            (
                point[0] - cell,
                point[1],
                point[2],
                point[3],
            ),
            first,
            second,
        )
        for face in _cell_face_indices(cell)
        for point, first, second in (meta[face],)
    )


def cell_local_channel_value(channel: ResolvedChannel) -> Fraction | None:
    """Evaluate a channel supported on one four-cell by its vertex six-j product."""

    surface, selected = channel
    support = surface | selected
    certificate = build_two_cell_spin_gluing()
    for cell, cell_mask in enumerate(certificate.cell_face_masks):
        if support & ~cell_mask:
            continue
        spins = tuple(
            1
            if (surface >> face) & 1
            else 2
            if (selected >> face) & 1
            else 0
            for face in _cell_face_indices(cell)
        )
        return vertex_sixj_product(_cell_local_meta(cell), spins)
    return None


@cache
def _coordinate_torus_cell_and_planes(
    surface: int,
) -> tuple[int, tuple[int, int], tuple[int, int]] | None:
    """Recognize a coordinate Clifford torus on either cell boundary."""

    plane_splits = (
        ((0, 1), (2, 3)),
        ((0, 2), (1, 3)),
        ((0, 3), (1, 2)),
    )
    for cell in (0, 1):
        indices = _cell_face_indices(cell)
        local_surface = sum(
            1 << local_face
            for local_face, global_face in enumerate(indices)
            if (surface >> global_face) & 1
        )
        if local_surface.bit_count() != surface.bit_count():
            continue
        for first_plane, second_plane in plane_splits:
            if local_surface == coordinate_clifford_torus_mask(
                _cell_local_meta(cell),
                first_plane,
                second_plane,
            ):
                return cell, first_plane, second_plane
    return None


def coordinate_torus_homology_class(
    channel: ResolvedChannel,
) -> TorusClass | None:
    """Return ``[boundary D]`` in the product basis of a cell Clifford torus."""

    surface, selected = channel
    geometry = _coordinate_torus_cell_and_planes(surface)
    if geometry is None or relative_boundary_defect(surface, selected):
        return None
    cell, first_plane, second_plane = geometry
    _complex, faces, meta = two_cell_brick()
    surface_edges = {
        edge
        for face_index, face in enumerate(faces)
        if (surface >> face_index) & 1
        for edge, _orientation in face
    }

    basis_cycles: list[int] = []
    for plane in (first_plane, second_plane):
        candidate = next(
            (
                face
                for face in _cell_face_indices(cell)
                if {meta[face][1], meta[face][2]} == set(plane)
                and {edge for edge, _orientation in faces[face]} <= surface_edges
            ),
            None,
        )
        if candidate is None:
            raise AssertionError("coordinate torus lost a product cap")
        basis_cycles.append(face_chain_boundary_mask(faces, 1 << candidate))

    selected_boundary = face_chain_boundary_mask(faces, selected)
    matches: list[TorusClass] = [
        (first, second)
        for first, second in product((0, 1), repeat=2)
        if edge_cycles_homologous_mod2(
            faces,
            surface,
            selected_boundary,
            (basis_cycles[0] if first else 0) ^ (basis_cycles[1] if second else 0),
        )
    ]
    if len(matches) != 1:
        raise AssertionError("torus boundary did not have a unique homology class")
    return matches[0]


@cache
def minimal_interface_torus_channels() -> tuple[ResolvedChannel, ...]:
    """Return the complete 16-face interface-torus stratum through overlap five."""

    interface = build_two_cell_spin_gluing().interface_face_mask
    return tuple(
        channel
        for channel in bounded_overlap_resolved_channel_quotient().representatives
        if channel[0].bit_count() == 16
        and (channel[0] & interface).bit_count() == 4
    )


def minimal_interface_torus_channel_value(channel: ResolvedChannel) -> Fraction:
    """Use the one-cell vertex factorization whenever the support permits it."""

    if channel not in set(minimal_interface_torus_channels()):
        raise ValueError("channel is outside the minimal interface-torus stratum")
    local = cell_local_channel_value(channel)
    return exact_interface_channel_value(channel) if local is None else local


@cache
def twenty_face_torus_channels() -> tuple[ResolvedChannel, ...]:
    """Return the first genuinely non-product two-cell torus stratum."""

    interface = build_two_cell_spin_gluing().interface_face_mask
    channels = tuple(
        channel
        for channel in bounded_overlap_resolved_channel_quotient().representatives
        if channel[0].bit_count() == 20
        and (channel[0] & interface).bit_count() == 3
    )
    surfaces = {surface for surface, _selected in channels}
    if len(surfaces) != 1:
        raise AssertionError("the 20-face quotient stopped being a single surface orbit")
    return channels


@cache
def twenty_face_torus_homology_basis() -> tuple[int, int]:
    """Choose the first two independent channel boundaries as an ``H1`` basis."""

    _complex, faces, _meta = two_cell_brick()
    channels = twenty_face_torus_channels()
    surface = channels[0][0]
    basis: list[int] = []
    for _surface, selected in channels:
        cycle = face_chain_boundary_mask(faces, selected)
        if edge_cycles_homologous_mod2(faces, surface, cycle, 0):
            continue
        if not basis:
            basis.append(cycle)
            continue
        if edge_cycles_homologous_mod2(faces, surface, cycle, basis[0]):
            continue
        basis.append(cycle)
        break
    if len(basis) != 2:
        raise AssertionError("the 20-face channel family did not span torus homology")
    return basis[0], basis[1]


def twenty_face_torus_homology_class(channel: ResolvedChannel) -> TorusClass:
    """Reduce a 20-face selected-chain boundary in the pinned torus basis."""

    if channel not in set(twenty_face_torus_channels()):
        raise ValueError("channel is outside the 20-face torus stratum")
    _complex, faces, _meta = two_cell_brick()
    surface, selected = channel
    basis = twenty_face_torus_homology_basis()
    cycle = face_chain_boundary_mask(faces, selected)
    matches: list[TorusClass] = [
        (first, second)
        for first, second in product((0, 1), repeat=2)
        if edge_cycles_homologous_mod2(
            faces,
            surface,
            cycle,
            (basis[0] if first else 0) ^ (basis[1] if second else 0),
        )
    ]
    if len(matches) != 1:
        raise AssertionError("20-face boundary did not have a unique homology class")
    return matches[0]


def twenty_face_torus_channel_value(channel: ResolvedChannel) -> Fraction:
    """Evaluate the 20-face stratum in its optimized exact gauge."""

    if channel not in set(twenty_face_torus_channels()):
        raise ValueError("channel is outside the 20-face torus stratum")
    return optimized_interface_channel_value(channel)


@cache
def twenty_two_face_torus_channels() -> tuple[ResolvedChannel, ...]:
    """Return the first stratum mixing cycles with trivalent interface branches."""

    interface = build_two_cell_spin_gluing().interface_face_mask
    channels = tuple(
        channel
        for channel in bounded_overlap_resolved_channel_quotient().representatives
        if channel[0].bit_count() == 22
        and (channel[0] & interface).bit_count() == 2
    )
    surfaces = {surface for surface, _selected in channels}
    if len(surfaces) != 1:
        raise AssertionError("the 22-face quotient stopped being a single surface orbit")
    return channels


@cache
def twenty_two_face_cycle_channels() -> tuple[ResolvedChannel, ...]:
    """Return the defect-free subspace of the 22-face decorated carrier."""

    return tuple(
        channel
        for channel in twenty_two_face_torus_channels()
        if not relative_boundary_defect(*channel)
    )


@cache
def twenty_two_face_homology_basis() -> tuple[int, int]:
    """Choose a deterministic basis from the defect-free channel boundaries."""

    _complex, faces, _meta = two_cell_brick()
    channels = twenty_two_face_cycle_channels()
    surface = channels[0][0]
    basis: list[int] = []
    for _surface, selected in channels:
        cycle = face_chain_boundary_mask(faces, selected)
        if edge_cycles_homologous_mod2(faces, surface, cycle, 0):
            continue
        if not basis:
            basis.append(cycle)
            continue
        if edge_cycles_homologous_mod2(faces, surface, cycle, basis[0]):
            continue
        basis.append(cycle)
        break
    if len(basis) != 2:
        raise AssertionError("the 22-face cycle channels did not span torus homology")
    return basis[0], basis[1]


def twenty_two_face_homology_class(channel: ResolvedChannel) -> TorusClass:
    """Reduce a defect-free 22-face channel in the pinned torus basis."""

    if channel not in set(twenty_two_face_cycle_channels()):
        raise ValueError("channel is outside the 22-face cycle sector")
    _complex, faces, _meta = two_cell_brick()
    surface, selected = channel
    basis = twenty_two_face_homology_basis()
    cycle = face_chain_boundary_mask(faces, selected)
    matches: list[TorusClass] = [
        (first, second)
        for first, second in product((0, 1), repeat=2)
        if edge_cycles_homologous_mod2(
            faces,
            surface,
            cycle,
            (basis[0] if first else 0) ^ (basis[1] if second else 0),
        )
    ]
    if len(matches) != 1:
        raise AssertionError("22-face boundary did not have a unique homology class")
    return matches[0]


def twenty_two_face_channel_value(channel: ResolvedChannel) -> Fraction:
    """Evaluate the complete 22-face decorated carrier in an optimized gauge."""

    if channel not in set(twenty_two_face_torus_channels()):
        raise ValueError("channel is outside the 22-face torus stratum")
    return optimized_interface_channel_value(channel)


@cache
def exact_interface_channel_value(channel: ResolvedChannel) -> Fraction:
    """Evaluate one resolved-channel representative by exact Haar integration."""

    from computations.interior_link4d_probe import evaluate_active_assignment

    complex_, faces, _meta = two_cell_brick()
    surface, selected = channel
    spins = tuple(
        1
        if (surface >> face) & 1
        else 2
        if (selected >> face) & 1
        else 0
        for face in range(len(faces))
    )
    return evaluate_active_assignment(complex_, faces, spins)


@cache
def optimized_interface_channel_value(channel: ResolvedChannel) -> Fraction:
    """Evaluate a channel after deterministic maximal-tree optimization.

    Gauge invariance permits any maximal tree.  The default breadth-first
    tree can create thousands of coordinate monomials before contraction.
    This evaluator generates a fixed finite family of vertex/edge
    relabellings, constructs the induced breadth-first tree for each, and
    chooses the tree minimizing the product of the initial face-factor
    sizes.  The subsequent Haar contraction is unchanged and exact.
    """

    complex_, faces, _meta = two_cell_brick()
    surface, selected = channel
    if not resolved_channel_is_admissible(surface, selected):
        return Fraction(0)
    spins = tuple(
        1
        if (surface >> face) & 1
        else 2
        if (selected >> face) & 1
        else 0
        for face in range(len(faces))
    )
    active_faces = [face for face, spin in enumerate(spins) if spin]
    active_edges = sorted(
        {
            edge
            for face in active_faces
            for edge, _orientation in faces[face]
        }
    )
    edge_position = {edge: index for index, edge in enumerate(active_edges)}
    active_vertices = sorted(
        {
            vertex
            for edge in active_edges
            for vertex in complex_.edges[edge]
        }
    )
    vertex_position = {
        vertex: index for index, vertex in enumerate(active_vertices)
    }
    base_edges = [
        (
            vertex_position[complex_.edges[edge][0]],
            vertex_position[complex_.edges[edge][1]],
        )
        for edge in active_edges
    ]
    base_faces = {
        face: [
            (edge_position[edge], orientation)
            for edge, orientation in faces[face]
        ]
        for face in active_faces
    }

    vertex_ids = list(range(len(active_vertices)))
    edge_ids = list(range(len(active_edges)))
    generator = Random(GAUGE_TREE_SEED)
    best_score: tuple[int, int, int, int] | None = None
    best_complex: GaugeFixedComplex | None = None
    best_factors: list[Poly] | None = None
    for candidate in range(GAUGE_TREE_CANDIDATES):
        vertex_permutation = (
            vertex_ids[:]
            if candidate == 0
            else generator.sample(vertex_ids, len(vertex_ids))
        )
        edge_permutation = (
            edge_ids[:]
            if candidate == 0
            else generator.sample(edge_ids, len(edge_ids))
        )
        vertex_inverse = {
            old: new for new, old in enumerate(vertex_permutation)
        }
        edge_inverse = {
            old: new for new, old in enumerate(edge_permutation)
        }
        candidate_complex = GaugeFixedComplex(
            len(active_vertices),
            [
                (
                    vertex_inverse[base_edges[old_edge][0]],
                    vertex_inverse[base_edges[old_edge][1]],
                )
                for old_edge in edge_permutation
            ],
        )
        candidate_faces = {
            face: [
                (edge_inverse[edge], orientation)
                for edge, orientation in base_faces[face]
            ]
            for face in active_faces
        }
        factors = [
            chi(
                spins[face],
                candidate_complex.holonomy_of(candidate_faces[face]),
            )
            for face in active_faces
        ]
        sizes = tuple(max(1, len(factor)) for factor in factors)
        score = (
            prod(sizes),
            max(sizes, default=1),
            sum(sizes),
            candidate,
        )
        if best_score is None or score < best_score:
            best_score = score
            best_complex = candidate_complex
            best_factors = factors
    if best_complex is None or best_factors is None:
        raise AssertionError("gauge-tree optimizer produced no candidate")
    value = best_complex.contract_invariant(best_factors)
    if any(power != 0 for power in value):
        raise AssertionError("optimized fixed-spin amplitude acquired heat powers")
    return value.get(0, Fraction(0))


@cache
def pairing_interface_channel_value(channel: ResolvedChannel) -> Fraction:
    """Evaluate a label-one/two channel through fundamental Haar projectors.

    The character identity ``chi_2 = chi_1**2 - 1`` expands each selected
    spin-one face into either two explicit fundamental strands or the
    subtraction term.  Link-linear factors are then contracted by
    :func:`contract_pairing_aware`, retaining the local invariant projector
    before any generic coordinate multiplication.
    """

    complex_, faces, _meta = two_cell_brick()
    surface, selected = channel
    if not resolved_channel_is_admissible(surface, selected):
        return Fraction(0)
    fundamental_factors = tuple(
        chi(1, complex_.holonomy_of(face))
        for face in faces
    )
    surface_faces = [
        face for face in range(len(faces)) if (surface >> face) & 1
    ]
    selected_faces = [
        face for face in range(len(faces)) if (selected >> face) & 1
    ]
    total = Fraction(0)
    for doubled_selection in range(1 << len(selected_faces)):
        doubled_faces = [
            face
            for index, face in enumerate(selected_faces)
            if (doubled_selection >> index) & 1
        ]
        factors = [
            fundamental_factors[face]
            for face in surface_faces
        ]
        factors.extend(
            fundamental_factors[face]
            for face in doubled_faces
            for _copy in range(2)
        )
        contracted = scalar(contract_pairing_aware(factors, complex_.free))
        if any(power != 0 for power in contracted):
            raise AssertionError("fundamental channel contraction acquired heat powers")
        sign = -1 if (len(selected_faces) - len(doubled_faces)) % 2 else 1
        total += sign * contracted.get(0, Fraction(0))
    return total


@cache
def first_branching_census() -> InterfacePairCensus:
    """Return the complete cardinality certificate through overlap five."""

    quotient = bounded_overlap_resolved_channel_quotient()
    overlap_census = interface_pair_overlap_census()
    return InterfacePairCensus(
        closed_surfaces=len(closed_surface_masks()),
        genus_one_surfaces=len(genus_one_surface_masks()),
        interface_genus_one_surfaces=len(interface_genus_one_surface_masks()),
        physical_pairs=sum(count for _overlap, count in overlap_census),
        overlap_census=overlap_census,
        filtered_pairs=sum(
            count
            for overlap, count in overlap_census
            if overlap <= FIRST_BRANCHING_OVERLAP
        ),
        filtered_pair_orbits=len(bounded_overlap_pair_orbit_representatives()),
        raw_orbit_representative_channels=quotient.raw_representative_channels,
        admissible_orbit_representative_channels=(
            quotient.admissible_representative_channels
        ),
        resolved_channel_orbits=len(quotient.representatives),
        nonzero_defect_channel_orbits=len(nonzero_defect_channel_representatives()),
    )
