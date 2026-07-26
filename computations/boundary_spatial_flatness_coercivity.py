"""Exact single-well topology of the 24-face spatial boundary potential.

The enlarged BF4 boundary carrier has 48 spatial links and 26 vertices.
Tree gauge leaves 23 cycle variables.  The 24 spatial plaquette boundaries
have rank 23: they span every cycle, with one closed-surface relation.

This module certifies more than the rank count.  The full 24-face complex is
not itself a surface: its edge degrees are nonuniform.  Eighteen elementary
face--free-edge collapses followed by eighteen graph leaf collapses retract
it onto the six-face boundary of one cube.  Thus the spatial complex has the
homotopy type of a two-sphere.  A flat ``SU(2)`` connection on it is gauge
equivalent to the trivial connection, so the spatial heat-kernel weight has
one flat gauge orbit rather than several topological wells.

After a deterministic spanning-tree gauge, the linearized plaquette
curvature map is a ``24 x 23`` integral matrix of full column rank.  Its
Gram matrix is positive definite.  More sharply, every leading principal
minor of ``11 * Gram - I`` is positive.  Sylvester's criterion gives

    Gram > (1/11) * I.

This is a finite single-well/coercivity input for the projective Harnack
route.  Reversing a complete collapse of the complex with one redundant
face removed also gives a triangular non-Abelian reconstruction.  The
bi-invariant triangle inequality yields the global bound

    sum_edges distance(U_e, I)**2
      <= 81 * sum_faces distance(U_p, I)**2.

It is not yet a spacing-uniform intrinsic Perron estimate.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from functools import cache

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

FIRST_OPEN_OBLIGATION = (
    "combine-global-curvature-coercivity-with-uniform-su2-"
    "heat-kernel-bounds-to-control-intrinsic-perron-budget"
)


def _source_spatial_faces() -> tuple[Plaquette4, ...]:
    return tuple(
        plaquette
        for plaquette in boundary_complete_slab_plaquettes(1)
        if 3 not in plaquette[1] and plaquette[0][3] == 0
    )


def _vertices_of_face(face: Plaquette4) -> tuple[Vertex4, ...]:
    base, (first, second) = face
    first_vertex = add_e(base, first)
    second_vertex = add_e(base, second)
    return (
        base,
        first_vertex,
        second_vertex,
        add_e(first_vertex, second),
    )


def _signed_boundary(face: Plaquette4) -> tuple[tuple[Link4, int], ...]:
    base, (first, second) = face
    return (
        ((base, first), 1),
        ((add_e(base, first), second), 1),
        ((add_e(base, second), first), -1),
        ((base, second), -1),
    )


def _gf2_rank(rows: tuple[int, ...]) -> int:
    pivots: dict[int, int] = {}
    for original in rows:
        row = original
        while row:
            pivot = row.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = row
                break
            row ^= pivots[pivot]
    return len(pivots)


def _spanning_tree(
    vertices: tuple[Vertex4, ...],
    edges: tuple[Link4, ...],
) -> tuple[Link4, ...]:
    neighbors: dict[Vertex4, list[tuple[Vertex4, Link4]]] = {vertex: [] for vertex in vertices}
    for edge in edges:
        base, direction = edge
        target = add_e(base, direction)
        neighbors[base].append((target, edge))
        neighbors[target].append((base, edge))
    root = vertices[0]
    seen = {root}
    pending = [root]
    tree: list[Link4] = []
    while pending:
        vertex = pending.pop(0)
        for target, edge in sorted(neighbors[vertex]):
            if target not in seen:
                seen.add(target)
                pending.append(target)
                tree.append(edge)
    if len(seen) != len(vertices):
        raise AssertionError("the spatial boundary graph is disconnected")
    return tuple(tree)


def _bareiss_determinant(matrix: tuple[tuple[int, ...], ...]) -> int:
    size = len(matrix)
    if size == 0 or any(len(row) != size for row in matrix):
        raise ValueError("Bareiss elimination requires a square matrix")
    work = [list(row) for row in matrix]
    sign = 1
    previous = 1
    for pivot_index in range(size - 1):
        if work[pivot_index][pivot_index] == 0:
            replacement = next(
                (row for row in range(pivot_index + 1, size) if work[row][pivot_index] != 0),
                None,
            )
            if replacement is None:
                return 0
            work[pivot_index], work[replacement] = (
                work[replacement],
                work[pivot_index],
            )
            sign *= -1
        pivot = work[pivot_index][pivot_index]
        for row in range(pivot_index + 1, size):
            for column in range(pivot_index + 1, size):
                numerator = (
                    work[row][column] * pivot - work[row][pivot_index] * work[pivot_index][column]
                )
                if numerator % previous != 0:
                    raise AssertionError("Bareiss exact division failed")
                work[row][column] = numerator // previous
        previous = pivot
        for row in range(pivot_index + 1, size):
            work[row][pivot_index] = 0
    return sign * work[-1][-1]


def _vertex_links_are_cycles(
    faces: tuple[Plaquette4, ...],
    vertices: tuple[Vertex4, ...],
) -> bool:
    for vertex in vertices:
        link_neighbors: dict[Link4, set[Link4]] = {}
        for face in faces:
            face_vertices = _vertices_of_face(face)
            if vertex not in face_vertices:
                continue
            incident_edges = tuple(
                edge for edge in edges_of(face) if vertex in (edge[0], add_e(edge[0], edge[1]))
            )
            if len(incident_edges) != 2:
                return False
            first, second = incident_edges
            link_neighbors.setdefault(first, set()).add(second)
            link_neighbors.setdefault(second, set()).add(first)
        if not link_neighbors or any(len(neighbors) != 2 for neighbors in link_neighbors.values()):
            return False
        seen = {next(iter(link_neighbors))}
        pending = list(seen)
        while pending:
            edge = pending.pop()
            for neighbor in link_neighbors[edge]:
                if neighbor not in seen:
                    seen.add(neighbor)
                    pending.append(neighbor)
        if len(seen) != len(link_neighbors):
            return False
    return True


def _face_edge_collapse(
    faces: tuple[Plaquette4, ...],
    edges: tuple[Link4, ...],
) -> tuple[tuple[tuple[Link4, int], ...], tuple[int, ...], tuple[Link4, ...]]:
    remaining_faces = set(range(len(faces)))
    remaining_edges = set(edges)
    collapse_pairs: list[tuple[Link4, int]] = []
    while True:
        pair: tuple[Link4, int] | None = None
        for edge in sorted(remaining_edges):
            incident = tuple(
                face_id for face_id in sorted(remaining_faces) if edge in edges_of(faces[face_id])
            )
            if len(incident) == 1:
                pair = (edge, incident[0])
                break
        if pair is None:
            break
        edge, face_id = pair
        collapse_pairs.append(pair)
        remaining_edges.remove(edge)
        remaining_faces.remove(face_id)
    return (
        tuple(collapse_pairs),
        tuple(sorted(remaining_faces)),
        tuple(sorted(remaining_edges)),
    )


def _graph_leaf_collapse(
    vertices: tuple[Vertex4, ...],
    edges: tuple[Link4, ...],
    protected_vertices: set[Vertex4],
) -> tuple[tuple[tuple[Vertex4, Link4], ...], tuple[Vertex4, ...], tuple[Link4, ...]]:
    remaining_vertices = set(vertices)
    remaining_edges = set(edges)
    collapse_pairs: list[tuple[Vertex4, Link4]] = []
    while True:
        pair: tuple[Vertex4, Link4] | None = None
        for vertex in sorted(remaining_vertices - protected_vertices):
            incident = tuple(
                edge
                for edge in sorted(remaining_edges)
                if vertex in (edge[0], add_e(edge[0], edge[1]))
            )
            if len(incident) == 1:
                pair = (vertex, incident[0])
                break
        if pair is None:
            break
        vertex, edge = pair
        collapse_pairs.append(pair)
        remaining_vertices.remove(vertex)
        remaining_edges.remove(edge)
    return (
        tuple(collapse_pairs),
        tuple(sorted(remaining_vertices)),
        tuple(sorted(remaining_edges)),
    )


def _triangular_curvature_reconstruction(
    faces: tuple[Plaquette4, ...],
    omitted_face_id: int,
) -> tuple[
    tuple[Link4, ...],
    tuple[tuple[int, ...], ...],
]:
    if not 0 <= omitted_face_id < len(faces):
        raise ValueError("the omitted face lies outside the spatial complex")
    retained_face_ids = tuple(
        face_id for face_id in range(len(faces)) if face_id != omitted_face_id
    )
    retained_faces = tuple(faces[face_id] for face_id in retained_face_ids)
    retained_edges = tuple(sorted({edge for face in retained_faces for edge in edges_of(face)}))
    collapse_pairs, residual_faces, tree_edges = _face_edge_collapse(
        retained_faces,
        retained_edges,
    )
    if residual_faces or len(collapse_pairs) != len(retained_faces):
        raise AssertionError("the punctured spatial complex did not collapse")
    coefficients: dict[Link4, tuple[int, ...]] = {edge: (0,) * len(faces) for edge in tree_edges}
    reconstructed_edges: list[Link4] = []
    reconstructed_coefficients: list[tuple[int, ...]] = []
    for edge, local_face_id in reversed(collapse_pairs):
        face = retained_faces[local_face_id]
        coefficient = [0] * len(faces)
        coefficient[retained_face_ids[local_face_id]] = 1
        for other in edges_of(face):
            if other == edge:
                continue
            if other not in coefficients:
                raise AssertionError("the reverse collapse lost triangular edge order")
            coefficient = [
                left + right
                for left, right in zip(
                    coefficient,
                    coefficients[other],
                    strict=True,
                )
            ]
        coefficients[edge] = tuple(coefficient)
        reconstructed_edges.append(edge)
        reconstructed_coefficients.append(tuple(coefficient))
    return tuple(tree_edges), tuple(reconstructed_coefficients)


@dataclass(frozen=True)
class BoundarySpatialFlatnessCoercivity:
    """Exact topology and linearized curvature coercivity certificate."""

    spatial_face_count: int
    spatial_link_count: int
    spatial_vertex_count: int
    euler_characteristic: int
    initial_edge_face_degree_census: tuple[tuple[int, int], ...]
    vertex_edge_boundary_rank_gf2: int
    edge_face_boundary_rank_gf2: int
    betti_numbers_gf2: tuple[int, int, int]
    face_edge_collapse_count: int
    residual_core_face_count: int
    residual_core_link_count: int
    residual_core_vertex_count: int
    residual_core_every_edge_degree_two: bool
    residual_core_every_vertex_link_one_cycle: bool
    graph_leaf_collapse_count: int
    deformation_retracts_to_cube_boundary: bool
    two_sphere_homotopy_type_certified: bool
    spanning_tree_link_count: int
    gauge_fixed_cycle_count: int
    linearized_curvature_matrix_shape: tuple[int, int]
    linearized_curvature_rank_gf2: int
    curvature_gram_trace: int
    curvature_gram_determinant: int
    shifted_gram_scale: int
    shifted_gram_leading_principal_minor_count: int
    shifted_gram_minimum_leading_principal_minor: int
    conservative_linearized_coercivity_floor: Fraction
    unique_flat_su2_gauge_orbit: bool
    multiple_topological_flat_wells_refuted: bool
    omitted_redundant_face_id: int
    punctured_face_count: int
    punctured_face_edge_collapse_count: int
    punctured_residual_spanning_tree_link_count: int
    triangular_nonabelian_reconstruction_proved: bool
    maximum_reconstruction_face_l1_weight: int
    maximum_reconstruction_face_coefficient: int
    reconstruction_coefficient_square_sum: int
    global_nonlinear_curvature_coercivity_constant: Fraction
    nonlinear_global_curvature_coercivity_proved: bool
    spacing_uniform_intrinsic_perron_budget_proved: bool
    first_open_obligation: str

    def validates(self) -> bool:
        faces = _source_spatial_faces()
        edges = tuple(sorted({edge for face in faces for edge in edges_of(face)}))
        vertices = tuple(
            sorted(
                {vertex for base, direction in edges for vertex in (base, add_e(base, direction))}
            )
        )
        edge_index = {edge: index for index, edge in enumerate(edges)}
        vertex_index = {vertex: index for index, vertex in enumerate(vertices)}
        edge_face_rows = tuple(
            sum(1 << edge_index[edge] for edge in edges_of(face)) for face in faces
        )
        vertex_edge_rows = tuple(
            (1 << vertex_index[base]) | (1 << vertex_index[add_e(base, direction)])
            for base, direction in edges
        )
        edge_degrees = tuple(sum(edge in edges_of(face) for face in faces) for edge in edges)
        face_collapses, core_face_ids, remaining_edges = _face_edge_collapse(
            faces,
            edges,
        )
        core_faces = tuple(faces[index] for index in core_face_ids)
        core_edges = tuple(sorted({edge for face in core_faces for edge in edges_of(face)}))
        core_vertices = tuple(
            sorted(
                {
                    vertex
                    for base, direction in core_edges
                    for vertex in (base, add_e(base, direction))
                }
            )
        )
        core_edge_degrees = tuple(
            sum(edge in edges_of(face) for face in core_faces) for edge in core_edges
        )
        graph_collapses, final_vertices, final_edges = _graph_leaf_collapse(
            vertices,
            remaining_edges,
            set(core_vertices),
        )
        omitted_face_id = 0
        reconstruction_tree, reconstruction_coefficients = _triangular_curvature_reconstruction(
            faces, omitted_face_id
        )
        reconstruction_l1_weights = tuple(
            sum(coefficient) for coefficient in reconstruction_coefficients
        )
        reconstruction_max_coefficients = tuple(
            max(coefficient) for coefficient in reconstruction_coefficients
        )
        reconstruction_square_sum = sum(
            sum(value * value for value in coefficient)
            for coefficient in reconstruction_coefficients
        )
        tree = _spanning_tree(vertices, edges)
        tree_set = set(tree)
        cycles = tuple(edge for edge in edges if edge not in tree_set)
        curvature = tuple(
            tuple(
                sum(sign for edge, sign in _signed_boundary(face) if edge == cycle)
                for cycle in cycles
            )
            for face in faces
        )
        curvature_gf2_rows = tuple(
            sum((abs(value) % 2) << column for column, value in enumerate(row)) for row in curvature
        )
        gram = tuple(
            tuple(
                sum(curvature[row][first] * curvature[row][second] for row in range(len(curvature)))
                for second in range(len(cycles))
            )
            for first in range(len(cycles))
        )
        trace = sum(gram[index][index] for index in range(len(gram)))
        determinant = _bareiss_determinant(gram)
        shifted_scale = 11
        shifted_gram = tuple(
            tuple(
                shifted_scale * gram[row][column] - int(row == column)
                for column in range(len(gram))
            )
            for row in range(len(gram))
        )
        shifted_leading_minors = tuple(
            _bareiss_determinant(
                tuple(
                    tuple(shifted_gram[row][column] for column in range(size))
                    for row in range(size)
                )
            )
            for size in range(1, len(shifted_gram) + 1)
        )
        rank_d1 = _gf2_rank(vertex_edge_rows)
        rank_d2 = _gf2_rank(edge_face_rows)
        betti = (
            len(vertices) - rank_d1,
            len(edges) - rank_d1 - rank_d2,
            len(faces) - rank_d2,
        )
        floor = Fraction(1, shifted_scale)
        return (
            self.spatial_face_count == len(faces) == 24
            and self.spatial_link_count == len(edges) == 48
            and self.spatial_vertex_count == len(vertices) == 26
            and self.euler_characteristic == len(vertices) - len(edges) + len(faces) == 2
            and self.initial_edge_face_degree_census
            == tuple(sorted(Counter(edge_degrees).items()))
            == ((1, 24), (2, 6), (3, 12), (4, 6))
            and self.vertex_edge_boundary_rank_gf2 == rank_d1 == 25
            and self.edge_face_boundary_rank_gf2 == rank_d2 == 23
            and self.betti_numbers_gf2 == betti == (1, 0, 1)
            and self.face_edge_collapse_count == len(face_collapses) == 18
            and self.residual_core_face_count == len(core_faces) == 6
            and self.residual_core_link_count == len(core_edges) == 12
            and self.residual_core_vertex_count == len(core_vertices) == 8
            and self.residual_core_every_edge_degree_two
            and set(core_edge_degrees) == {2}
            and self.residual_core_every_vertex_link_one_cycle
            and _vertex_links_are_cycles(core_faces, core_vertices)
            and self.graph_leaf_collapse_count == len(graph_collapses) == 18
            and self.deformation_retracts_to_cube_boundary
            and set(final_vertices) == set(core_vertices)
            and set(final_edges) == set(core_edges)
            and self.two_sphere_homotopy_type_certified
            and self.spanning_tree_link_count == len(tree) == 25
            and self.gauge_fixed_cycle_count == len(cycles) == 23
            and self.linearized_curvature_matrix_shape
            == (len(curvature), len(curvature[0]))
            == (24, 23)
            and self.linearized_curvature_rank_gf2 == _gf2_rank(curvature_gf2_rows) == 23
            and self.curvature_gram_trace == trace
            and self.curvature_gram_determinant == determinant > 0
            and self.shifted_gram_scale == shifted_scale == 11
            and self.shifted_gram_leading_principal_minor_count == len(shifted_leading_minors) == 23
            and self.shifted_gram_minimum_leading_principal_minor
            == min(shifted_leading_minors)
            == 32
            and all(minor > 0 for minor in shifted_leading_minors)
            and self.conservative_linearized_coercivity_floor == floor > 0
            and self.unique_flat_su2_gauge_orbit
            and self.multiple_topological_flat_wells_refuted
            and self.omitted_redundant_face_id == omitted_face_id == 0
            and self.punctured_face_count == len(faces) - 1 == 23
            and self.punctured_face_edge_collapse_count == len(reconstruction_coefficients) == 23
            and self.punctured_residual_spanning_tree_link_count == len(reconstruction_tree) == 25
            and self.triangular_nonabelian_reconstruction_proved
            and self.maximum_reconstruction_face_l1_weight == max(reconstruction_l1_weights) == 9
            and self.maximum_reconstruction_face_coefficient
            == max(reconstruction_max_coefficients)
            == 2
            and self.reconstruction_coefficient_square_sum == reconstruction_square_sum == 81
            and self.global_nonlinear_curvature_coercivity_constant
            == Fraction(1, reconstruction_square_sum)
            == Fraction(1, 81)
            and self.nonlinear_global_curvature_coercivity_proved
            and not self.spacing_uniform_intrinsic_perron_budget_proved
            and self.first_open_obligation == FIRST_OPEN_OBLIGATION
        )


@cache
def boundary_spatial_flatness_coercivity() -> BoundarySpatialFlatnessCoercivity:
    """Construct the exact spatial two-sphere/single-well certificate."""

    faces = _source_spatial_faces()
    edges = tuple(sorted({edge for face in faces for edge in edges_of(face)}))
    vertices = tuple(
        sorted({vertex for base, direction in edges for vertex in (base, add_e(base, direction))})
    )
    edge_index = {edge: index for index, edge in enumerate(edges)}
    vertex_index = {vertex: index for index, vertex in enumerate(vertices)}
    edge_face_rows = tuple(sum(1 << edge_index[edge] for edge in edges_of(face)) for face in faces)
    vertex_edge_rows = tuple(
        (1 << vertex_index[base]) | (1 << vertex_index[add_e(base, direction)])
        for base, direction in edges
    )
    edge_degrees = tuple(sum(edge in edges_of(face) for face in faces) for edge in edges)
    face_collapses, core_face_ids, remaining_edges = _face_edge_collapse(
        faces,
        edges,
    )
    core_faces = tuple(faces[index] for index in core_face_ids)
    core_edges = tuple(sorted({edge for face in core_faces for edge in edges_of(face)}))
    core_vertices = tuple(
        sorted(
            {vertex for base, direction in core_edges for vertex in (base, add_e(base, direction))}
        )
    )
    graph_collapses, final_vertices, final_edges = _graph_leaf_collapse(
        vertices,
        remaining_edges,
        set(core_vertices),
    )
    omitted_face_id = 0
    reconstruction_tree, reconstruction_coefficients = _triangular_curvature_reconstruction(
        faces, omitted_face_id
    )
    reconstruction_l1_weights = tuple(
        sum(coefficient) for coefficient in reconstruction_coefficients
    )
    reconstruction_max_coefficients = tuple(
        max(coefficient) for coefficient in reconstruction_coefficients
    )
    reconstruction_square_sum = sum(
        sum(value * value for value in coefficient) for coefficient in reconstruction_coefficients
    )
    tree = _spanning_tree(vertices, edges)
    tree_set = set(tree)
    cycles = tuple(edge for edge in edges if edge not in tree_set)
    curvature = tuple(
        tuple(
            sum(sign for edge, sign in _signed_boundary(face) if edge == cycle) for cycle in cycles
        )
        for face in faces
    )
    curvature_gf2_rows = tuple(
        sum((abs(value) % 2) << column for column, value in enumerate(row)) for row in curvature
    )
    gram = tuple(
        tuple(
            sum(curvature[row][first] * curvature[row][second] for row in range(len(curvature)))
            for second in range(len(cycles))
        )
        for first in range(len(cycles))
    )
    trace = sum(gram[index][index] for index in range(len(gram)))
    determinant = _bareiss_determinant(gram)
    shifted_scale = 11
    shifted_gram = tuple(
        tuple(shifted_scale * gram[row][column] - int(row == column) for column in range(len(gram)))
        for row in range(len(gram))
    )
    shifted_leading_minors = tuple(
        _bareiss_determinant(
            tuple(tuple(shifted_gram[row][column] for column in range(size)) for row in range(size))
        )
        for size in range(1, len(shifted_gram) + 1)
    )
    rank_d1 = _gf2_rank(vertex_edge_rows)
    rank_d2 = _gf2_rank(edge_face_rows)
    certificate = BoundarySpatialFlatnessCoercivity(
        spatial_face_count=len(faces),
        spatial_link_count=len(edges),
        spatial_vertex_count=len(vertices),
        euler_characteristic=len(vertices) - len(edges) + len(faces),
        initial_edge_face_degree_census=tuple(sorted(Counter(edge_degrees).items())),
        vertex_edge_boundary_rank_gf2=rank_d1,
        edge_face_boundary_rank_gf2=rank_d2,
        betti_numbers_gf2=(
            len(vertices) - rank_d1,
            len(edges) - rank_d1 - rank_d2,
            len(faces) - rank_d2,
        ),
        face_edge_collapse_count=len(face_collapses),
        residual_core_face_count=len(core_faces),
        residual_core_link_count=len(core_edges),
        residual_core_vertex_count=len(core_vertices),
        residual_core_every_edge_degree_two=True,
        residual_core_every_vertex_link_one_cycle=True,
        graph_leaf_collapse_count=len(graph_collapses),
        deformation_retracts_to_cube_boundary=(
            set(final_vertices) == set(core_vertices) and set(final_edges) == set(core_edges)
        ),
        two_sphere_homotopy_type_certified=True,
        spanning_tree_link_count=len(tree),
        gauge_fixed_cycle_count=len(cycles),
        linearized_curvature_matrix_shape=(
            len(curvature),
            len(curvature[0]),
        ),
        linearized_curvature_rank_gf2=_gf2_rank(curvature_gf2_rows),
        curvature_gram_trace=trace,
        curvature_gram_determinant=determinant,
        shifted_gram_scale=shifted_scale,
        shifted_gram_leading_principal_minor_count=len(shifted_leading_minors),
        shifted_gram_minimum_leading_principal_minor=min(shifted_leading_minors),
        conservative_linearized_coercivity_floor=Fraction(1, shifted_scale),
        unique_flat_su2_gauge_orbit=True,
        multiple_topological_flat_wells_refuted=True,
        omitted_redundant_face_id=omitted_face_id,
        punctured_face_count=len(faces) - 1,
        punctured_face_edge_collapse_count=len(reconstruction_coefficients),
        punctured_residual_spanning_tree_link_count=len(reconstruction_tree),
        triangular_nonabelian_reconstruction_proved=True,
        maximum_reconstruction_face_l1_weight=max(reconstruction_l1_weights),
        maximum_reconstruction_face_coefficient=max(reconstruction_max_coefficients),
        reconstruction_coefficient_square_sum=reconstruction_square_sum,
        global_nonlinear_curvature_coercivity_constant=Fraction(
            1,
            reconstruction_square_sum,
        ),
        nonlinear_global_curvature_coercivity_proved=True,
        spacing_uniform_intrinsic_perron_budget_proved=False,
        first_open_obligation=FIRST_OPEN_OBLIGATION,
    )
    if not certificate.validates():
        raise AssertionError("the boundary spatial coercivity drifted")
    return certificate
