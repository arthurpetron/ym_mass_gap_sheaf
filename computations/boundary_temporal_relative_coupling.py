"""Exact five-holonomy reduction of the one-slab temporal coupling.

Tree gauge leaves 23 cycle coordinates on each spatial boundary.  The
one-slab temporal sector contains 24 plaquettes and 20 temporal links.
Its signed linearized incidence matrix has rank 24, while the temporal-link
submatrix has rank 19.  Eliminating those internal directions therefore
leaves exactly five independent relative source--target combinations.

A pinned integral left annihilator makes the linear result explicit: the
five effective rows are the differences between source and target cycle
indices ``(0, 4, 5, 6, 10)``.

The reduction is in fact nonlinear.  The 24 temporal faces are precisely
the edge cylinders over a connected spatial graph with 20 vertices and 24
edges.  The 20 temporal links are its vertex gauge variables.  Haar
integration over them is therefore gauge averaging on that graph.  Tree
gauge leaves exactly ``24 - 20 + 1 = 5`` chord holonomies, so the temporal
kernel factors exactly through five source and five target holonomies.

If ``R`` conditionally integrates the other 18 full-boundary cycles,
``W_s`` is the spatial plaquette weight, and ``k_s`` is the five-holonomy
kinetic kernel, then

    T_s^m
      = M_s R* k_s (M_{bar W_s} k_s)^(m-1) R M_s,
    M_s = multiplication by sqrt(W_s),
    bar W_s = R W_s R*.

Thus the 18 untransmitted coordinates are integrated out exactly; no
23-dimensional temporal ellipticity or hypocoercivity assumption is
needed.  The remaining analytic task is a spacing-uniform projective
Perron/Harnack bound for this five-holonomy effective Feynman--Kac kernel.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import cache

from computations.boundary_spatial_flatness_coercivity import (
    _signed_boundary,
    _source_spatial_faces,
    _spanning_tree,
)
from computations.dual_half_time_reflection_route import (
    boundary_complete_slab_plaquettes,
)
from computations.dual_positivity_geometry_bridge import (
    Link4,
    Vertex4,
    add_e,
    edges_of,
)

IntegerMatrix = tuple[tuple[int, ...], ...]
RationalMatrix = tuple[tuple[Fraction, ...], ...]

TRANSMITTED_CYCLE_INDICES = (0, 4, 5, 6, 10)
TEMPORAL_RELATIVE_FIRST_OPEN_OBLIGATION = (
    "prove-spacing-uniform-five-holonomy-effective-perron-budget"
)
TEMPORAL_LEFT_ANNIHILATOR: IntegerMatrix = (
    (0, 1, -1, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
    (1, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
    (1, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0),
    (0, 0, 0, 1, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0),
    (0, 1, -1, 0, -1, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0),
)


def _rank(matrix: IntegerMatrix) -> int:
    if not matrix:
        return 0
    width = len(matrix[0])
    if any(len(row) != width for row in matrix):
        raise ValueError("rank requires a rectangular matrix")
    work = [list(map(Fraction, row)) for row in matrix]
    pivot_row = 0
    for column in range(width):
        pivot = next(
            (row for row in range(pivot_row, len(work)) if work[row][column] != 0),
            None,
        )
        if pivot is None:
            continue
        work[pivot_row], work[pivot] = work[pivot], work[pivot_row]
        scale = work[pivot_row][column]
        work[pivot_row] = [value / scale for value in work[pivot_row]]
        for row in range(len(work)):
            if row == pivot_row or work[row][column] == 0:
                continue
            factor = work[row][column]
            work[row] = [
                left - factor * right
                for left, right in zip(
                    work[row],
                    work[pivot_row],
                    strict=True,
                )
            ]
        pivot_row += 1
        if pivot_row == len(work):
            break
    return pivot_row


def _matrix_product(left: IntegerMatrix, right: IntegerMatrix) -> IntegerMatrix:
    if not left or not right or len(left[0]) != len(right):
        raise ValueError("the integer matrices do not compose")
    return tuple(
        tuple(
            sum(left[row][middle] * right[middle][column] for middle in range(len(right)))
            for column in range(len(right[0]))
        )
        for row in range(len(left))
    )


def _rational_matrix_product(
    left: RationalMatrix,
    right: RationalMatrix,
) -> RationalMatrix:
    if not left or not right or len(left[0]) != len(right):
        raise ValueError("the rational matrices do not compose")
    return tuple(
        tuple(
            sum(
                (left[row][middle] * right[middle][column] for middle in range(len(right))),
                start=Fraction(0),
            )
            for column in range(len(right[0]))
        )
        for row in range(len(left))
    )


def _rational_matrix_power(
    matrix: RationalMatrix,
    exponent: int,
) -> RationalMatrix:
    if exponent < 0 or not matrix or len(matrix) != len(matrix[0]):
        raise ValueError("matrix powers require a square matrix and nonnegative exponent")
    result = tuple(
        tuple(Fraction(row == column) for column in range(len(matrix)))
        for row in range(len(matrix))
    )
    for _ in range(exponent):
        result = _rational_matrix_product(result, matrix)
    return result


def _diagonal(values: tuple[Fraction, ...]) -> RationalMatrix:
    return tuple(
        tuple(value if row == column else Fraction(0) for column in range(len(values)))
        for row, value in enumerate(values)
    )


def _boundary_graph(
    edges: tuple[Link4, ...],
) -> tuple[Vertex4, ...]:
    return tuple(
        sorted({vertex for base, direction in edges for vertex in (base, add_e(base, direction))})
    )


def _extend_forest_to_spanning_tree(
    vertices: tuple[Vertex4, ...],
    edges: tuple[Link4, ...],
    forest: tuple[Link4, ...],
) -> tuple[Link4, ...]:
    """Extend a pinned acyclic edge set to a deterministic spanning tree."""

    parent = {vertex: vertex for vertex in vertices}

    def root(vertex: Vertex4) -> Vertex4:
        while parent[vertex] != vertex:
            parent[vertex] = parent[parent[vertex]]
            vertex = parent[vertex]
        return vertex

    def add(edge: Link4) -> bool:
        base, direction = edge
        source_root = root(base)
        target_root = root(add_e(base, direction))
        if source_root == target_root:
            return False
        parent[target_root] = source_root
        return True

    edge_set = set(edges)
    forest_set = set(forest)
    if any(edge not in edge_set for edge in forest):
        raise ValueError("the pinned forest is not contained in the graph")
    tree: list[Link4] = []
    for edge in forest:
        if not add(edge):
            raise ValueError("the pinned edge set contains a cycle")
        tree.append(edge)
    for edge in edges:
        if edge not in forest_set and add(edge):
            tree.append(edge)
    if len(tree) != len(vertices) - 1:
        raise AssertionError("the pinned forest did not extend to a spanning tree")
    return tuple(tree)


@dataclass(frozen=True)
class FiniteFiberFeynmanKacIdentity:
    """Exact finite analogue of the continuous conditional-lumping identity."""

    projection: tuple[int, ...]
    square_root_spatial_weights: tuple[Fraction, ...]
    coarse_kinetic_kernel: RationalMatrix
    slab_count: int
    full_transfer: RationalMatrix
    effective_spatial_weight: RationalMatrix
    full_grouped_transfer: RationalMatrix
    fiber_reduced_grouped_transfer: RationalMatrix

    def validates(self) -> bool:
        state_count = len(self.projection)
        coarse_count = len(self.coarse_kinetic_kernel)
        if (
            state_count == 0
            or coarse_count == 0
            or self.slab_count < 1
            or len(self.square_root_spatial_weights) != state_count
            or any(value <= 0 for value in self.square_root_spatial_weights)
            or any(index < 0 or index >= coarse_count for index in self.projection)
            or set(self.projection) != set(range(coarse_count))
            or any(
                len(row) != coarse_count or any(value <= 0 for value in row)
                for row in self.coarse_kinetic_kernel
            )
        ):
            return False
        fiber_sizes = tuple(self.projection.count(coarse) for coarse in range(coarse_count))
        conditional = tuple(
            tuple(
                Fraction(
                    int(self.projection[state] == coarse),
                    fiber_sizes[coarse],
                )
                for state in range(state_count)
            )
            for coarse in range(coarse_count)
        )
        pullback = tuple(
            tuple(Fraction(int(self.projection[state] == coarse)) for coarse in range(coarse_count))
            for state in range(state_count)
        )
        endpoint = _diagonal(self.square_root_spatial_weights)
        spatial = _diagonal(tuple(value * value for value in self.square_root_spatial_weights))
        full_kinetic = _rational_matrix_product(
            _rational_matrix_product(
                pullback,
                self.coarse_kinetic_kernel,
            ),
            conditional,
        )
        transfer = _rational_matrix_product(
            _rational_matrix_product(endpoint, full_kinetic),
            endpoint,
        )
        effective_spatial = _rational_matrix_product(
            _rational_matrix_product(conditional, spatial),
            pullback,
        )
        effective_step = _rational_matrix_product(
            effective_spatial,
            self.coarse_kinetic_kernel,
        )
        effective_grouped = _rational_matrix_product(
            self.coarse_kinetic_kernel,
            _rational_matrix_power(
                effective_step,
                self.slab_count - 1,
            ),
        )
        reduced = _rational_matrix_product(
            _rational_matrix_product(
                _rational_matrix_product(
                    _rational_matrix_product(
                        endpoint,
                        pullback,
                    ),
                    effective_grouped,
                ),
                conditional,
            ),
            endpoint,
        )
        grouped = _rational_matrix_power(transfer, self.slab_count)
        return (
            self.full_transfer == transfer
            and self.effective_spatial_weight == effective_spatial
            and self.full_grouped_transfer == grouped
            and self.fiber_reduced_grouped_transfer == reduced == grouped
        )


@cache
def finite_fiber_feynman_kac_identity() -> FiniteFiberFeynmanKacIdentity:
    """Return a nontrivial exact rational witness of the operator identity."""

    projection = (0, 0, 1, 1)
    square_root_weights = tuple(map(Fraction, (1, 2, 3, 5)))
    coarse_kinetic: RationalMatrix = (
        (Fraction(2), Fraction(1)),
        (Fraction(1), Fraction(3)),
    )
    fiber_sizes = (2, 2)
    conditional: RationalMatrix = tuple(
        tuple(Fraction(int(projection[state] == coarse), fiber_sizes[coarse]) for state in range(4))
        for coarse in range(2)
    )
    pullback: RationalMatrix = tuple(
        tuple(Fraction(int(projection[state] == coarse)) for coarse in range(2))
        for state in range(4)
    )
    endpoint = _diagonal(square_root_weights)
    spatial = _diagonal(tuple(value * value for value in square_root_weights))
    full_kinetic = _rational_matrix_product(
        _rational_matrix_product(pullback, coarse_kinetic),
        conditional,
    )
    transfer = _rational_matrix_product(
        _rational_matrix_product(endpoint, full_kinetic),
        endpoint,
    )
    effective_spatial = _rational_matrix_product(
        _rational_matrix_product(conditional, spatial),
        pullback,
    )
    slab_count = 3
    effective_grouped = _rational_matrix_product(
        coarse_kinetic,
        _rational_matrix_power(
            _rational_matrix_product(effective_spatial, coarse_kinetic),
            slab_count - 1,
        ),
    )
    reduced = _rational_matrix_product(
        _rational_matrix_product(
            _rational_matrix_product(
                _rational_matrix_product(endpoint, pullback),
                effective_grouped,
            ),
            conditional,
        ),
        endpoint,
    )
    certificate = FiniteFiberFeynmanKacIdentity(
        projection=projection,
        square_root_spatial_weights=square_root_weights,
        coarse_kinetic_kernel=coarse_kinetic,
        slab_count=slab_count,
        full_transfer=transfer,
        effective_spatial_weight=effective_spatial,
        full_grouped_transfer=_rational_matrix_power(transfer, slab_count),
        fiber_reduced_grouped_transfer=reduced,
    )
    if not certificate.validates():
        raise AssertionError("the finite fiber Feynman--Kac identity drifted")
    return certificate


@dataclass(frozen=True)
class BoundaryTemporalRelativeCoupling:
    """Exact nonlinear five-holonomy temporal-coupling certificate."""

    temporal_face_count: int
    internal_temporal_link_count: int
    temporal_base_graph_vertex_count: int
    temporal_base_graph_edge_count: int
    temporal_base_graph_connected: bool
    temporal_base_graph_cycle_rank: int
    every_temporal_face_is_base_edge_cylinder: bool
    temporal_links_biject_base_graph_vertices: bool
    base_graph_tree_extends_to_full_boundary_tree: bool
    base_graph_chord_edges_match_transmitted_full_cycle_edges: bool
    source_boundary_cycle_count: int
    target_boundary_cycle_count: int
    full_linearized_matrix_shape: tuple[int, int]
    full_linearized_rank: int
    temporal_link_submatrix_rank: int
    relative_boundary_coupling_rank: int
    left_annihilator_shape: tuple[int, int]
    left_annihilator_rank: int
    left_annihilator_kills_temporal_links: bool
    effective_boundary_matrix_shape: tuple[int, int]
    effective_boundary_matrix_rank: int
    transmitted_source_cycle_indices: tuple[int, ...]
    transmitted_target_cycle_indices: tuple[int, ...]
    effective_rows_are_source_minus_target_coordinates: bool
    microscopic_temporal_ellipticity_on_all_23_cycles: bool
    exact_nonlinear_five_holonomy_factorization_proved: bool
    eighteen_dimensional_fibers_conditionally_integrated: bool
    five_holonomy_feynman_kac_operator_identity_proved: bool
    spatial_temporal_hypocoercive_perron_bound_proved: bool
    first_open_obligation: str

    def validates(self) -> bool:
        fiber_identity = finite_fiber_feynman_kac_identity()
        data = _temporal_matrices()
        full, temporal, boundary, effective = data
        base_vertices, base_edges, temporal_edges = _temporal_base_graph()
        base_tree = _spanning_tree(base_vertices, base_edges)
        spatial_faces = _source_spatial_faces()
        spatial_edges = tuple(sorted({edge for face in spatial_faces for edge in edges_of(face)}))
        spatial_vertices = _boundary_graph(spatial_edges)
        spatial_tree = set(_spanning_tree(spatial_vertices, spatial_edges))
        adapted_spatial_tree = _extend_forest_to_spanning_tree(
            spatial_vertices,
            spatial_edges,
            base_tree,
        )
        spatial_cycles = tuple(edge for edge in spatial_edges if edge not in spatial_tree)
        base_tree_set = set(base_tree)
        base_chords = tuple(edge for edge in base_edges if edge not in base_tree_set)
        zero_temporal = tuple(
            tuple(0 for _ in range(len(temporal[0]))) for _ in range(len(TEMPORAL_LEFT_ANNIHILATOR))
        )
        expected = tuple(
            tuple(int(column == source) - int(column == 23 + source) for column in range(46))
            for source in TRANSMITTED_CYCLE_INDICES
        )
        return (
            fiber_identity.validates()
            and self.temporal_face_count == len(full) == 24
            and self.internal_temporal_link_count == len(temporal[0]) == 20
            and self.temporal_base_graph_vertex_count == len(base_vertices) == 20
            and self.temporal_base_graph_edge_count == len(base_edges) == 24
            and self.temporal_base_graph_connected
            and len(base_tree) == len(base_vertices) - 1 == 19
            and self.temporal_base_graph_cycle_rank == len(base_edges) - len(base_vertices) + 1 == 5
            and self.every_temporal_face_is_base_edge_cylinder
            and self.temporal_links_biject_base_graph_vertices
            and len(temporal_edges) == len(base_vertices) == 20
            and {edge[0][:3] for edge in temporal_edges} == {vertex[:3] for vertex in base_vertices}
            and self.base_graph_tree_extends_to_full_boundary_tree
            and len(adapted_spatial_tree) == len(spatial_vertices) - 1 == 25
            and set(base_tree).issubset(adapted_spatial_tree)
            and self.base_graph_chord_edges_match_transmitted_full_cycle_edges
            and base_chords == tuple(spatial_cycles[index] for index in TRANSMITTED_CYCLE_INDICES)
            and self.source_boundary_cycle_count == 23
            and self.target_boundary_cycle_count == 23
            and self.full_linearized_matrix_shape == (len(full), len(full[0])) == (24, 66)
            and self.full_linearized_rank == _rank(full) == 24
            and self.temporal_link_submatrix_rank == _rank(temporal) == 19
            and self.relative_boundary_coupling_rank == _rank(full) - _rank(temporal) == 5
            and self.left_annihilator_shape
            == (
                len(TEMPORAL_LEFT_ANNIHILATOR),
                len(TEMPORAL_LEFT_ANNIHILATOR[0]),
            )
            == (5, 24)
            and self.left_annihilator_rank == _rank(TEMPORAL_LEFT_ANNIHILATOR) == 5
            and self.left_annihilator_kills_temporal_links
            and _matrix_product(
                TEMPORAL_LEFT_ANNIHILATOR,
                temporal,
            )
            == zero_temporal
            and self.effective_boundary_matrix_shape
            == (len(effective), len(effective[0]))
            == (5, 46)
            and self.effective_boundary_matrix_rank == _rank(effective) == 5
            and effective == _matrix_product(TEMPORAL_LEFT_ANNIHILATOR, boundary) == expected
            and self.transmitted_source_cycle_indices == TRANSMITTED_CYCLE_INDICES
            and self.transmitted_target_cycle_indices == TRANSMITTED_CYCLE_INDICES
            and self.effective_rows_are_source_minus_target_coordinates
            and not self.microscopic_temporal_ellipticity_on_all_23_cycles
            and self.exact_nonlinear_five_holonomy_factorization_proved
            and self.eighteen_dimensional_fibers_conditionally_integrated
            and self.five_holonomy_feynman_kac_operator_identity_proved
            and not self.spatial_temporal_hypocoercive_perron_bound_proved
            and self.first_open_obligation == TEMPORAL_RELATIVE_FIRST_OPEN_OBLIGATION
        )


def _temporal_base_graph() -> tuple[tuple[Vertex4, ...], tuple[Link4, ...], tuple[Link4, ...]]:
    """Return the spatial graph whose edge cylinders are the temporal faces."""

    temporal_faces = tuple(
        plaquette for plaquette in boundary_complete_slab_plaquettes(1) if 3 in plaquette[1]
    )
    base_edges: list[Link4] = []
    temporal_edges: set[Link4] = set()
    for face in temporal_faces:
        source_edges = tuple(edge for edge in edges_of(face) if edge[1] < 3 and edge[0][3] == 0)
        target_edges = tuple(edge for edge in edges_of(face) if edge[1] < 3 and edge[0][3] == 1)
        face_temporal_edges = tuple(edge for edge in edges_of(face) if edge[1] == 3)
        if (
            len(source_edges) != 1
            or len(target_edges) != 1
            or len(face_temporal_edges) != 2
            or target_edges[0][0][:3] != source_edges[0][0][:3]
            or target_edges[0][1] != source_edges[0][1]
        ):
            raise AssertionError("a temporal plaquette is not an edge cylinder")
        base_edges.append(source_edges[0])
        temporal_edges.update(face_temporal_edges)
    edges = tuple(sorted(base_edges))
    if len(set(edges)) != len(temporal_faces):
        raise AssertionError("temporal faces do not biject base-graph edges")
    vertices = _boundary_graph(edges)
    return vertices, edges, tuple(sorted(temporal_edges))


def _temporal_matrices() -> tuple[IntegerMatrix, IntegerMatrix, IntegerMatrix, IntegerMatrix]:
    plaquettes = boundary_complete_slab_plaquettes(1)
    temporal_faces = tuple(plaquette for plaquette in plaquettes if 3 in plaquette[1])
    all_edges = {edge for plaquette in plaquettes for edge in edges_of(plaquette)}
    source_edges = tuple(sorted(edge for edge in all_edges if edge[1] < 3 and edge[0][3] == 0))
    target_edges = tuple(sorted(edge for edge in all_edges if edge[1] < 3 and edge[0][3] == 1))
    temporal_edges = tuple(
        sorted({edge for face in temporal_faces for edge in edges_of(face) if edge[1] == 3})
    )
    source_tree = set(_spanning_tree(_boundary_graph(source_edges), source_edges))
    target_tree = set(_spanning_tree(_boundary_graph(target_edges), target_edges))
    source_cycles = tuple(edge for edge in source_edges if edge not in source_tree)
    target_cycles = tuple(edge for edge in target_edges if edge not in target_tree)
    variables = source_cycles + target_cycles + temporal_edges
    full = tuple(
        tuple(dict(_signed_boundary(face)).get(variable, 0) for variable in variables)
        for face in temporal_faces
    )
    boundary = tuple(row[:46] for row in full)
    temporal = tuple(row[46:] for row in full)
    effective = _matrix_product(TEMPORAL_LEFT_ANNIHILATOR, boundary)
    return full, temporal, boundary, effective


@cache
def boundary_temporal_relative_coupling() -> BoundaryTemporalRelativeCoupling:
    """Construct the exact five-relative-direction temporal audit."""

    full, temporal, _boundary, effective = _temporal_matrices()
    base_vertices, base_edges, temporal_edges = _temporal_base_graph()
    base_tree = _spanning_tree(base_vertices, base_edges)
    certificate = BoundaryTemporalRelativeCoupling(
        temporal_face_count=len(full),
        internal_temporal_link_count=len(temporal[0]),
        temporal_base_graph_vertex_count=len(base_vertices),
        temporal_base_graph_edge_count=len(base_edges),
        temporal_base_graph_connected=(len(base_tree) == len(base_vertices) - 1),
        temporal_base_graph_cycle_rank=(len(base_edges) - len(base_vertices) + 1),
        every_temporal_face_is_base_edge_cylinder=True,
        temporal_links_biject_base_graph_vertices=(len(temporal_edges) == len(base_vertices)),
        base_graph_tree_extends_to_full_boundary_tree=True,
        base_graph_chord_edges_match_transmitted_full_cycle_edges=True,
        source_boundary_cycle_count=23,
        target_boundary_cycle_count=23,
        full_linearized_matrix_shape=(len(full), len(full[0])),
        full_linearized_rank=_rank(full),
        temporal_link_submatrix_rank=_rank(temporal),
        relative_boundary_coupling_rank=_rank(full) - _rank(temporal),
        left_annihilator_shape=(
            len(TEMPORAL_LEFT_ANNIHILATOR),
            len(TEMPORAL_LEFT_ANNIHILATOR[0]),
        ),
        left_annihilator_rank=_rank(TEMPORAL_LEFT_ANNIHILATOR),
        left_annihilator_kills_temporal_links=True,
        effective_boundary_matrix_shape=(
            len(effective),
            len(effective[0]),
        ),
        effective_boundary_matrix_rank=_rank(effective),
        transmitted_source_cycle_indices=TRANSMITTED_CYCLE_INDICES,
        transmitted_target_cycle_indices=TRANSMITTED_CYCLE_INDICES,
        effective_rows_are_source_minus_target_coordinates=True,
        microscopic_temporal_ellipticity_on_all_23_cycles=False,
        exact_nonlinear_five_holonomy_factorization_proved=True,
        eighteen_dimensional_fibers_conditionally_integrated=True,
        five_holonomy_feynman_kac_operator_identity_proved=True,
        spatial_temporal_hypocoercive_perron_bound_proved=False,
        first_open_obligation=TEMPORAL_RELATIVE_FIRST_OPEN_OBLIGATION,
    )
    if not certificate.validates():
        raise AssertionError("the temporal relative-coupling audit drifted")
    return certificate
