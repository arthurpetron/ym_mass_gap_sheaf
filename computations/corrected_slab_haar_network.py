"""Exact Haar-network amplitudes on the corrected reflection slab.

This is the executable physical counterpart of the Lean corrected-slab face
enumeration.  It builds one connected oriented link complex from
``boundary_complete_slab_plaquettes``, gauge-fixes a spanning tree, and sends
the literal plaquette characters to the exact quaternion Haar integrator.

Unlike the multiplicity-product slab law, the resulting fixed-face
coefficient includes every vertex/intertwiner contraction and can be signed.
The extent-one slab contains the boundary two-skeleton of the unit four-cube;
the pinned negative cutoff-two assignment therefore gives a same-geometry
semantic witness rather than a comparison to an unrelated complex.
"""

from __future__ import annotations

from fractions import Fraction
from typing import Sequence

from computations.core_b_pilot import coeff_w
from computations.dual_half_time_reflection_route import (
    boundary_complete_slab_plaquettes,
)
from computations.dual_positivity_geometry_bridge import (
    Link4,
    Plaquette4,
    Vertex4,
    add_e,
)
from computations.exact_haar_network import (
    P_ONE,
    GaugeFixedComplex,
    SPoly,
    chi,
    invariant_multiplicity,
)
from computations.hypercube4d_survey import (
    decode_assignment,
    exact_constant,
    hypercube,
)


OrientedFace = list[tuple[int, int]]


def corrected_slab_haar_complex(
    extent: int,
) -> tuple[GaugeFixedComplex, tuple[OrientedFace, ...], tuple[Plaquette4, ...]]:
    """Build the exact oriented two-complex of the corrected slab."""

    plaquettes = boundary_complete_slab_plaquettes(extent)
    vertices: set[Vertex4] = set()
    geometric_edges: set[Link4] = set()
    for base, (first, second) in plaquettes:
        first_vertex = add_e(base, first)
        second_vertex = add_e(base, second)
        diagonal = add_e(first_vertex, second)
        vertices.update((base, first_vertex, second_vertex, diagonal))
        geometric_edges.update(
            (
                (base, first),
                (first_vertex, second),
                (second_vertex, first),
                (base, second),
            )
        )

    ordered_vertices = tuple(sorted(vertices))
    vertex_ids = {
        vertex: index for index, vertex in enumerate(ordered_vertices)
    }
    ordered_edges = tuple(sorted(geometric_edges))
    edge_ids = {edge: index for index, edge in enumerate(ordered_edges)}
    graph_edges = tuple(
        (
            vertex_ids[base],
            vertex_ids[add_e(base, direction)],
        )
        for base, direction in ordered_edges
    )

    oriented_faces: list[OrientedFace] = []
    for base, (first, second) in plaquettes:
        first_vertex = add_e(base, first)
        second_vertex = add_e(base, second)
        oriented_faces.append(
            [
                (edge_ids[(base, first)], 1),
                (edge_ids[(first_vertex, second)], 1),
                (edge_ids[(second_vertex, first)], -1),
                (edge_ids[(base, second)], -1),
            ]
        )
    return (
        GaugeFixedComplex(len(ordered_vertices), graph_edges),
        tuple(oriented_faces),
        plaquettes,
    )


def evaluate_corrected_slab_assignment(
    extent: int,
    spins: Sequence[int],
) -> SPoly:
    """Evaluate one fixed-face corrected-slab coefficient exactly."""

    complex_, faces, _plaquettes = corrected_slab_haar_complex(extent)
    if len(spins) != len(faces):
        raise ValueError(
            f"one spin per slab face is required: expected {len(faces)}, "
            f"got {len(spins)}"
        )
    if any(spin < 0 for spin in spins):
        raise ValueError("doubled spins must be nonnegative")
    factors = [
        chi(spin, complex_.holonomy_of(face))
        for spin, face in zip(spins, faces, strict=True)
        if spin
    ]
    return complex_.contract_invariant(factors or [dict(P_ONE)])


def evaluate_corrected_slab_surface_pair(
    extent: int,
    left: int,
    right: int,
    *,
    label: int = 1,
) -> SPoly:
    """Evaluate two surface strands without preselecting overlap channels."""

    complex_, faces, _plaquettes = corrected_slab_haar_complex(extent)
    if (
        left < 0
        or right < 0
        or (left | right) >> len(faces)
        or label < 0
    ):
        raise ValueError("surface pair leaves the slab face carrier")
    factors = [
        chi(label, complex_.holonomy_of(face))
        for mask in (left, right)
        for face_index, face in enumerate(faces)
        if (mask >> face_index) & 1
    ]
    return complex_.contract_invariant(factors or [dict(P_ONE)])


def corrected_slab_edge_multiplicities(
    extent: int,
    spins: Sequence[int],
) -> tuple[int, ...]:
    """Local invariant-space dimensions on the same oriented slab complex."""

    complex_, faces, _plaquettes = corrected_slab_haar_complex(extent)
    if len(spins) != len(faces):
        raise ValueError("one spin per slab face is required")
    return tuple(
        invariant_multiplicity(
            tuple(
                spins[face_index]
                for face_index, face in enumerate(faces)
                if any(face_edge == edge for face_edge, _orientation in face)
            )
        )
        for edge in range(len(complex_.edges))
    )


def corrected_slab_fixed_face_dual_term(
    extent: int,
    cutoff: int,
    coupling: Fraction,
    spins: Sequence[int],
) -> Fraction:
    """Heat-weighted exact fixed-face dual coefficient."""

    if cutoff < 0 or coupling < 0:
        raise ValueError("cutoff and coupling must be nonnegative")
    if any(spin > cutoff for spin in spins):
        raise ValueError("spin assignment exceeds the physical cutoff")
    amplitude = exact_constant(
        evaluate_corrected_slab_assignment(extent, spins)
    )
    face_weight = Fraction(1)
    for spin in spins:
        face_weight *= Fraction(coeff_w(coupling, spin))
    return amplitude * face_weight


def embedded_negative_hypercube_assignment() -> tuple[int, ...]:
    """Embed the pinned negative four-cube channel in the extent-one slab."""

    _hypercube_complex, _hypercube_faces, hypercube_meta = hypercube()
    hypercube_spins = decode_assignment((0x6F6D9E, 0x21))
    spin_by_face = {
        (tuple(point), (first, second)): spin
        for (point, first, second), spin in zip(
            hypercube_meta, hypercube_spins, strict=True
        )
    }
    _slab_complex, _slab_faces, slab_plaquettes = (
        corrected_slab_haar_complex(1)
    )
    if not set(spin_by_face).issubset(set(slab_plaquettes)):
        raise AssertionError("the unit four-cube left the corrected slab")
    return tuple(spin_by_face.get(plaquette, 0) for plaquette in slab_plaquettes)


def embed_hypercube_face_mask(mask: int) -> int:
    """Embed a unit-four-cube face mask in the extent-one slab ordering."""

    _hypercube_complex, hypercube_faces, hypercube_meta = hypercube()
    if mask < 0 or mask >> len(hypercube_faces):
        raise ValueError("mask leaves the unit four-cube")
    selected = {
        (tuple(point), (first, second))
        for face_index, (point, first, second) in enumerate(hypercube_meta)
        if (mask >> face_index) & 1
    }
    _slab_complex, _slab_faces, slab_plaquettes = (
        corrected_slab_haar_complex(1)
    )
    if not selected.issubset(set(slab_plaquettes)):
        raise AssertionError("selected hypercube face left the corrected slab")
    return sum(
        1 << face_index
        for face_index, plaquette in enumerate(slab_plaquettes)
        if plaquette in selected
    )


def embedded_negative_channel_surface_pair() -> tuple[int, int]:
    """The complete surface pair whose fusion ledger contains the negative channel."""

    return embed_hypercube_face_mask(0x4AB33), embed_hypercube_face_mask(0x6BC6AD)


if __name__ == "__main__":
    embedded = embedded_negative_hypercube_assignment()
    print(exact_constant(evaluate_corrected_slab_assignment(1, embedded)))
