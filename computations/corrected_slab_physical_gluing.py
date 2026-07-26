"""Exact two-slab gluing geometry and its interface-order obstruction.

The production ``boundary_complete_slab_plaquettes(1)`` has 72 faces.  To
glue two such slabs at fixed spatial size, translate the second copy by one
unit in time and identify the common time-one boundary.  The two copies
share 24 spatial plaquettes, 48 spatial links and 26 boundary vertices.
Their union therefore has 120 faces, 184 links and 78 vertices.

This fixed-spatial two-step slab is not
``boundary_complete_slab_plaquettes(2)``: that legacy parameter enlarges the
three spatial directions together with time and produces 405 faces.  A
physical consecutive-scale constructor must use the rectangular union
defined here rather than silently changing spatial volume.

If ``W_lower`` and ``W_upper`` are the full one-slab heat-kernel densities
on the identified variables, their product counts every shared spatial
plaquette twice.  The physical glued density counts it once:

    W_lower W_upper = W_glued W_interface,

where ``W_interface`` is the product of the 24 shared heat kernels.  Thus
ordinary independent convolution is not the physical gluing law.  It is a
boundary fiber product followed by an interface correction and a new
partition normalization.

A worst-holonomy correction repeats the previous failure.  If one bounds
the interface by one-plaquette floor and ceiling, the normalized comparison
coefficient is ``(ell_s/H_s)**24``.  On ``s=1-a`` it is at most ``a**72``.
This rejects a second naive route while leaving a direct integrated
relative-order estimate on the complete 120-face glued object open.
"""

from __future__ import annotations

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
from computations.physical_all_label_choi_domination import (
    physical_all_label_choi_domination,
)


def _translate_time_plaquette(
    plaquette: Plaquette4,
    amount: int,
) -> Plaquette4:
    base, plane = plaquette
    return (
        (base[0], base[1], base[2], base[3] + amount),
        plane,
    )


def _edge_set(plaquettes: tuple[Plaquette4, ...]) -> set[Link4]:
    return {
        edge
        for plaquette in plaquettes
        for edge in edges_of(plaquette)
    }


def _vertex_set(edges: set[Link4]) -> set[Vertex4]:
    return {
        vertex
        for base, direction in edges
        for vertex in (base, add_e(base, direction))
    }


@cache
def fixed_spatial_two_step_slab_plaquettes() -> tuple[Plaquette4, ...]:
    """Return the exact 120-face union of two adjacent extent-one slabs."""

    lower = boundary_complete_slab_plaquettes(1)
    upper = tuple(
        _translate_time_plaquette(plaquette, 1)
        for plaquette in lower
    )
    return tuple(sorted(set(lower) | set(upper)))


@dataclass(frozen=True)
class TwoSlabPhysicalGluingAudit:
    """Exact face/link/vertex fiber-product census."""

    one_slab_face_count: int
    lower_face_count: int
    upper_face_count: int
    shared_interface_face_count: int
    glued_face_count: int
    isotropic_extent_two_face_count: int
    one_slab_link_count: int
    shared_interface_link_count: int
    glued_link_count: int
    one_slab_vertex_count: int
    shared_interface_vertex_count: int
    glued_vertex_count: int
    shared_faces_all_spatial_at_time_one: bool
    shared_links_all_spatial_at_time_one: bool
    fixed_spatial_union_is_not_isotropic_extent_two: bool
    lower_upper_variables_identified_on_interface: bool
    product_density_interface_multiplicity: int
    physical_density_interface_multiplicity: int
    exact_unnormalized_density_correction: str
    independent_probability_convolution_is_physical_gluing: bool
    boundary_fiber_product_required: bool
    new_partition_normalization_required: bool
    physical_channel_gluing_identity_proved: bool
    first_open_obligation: str

    def validates(self) -> bool:
        lower = boundary_complete_slab_plaquettes(1)
        upper = tuple(
            _translate_time_plaquette(plaquette, 1)
            for plaquette in lower
        )
        lower_set = set(lower)
        upper_set = set(upper)
        shared = lower_set & upper_set
        glued = lower_set | upper_set
        isotropic_extent_two = set(boundary_complete_slab_plaquettes(2))
        lower_edges = _edge_set(lower)
        upper_edges = _edge_set(upper)
        shared_edges = lower_edges & upper_edges
        glued_edges = lower_edges | upper_edges
        lower_vertices = _vertex_set(lower_edges)
        upper_vertices = _vertex_set(upper_edges)
        return (
            self.one_slab_face_count
            == self.lower_face_count
            == self.upper_face_count
            == len(lower)
            == len(upper)
            == 72
            and self.shared_interface_face_count == len(shared) == 24
            and self.glued_face_count
            == len(glued)
            == len(fixed_spatial_two_step_slab_plaquettes())
            == 120
            and self.isotropic_extent_two_face_count
            == len(isotropic_extent_two)
            == 405
            and self.one_slab_link_count
            == len(lower_edges)
            == len(upper_edges)
            == 116
            and self.shared_interface_link_count == len(shared_edges) == 48
            and self.glued_link_count == len(glued_edges) == 184
            and self.one_slab_vertex_count
            == len(lower_vertices)
            == len(upper_vertices)
            == 52
            and self.shared_interface_vertex_count
            == len(lower_vertices & upper_vertices)
            == 26
            and self.glued_vertex_count
            == len(lower_vertices | upper_vertices)
            == 78
            and self.shared_faces_all_spatial_at_time_one
            and all(
                plaquette[1][1] < 3 and plaquette[0][3] == 1
                for plaquette in shared
            )
            and self.shared_links_all_spatial_at_time_one
            and all(
                direction < 3 and base[3] == 1
                for base, direction in shared_edges
            )
            and self.fixed_spatial_union_is_not_isotropic_extent_two
            and glued != isotropic_extent_two
            and self.lower_upper_variables_identified_on_interface
            and self.product_density_interface_multiplicity == 2
            and self.physical_density_interface_multiplicity == 1
            and self.exact_unnormalized_density_correction
            == "W_lower*W_upper=W_glued*W_interface"
            and not self.independent_probability_convolution_is_physical_gluing
            and self.boundary_fiber_product_required
            and self.new_partition_normalization_required
            and not self.physical_channel_gluing_identity_proved
            and self.first_open_obligation
            == "construct-boundary-conditioned-fiber-product-channel"
        )


@cache
def two_slab_physical_gluing_audit() -> TwoSlabPhysicalGluingAudit:
    """Construct the exact adjacent-slab interface certificate."""

    lower = boundary_complete_slab_plaquettes(1)
    upper = tuple(
        _translate_time_plaquette(plaquette, 1)
        for plaquette in lower
    )
    lower_set = set(lower)
    upper_set = set(upper)
    lower_edges = _edge_set(lower)
    upper_edges = _edge_set(upper)
    lower_vertices = _vertex_set(lower_edges)
    upper_vertices = _vertex_set(upper_edges)
    certificate = TwoSlabPhysicalGluingAudit(
        one_slab_face_count=len(lower),
        lower_face_count=len(lower),
        upper_face_count=len(upper),
        shared_interface_face_count=len(lower_set & upper_set),
        glued_face_count=len(lower_set | upper_set),
        isotropic_extent_two_face_count=len(
            boundary_complete_slab_plaquettes(2)
        ),
        one_slab_link_count=len(lower_edges),
        shared_interface_link_count=len(lower_edges & upper_edges),
        glued_link_count=len(lower_edges | upper_edges),
        one_slab_vertex_count=len(lower_vertices),
        shared_interface_vertex_count=len(
            lower_vertices & upper_vertices
        ),
        glued_vertex_count=len(lower_vertices | upper_vertices),
        shared_faces_all_spatial_at_time_one=True,
        shared_links_all_spatial_at_time_one=True,
        fixed_spatial_union_is_not_isotropic_extent_two=True,
        lower_upper_variables_identified_on_interface=True,
        product_density_interface_multiplicity=2,
        physical_density_interface_multiplicity=1,
        exact_unnormalized_density_correction=(
            "W_lower*W_upper=W_glued*W_interface"
        ),
        independent_probability_convolution_is_physical_gluing=False,
        boundary_fiber_product_required=True,
        new_partition_normalization_required=True,
        physical_channel_gluing_identity_proved=False,
        first_open_obligation=(
            "construct-boundary-conditioned-fiber-product-channel"
        ),
    )
    if not certificate.validates():
        raise AssertionError("the two-slab physical gluing audit drifted")
    return certificate


@dataclass(frozen=True)
class InterfaceFloorCeilingNoGo:
    """Collapse of the naive 24-face interface correction coefficient."""

    coupling: Fraction
    interface_face_count: int
    interface_order_coefficient: Fraction
    collapse_upper_bound: Fraction
    spacing: Fraction | None
    dyadic_spacing_power_upper_bound: Fraction | None
    fixed_coupling_interface_comparison_positive: bool
    spacing_uniform_interface_comparison_proved: bool
    direct_integrated_glued_block_comparison_refuted: bool

    def validates(self) -> bool:
        if not 0 < self.coupling < 1:
            return False
        choi = physical_all_label_choi_domination(
            self.coupling,
            self.coupling,
        )
        floor = choi.density_floor.heat_kernel_floor
        upper = (
            choi.density_cutoff_schedule.plaquette_tail.total_upper_bound
        )
        coefficient = (floor / upper) ** 24
        collapse = (
            (1 - self.coupling) ** 3
            / (1 + self.coupling)
        ) ** 24
        base = (
            self.interface_face_count == 24
            and self.interface_order_coefficient == coefficient
            and 0 < coefficient <= collapse
            and self.collapse_upper_bound == collapse
            and self.fixed_coupling_interface_comparison_positive
            and not self.spacing_uniform_interface_comparison_proved
            and not self.direct_integrated_glued_block_comparison_refuted
        )
        if self.spacing is None:
            return bool(
                base and self.dyadic_spacing_power_upper_bound is None
            )
        return bool(
            base
            and self.spacing == 1 - self.coupling
            and self.dyadic_spacing_power_upper_bound == self.spacing**72
            and collapse <= self.spacing**72
        )


def interface_floor_ceiling_no_go(
    coupling: Fraction,
    *,
    dyadic_spacing: bool = False,
) -> InterfaceFloorCeilingNoGo:
    """Evaluate the naive interface correction at one exact coupling."""

    if not 0 < coupling < 1:
        raise ValueError("the heat coordinate must lie in (0, 1)")
    spacing = 1 - coupling if dyadic_spacing else None
    choi = physical_all_label_choi_domination(coupling, coupling)
    floor = choi.density_floor.heat_kernel_floor
    upper = choi.density_cutoff_schedule.plaquette_tail.total_upper_bound
    certificate = InterfaceFloorCeilingNoGo(
        coupling=coupling,
        interface_face_count=24,
        interface_order_coefficient=(floor / upper) ** 24,
        collapse_upper_bound=(
            (1 - coupling) ** 3 / (1 + coupling)
        )
        ** 24,
        spacing=spacing,
        dyadic_spacing_power_upper_bound=(
            spacing**72 if spacing is not None else None
        ),
        fixed_coupling_interface_comparison_positive=True,
        spacing_uniform_interface_comparison_proved=False,
        direct_integrated_glued_block_comparison_refuted=False,
    )
    if not certificate.validates():
        raise AssertionError("the interface correction no-go drifted")
    return certificate
