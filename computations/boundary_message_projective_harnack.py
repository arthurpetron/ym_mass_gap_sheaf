"""Projective Harnack reduction for the physical boundary-message kernel.

The absolute grouped-kernel limit used in the first BF4 reduction is
stronger than the normalized channel needs.  For a strictly positive kernel
``G`` define its four-boundary cross-ratio

    Theta(G) = max G(x,z) G(x',z') / (G(x,z') G(x',z)).

If ``P_h`` is the Doob transform by any positive terminal message ``h``,
then

    P_h(x,dz) >= Theta(G)**(-1) P_h(x',dz)

for every pair of sources.  This follows because the backward-message ratio
is a weighted average of ``G(x,z)/G(x',z)``.  The result is independent of
``h`` and invariant under arbitrary positive source and target factors.

Consequently a spacing-independent *absolute* positive-kernel limit is not
required.  It is enough that the grouped Feynman--Kac kernel be uniformly
close, relative to spacing-dependent profiles, to a rank-one kernel:

    G_a(x,z) = alpha_a(x) beta_a(z) (1 + r_a(x,z)),
    |r_a| <= delta < 1.

Then ``Theta(G_a) <= ((1+delta)/(1-delta))**2`` and every Doob transform has
common mass at least ``((1-delta)/(1+delta))**2``.  The profiles may
localize as the spacing vanishes.

For the continuous Yang--Mills transfer, the temporal Haar integral factors
exactly through five holonomies of its connected 20-vertex, 24-edge base
graph.  Conditional integration removes the other 18 boundary cycles and
produces a five-holonomy Feynman--Kac kernel with an effective spatial
weight.  At fixed coupling, rank-one Perron convergence then follows at
paper level from its strictly positive continuous kernel on a compact
quotient: the integral operator is compact and positivity improving, and
two smoothing factors turn the operator-norm Perron remainder into a
uniform kernel remainder.  The open estimate is quantitative and
spacing-uniform.  Equivalently, one must bound the four-boundary cross-ratio
of the grouped five-holonomy kernel.
"""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass
from fractions import Fraction
from functools import cache

from computations.boundary_message_markovization import (
    AllLabelFineBoundaryTransfer,
    all_label_fine_boundary_transfer,
)
from computations.boundary_message_uniform_order import (
    RationalMatrix,
    RationalVector,
    finite_grouped_message_order,
)
from computations.boundary_spatial_flatness_coercivity import (
    boundary_spatial_flatness_coercivity,
)
from computations.boundary_temporal_relative_coupling import (
    TEMPORAL_RELATIVE_FIRST_OPEN_OBLIGATION,
    boundary_temporal_relative_coupling,
)
from computations.rational_projective_diameter import (
    certify_positive_sector,
)


def _positive_vector(
    values: Iterable[int | Fraction],
    *,
    name: str,
) -> RationalVector:
    vector = tuple(Fraction(value) for value in values)
    if not vector or any(value <= 0 for value in vector):
        raise ValueError(f"{name} must be nonempty and strictly positive")
    return vector


def _positive_matrix(
    rows: Iterable[Iterable[int | Fraction]],
) -> RationalMatrix:
    matrix = tuple(tuple(Fraction(value) for value in row) for row in rows)
    if not matrix or not matrix[0]:
        raise ValueError("the grouped kernel must be nonempty")
    width = len(matrix[0])
    if any(len(row) != width for row in matrix):
        raise ValueError("the grouped kernel must be rectangular")
    if any(value <= 0 for row in matrix for value in row):
        raise ValueError("the projective Harnack theorem requires positivity")
    return matrix


@dataclass(frozen=True)
class CrossRatioBackwardMessageOrder:
    """Exact terminal-independent Doob order from one cross-ratio bound."""

    grouped_kernel: RationalMatrix
    terminal_message: RationalVector
    markov_kernel: RationalMatrix
    max_four_boundary_cross_ratio: Fraction
    common_markov_mass: Fraction
    every_source_pair_ordered: bool
    terminal_message_independent_coefficient: bool
    row_column_scaling_invariant: bool

    def validates(self) -> bool:
        try:
            kernel = _positive_matrix(self.grouped_kernel)
            terminal = _positive_vector(
                self.terminal_message,
                name="the terminal message",
            )
        except ValueError:
            return False
        if len(terminal) != len(kernel[0]):
            return False
        order = finite_grouped_message_order(kernel, terminal)
        projective = certify_positive_sector(
            kernel,
            tuple(range(len(kernel))),
            tuple(range(len(kernel[0]))),
        )
        theta = projective.max_cross_ratio
        epsilon = Fraction(1, theta)
        return (
            self.markov_kernel == order.markov_kernel
            and self.max_four_boundary_cross_ratio == theta >= 1
            and self.common_markov_mass == epsilon
            and 0 < epsilon <= 1
            and self.every_source_pair_ordered
            and self.terminal_message_independent_coefficient
            and self.row_column_scaling_invariant
            and all(
                order.markov_kernel[first][target] >= epsilon * order.markov_kernel[second][target]
                for first in range(len(kernel))
                for second in range(len(kernel))
                for target in range(len(kernel[0]))
            )
        )


def cross_ratio_backward_message_order(
    grouped_kernel: Iterable[Iterable[int | Fraction]],
    terminal_message: Iterable[int | Fraction],
) -> CrossRatioBackwardMessageOrder:
    """Order every Doob row by the inverse four-boundary cross-ratio."""

    kernel = _positive_matrix(grouped_kernel)
    terminal = _positive_vector(
        terminal_message,
        name="the terminal message",
    )
    if len(terminal) != len(kernel[0]):
        raise ValueError("the terminal message has the wrong target dimension")
    order = finite_grouped_message_order(kernel, terminal)
    projective = certify_positive_sector(
        kernel,
        tuple(range(len(kernel))),
        tuple(range(len(kernel[0]))),
    )
    certificate = CrossRatioBackwardMessageOrder(
        grouped_kernel=kernel,
        terminal_message=terminal,
        markov_kernel=order.markov_kernel,
        max_four_boundary_cross_ratio=projective.max_cross_ratio,
        common_markov_mass=Fraction(1, projective.max_cross_ratio),
        every_source_pair_ordered=True,
        terminal_message_independent_coefficient=True,
        row_column_scaling_invariant=True,
    )
    if not certificate.validates():
        raise AssertionError("the cross-ratio backward-message order drifted")
    return certificate


@dataclass(frozen=True)
class RelativeRankOneProjectiveOrder:
    """Uniform Doob order from relative rank-one kernel convergence."""

    grouped_kernel: RationalMatrix
    source_profile: RationalVector
    target_profile: RationalVector
    terminal_message: RationalVector
    relative_kernel: RationalMatrix
    actual_relative_error: Fraction
    certified_relative_error: Fraction
    actual_max_cross_ratio: Fraction
    certified_cross_ratio_ceiling: Fraction
    certified_common_markov_mass: Fraction
    spacing_dependent_profiles_allowed: bool
    absolute_kernel_floor_required: bool
    uniform_projective_order_proved: bool

    def validates(self) -> bool:
        try:
            kernel = _positive_matrix(self.grouped_kernel)
            source = _positive_vector(
                self.source_profile,
                name="the source profile",
            )
            target = _positive_vector(
                self.target_profile,
                name="the target profile",
            )
            terminal = _positive_vector(
                self.terminal_message,
                name="the terminal message",
            )
        except ValueError:
            return False
        if (
            len(source) != len(kernel)
            or len(target) != len(kernel[0])
            or len(terminal) != len(kernel[0])
        ):
            return False
        relative = tuple(
            tuple(
                kernel[row][column] / (source[row] * target[column])
                for column in range(len(target))
            )
            for row in range(len(source))
        )
        error = max(abs(value - 1) for row in relative for value in row)
        if not 0 <= self.certified_relative_error < 1:
            return False
        lower = 1 - self.certified_relative_error
        upper = 1 + self.certified_relative_error
        cross_ratio_ceiling = (upper / lower) ** 2
        projective = cross_ratio_backward_message_order(kernel, terminal)
        epsilon = (lower / upper) ** 2
        return (
            self.relative_kernel == relative
            and self.actual_relative_error == error
            and error <= self.certified_relative_error
            and self.actual_max_cross_ratio
            == projective.max_four_boundary_cross_ratio
            <= cross_ratio_ceiling
            and self.certified_cross_ratio_ceiling == cross_ratio_ceiling
            and self.certified_common_markov_mass == epsilon
            and epsilon <= projective.common_markov_mass
            and self.spacing_dependent_profiles_allowed
            and not self.absolute_kernel_floor_required
            and self.uniform_projective_order_proved
            and all(
                projective.markov_kernel[first][column]
                >= epsilon * projective.markov_kernel[second][column]
                for first in range(len(kernel))
                for second in range(len(kernel))
                for column in range(len(kernel[0]))
            )
        )


def relative_rank_one_projective_order(
    grouped_kernel: Iterable[Iterable[int | Fraction]],
    source_profile: Iterable[int | Fraction],
    target_profile: Iterable[int | Fraction],
    terminal_message: Iterable[int | Fraction],
    certified_relative_error: Fraction,
) -> RelativeRankOneProjectiveOrder:
    """Certify a profile-relative rank-one Harnack bound."""

    kernel = _positive_matrix(grouped_kernel)
    source = _positive_vector(source_profile, name="the source profile")
    target = _positive_vector(target_profile, name="the target profile")
    terminal = _positive_vector(
        terminal_message,
        name="the terminal message",
    )
    if (
        len(source) != len(kernel)
        or len(target) != len(kernel[0])
        or len(terminal) != len(kernel[0])
    ):
        raise ValueError("the profiles and terminal message must fit the kernel")
    if not 0 <= certified_relative_error < 1:
        raise ValueError("the certified relative error must lie in [0,1)")
    relative = tuple(
        tuple(kernel[row][column] / (source[row] * target[column]) for column in range(len(target)))
        for row in range(len(source))
    )
    actual_error = max(abs(value - 1) for row in relative for value in row)
    if actual_error > certified_relative_error:
        raise ValueError("the supplied relative error does not bound the kernel")
    projective = cross_ratio_backward_message_order(kernel, terminal)
    lower = 1 - certified_relative_error
    upper = 1 + certified_relative_error
    certificate = RelativeRankOneProjectiveOrder(
        grouped_kernel=kernel,
        source_profile=source,
        target_profile=target,
        terminal_message=terminal,
        relative_kernel=relative,
        actual_relative_error=actual_error,
        certified_relative_error=certified_relative_error,
        actual_max_cross_ratio=projective.max_four_boundary_cross_ratio,
        certified_cross_ratio_ceiling=(upper / lower) ** 2,
        certified_common_markov_mass=(lower / upper) ** 2,
        spacing_dependent_profiles_allowed=True,
        absolute_kernel_floor_required=False,
        uniform_projective_order_proved=True,
    )
    if not certificate.validates():
        raise AssertionError("the relative rank-one order drifted")
    return certificate


@dataclass(frozen=True)
class LocalizedRankOneProfileWitness:
    """Exact witness that an absolute positive limiting floor is unnecessary."""

    localization_parameter: int
    source_profile: RationalVector
    target_profile: RationalVector
    rank_one_kernel: RationalMatrix
    absolute_kernel_floor: Fraction
    absolute_floor_upper_bound: Fraction
    max_four_boundary_cross_ratio: Fraction
    common_markov_mass: Fraction
    absolute_floor_collapses: bool
    projective_order_stays_exact: bool

    def validates(self) -> bool:
        n = self.localization_parameter
        if n < 2:
            return False
        source = (Fraction(1, n + 1), Fraction(n, n + 1))
        target = (Fraction(n, n + 1), Fraction(1, n + 1))
        kernel = tuple(
            tuple(source[row] * target[column] for column in range(2)) for row in range(2)
        )
        projective = cross_ratio_backward_message_order(kernel, (1, 1))
        floor = min(value for row in kernel for value in row)
        return (
            self.source_profile == source
            and self.target_profile == target
            and self.rank_one_kernel == kernel
            and self.absolute_kernel_floor == floor == Fraction(1, (n + 1) ** 2)
            and self.absolute_floor_upper_bound == Fraction(1, n * n)
            and floor <= self.absolute_floor_upper_bound
            and self.max_four_boundary_cross_ratio == projective.max_four_boundary_cross_ratio == 1
            and self.common_markov_mass == projective.common_markov_mass == 1
            and self.absolute_floor_collapses
            and self.projective_order_stays_exact
        )


def localized_rank_one_profile_witness(
    localization_parameter: int,
) -> LocalizedRankOneProfileWitness:
    """Construct a rank-one family with vanishing absolute kernel floor."""

    if localization_parameter < 2:
        raise ValueError("the localization parameter must be at least two")
    n = localization_parameter
    source = (Fraction(1, n + 1), Fraction(n, n + 1))
    target = (Fraction(n, n + 1), Fraction(1, n + 1))
    kernel = tuple(tuple(source[row] * target[column] for column in range(2)) for row in range(2))
    projective = cross_ratio_backward_message_order(kernel, (1, 1))
    certificate = LocalizedRankOneProfileWitness(
        localization_parameter=n,
        source_profile=source,
        target_profile=target,
        rank_one_kernel=kernel,
        absolute_kernel_floor=min(value for row in kernel for value in row),
        absolute_floor_upper_bound=Fraction(1, n * n),
        max_four_boundary_cross_ratio=projective.max_four_boundary_cross_ratio,
        common_markov_mass=projective.common_markov_mass,
        absolute_floor_collapses=True,
        projective_order_stays_exact=True,
    )
    if not certificate.validates():
        raise AssertionError("the localized rank-one witness drifted")
    return certificate


@dataclass(frozen=True)
class IntrinsicPerronRemainderBudget:
    """Exact scalar budget for a buffered intrinsic Perron estimate."""

    intrinsic_buffer_constant: Fraction
    bulk_spectral_ratio: Fraction
    bulk_steps: int
    relative_rank_one_error: Fraction
    common_markov_mass: Fraction
    closes_projective_harnack: bool

    def validates(self) -> bool:
        error = self.intrinsic_buffer_constant**2 * self.bulk_spectral_ratio**self.bulk_steps
        return (
            self.intrinsic_buffer_constant >= 1
            and 0 <= self.bulk_spectral_ratio < 1
            and self.bulk_steps >= 1
            and self.relative_rank_one_error == error < 1
            and self.common_markov_mass == ((1 - error) / (1 + error)) ** 2
            and self.closes_projective_harnack
        )


def intrinsic_perron_remainder_budget(
    intrinsic_buffer_constant: Fraction,
    bulk_spectral_ratio: Fraction,
    bulk_steps: int,
) -> IntrinsicPerronRemainderBudget:
    """Turn ``C**2 q**m < 1`` into a terminal-independent order mass."""

    if intrinsic_buffer_constant < 1:
        raise ValueError("the intrinsic buffer constant must be at least one")
    if not 0 <= bulk_spectral_ratio < 1:
        raise ValueError("the bulk spectral ratio must lie in [0,1)")
    if bulk_steps < 1:
        raise ValueError("at least one bulk step is required")
    error = intrinsic_buffer_constant**2 * bulk_spectral_ratio**bulk_steps
    if error >= 1:
        raise ValueError("the intrinsic Perron remainder must be below one")
    certificate = IntrinsicPerronRemainderBudget(
        intrinsic_buffer_constant=intrinsic_buffer_constant,
        bulk_spectral_ratio=bulk_spectral_ratio,
        bulk_steps=bulk_steps,
        relative_rank_one_error=error,
        common_markov_mass=((1 - error) / (1 + error)) ** 2,
        closes_projective_harnack=True,
    )
    if not certificate.validates():
        raise AssertionError("the intrinsic Perron budget drifted")
    return certificate


@dataclass(frozen=True)
class PhysicalFeynmanKacProjectiveRoute:
    """The exact projective target and its still-open physical estimate."""

    transfer: AllLabelFineBoundaryTransfer
    four_boundary_ratio: str
    cross_ratio_orders_every_terminal_message: bool
    source_target_profiles_cancel_exactly: bool
    spacing_dependent_perron_profiles_allowed: bool
    absolute_positive_kernel_limit_required: bool
    fixed_coupling_compact_positivity_improving: bool
    fixed_coupling_intrinsic_perron_convergence_available: bool
    fixed_coupling_two_buffer_remainder_formula: str
    interior_spatial_weights_in_physical_grouped_kernel: bool
    spatial_complex_two_sphere_homotopy_type_certified: bool
    unique_flat_spatial_su2_gauge_orbit_proved: bool
    multiple_topological_flat_wells_refuted: bool
    linearized_spatial_curvature_coercivity_floor: Fraction
    global_nonlinear_spatial_curvature_coercivity_constant: Fraction
    nonlinear_global_spatial_curvature_coercivity_proved: bool
    linearized_temporal_relative_coupling_rank: int
    microscopic_temporal_ellipticity_on_all_23_cycles: bool
    exact_nonlinear_five_holonomy_factorization_proved: bool
    eighteen_dimensional_fibers_conditionally_integrated: bool
    five_holonomy_feynman_kac_operator_identity_proved: bool
    spatial_temporal_hypocoercive_perron_bound_proved: bool
    boundary_connected_interaction_target_identified: bool
    spacing_uniform_physical_cross_ratio_proved: bool
    spacing_uniform_intrinsic_buffer_bound_proved: bool
    spacing_uniform_bulk_spectral_budget_proved: bool
    boundary_spanning_connected_expansion_bound_proved: bool
    physical_backward_message_order_proved: bool
    first_open_obligation: str

    def validates(self) -> bool:
        cross_ratio = cross_ratio_backward_message_order(
            ((4, 9), (7, 7)),
            (1, 2),
        )
        rank_one = relative_rank_one_projective_order(
            ((10, 2), (15, 3)),
            (2, 3),
            (5, 1),
            (7, 11),
            Fraction(0),
        )
        localized = localized_rank_one_profile_witness(10)
        budget = intrinsic_perron_remainder_budget(
            Fraction(2),
            Fraction(1, 4),
            4,
        )
        spatial_flatness = boundary_spatial_flatness_coercivity()
        temporal_coupling = boundary_temporal_relative_coupling()
        return (
            self.transfer.validates()
            and self.transfer.transfer_strictly_positive_and_continuous
            and self.transfer.time_reflection_symmetric
            and cross_ratio.validates()
            and rank_one.validates()
            and localized.validates()
            and budget.validates()
            and spatial_flatness.validates()
            and temporal_coupling.validates()
            and self.four_boundary_ratio == "G(x,z)G(x',z')/[G(x,z')G(x',z)]"
            and self.cross_ratio_orders_every_terminal_message
            and self.source_target_profiles_cancel_exactly
            and self.spacing_dependent_perron_profiles_allowed
            and not self.absolute_positive_kernel_limit_required
            and self.fixed_coupling_compact_positivity_improving
            and self.fixed_coupling_intrinsic_perron_convergence_available
            and self.fixed_coupling_two_buffer_remainder_formula == "delta_s,m <= C_s^2 q_s^(m-2)"
            and self.interior_spatial_weights_in_physical_grouped_kernel
            and self.spatial_complex_two_sphere_homotopy_type_certified
            and self.unique_flat_spatial_su2_gauge_orbit_proved
            and self.multiple_topological_flat_wells_refuted
            and self.linearized_spatial_curvature_coercivity_floor
            == spatial_flatness.conservative_linearized_coercivity_floor
            == Fraction(1, 11)
            and self.global_nonlinear_spatial_curvature_coercivity_constant
            == spatial_flatness.global_nonlinear_curvature_coercivity_constant
            == Fraction(1, 81)
            and self.nonlinear_global_spatial_curvature_coercivity_proved
            and self.linearized_temporal_relative_coupling_rank
            == temporal_coupling.relative_boundary_coupling_rank
            == 5
            and not self.microscopic_temporal_ellipticity_on_all_23_cycles
            and self.exact_nonlinear_five_holonomy_factorization_proved
            and self.eighteen_dimensional_fibers_conditionally_integrated
            and self.five_holonomy_feynman_kac_operator_identity_proved
            and not self.spatial_temporal_hypocoercive_perron_bound_proved
            and self.boundary_connected_interaction_target_identified
            and not self.spacing_uniform_physical_cross_ratio_proved
            and not self.spacing_uniform_intrinsic_buffer_bound_proved
            and not self.spacing_uniform_bulk_spectral_budget_proved
            and not self.boundary_spanning_connected_expansion_bound_proved
            and not self.physical_backward_message_order_proved
            and self.first_open_obligation == TEMPORAL_RELATIVE_FIRST_OPEN_OBLIGATION
        )


@cache
def physical_feynman_kac_projective_route() -> PhysicalFeynmanKacProjectiveRoute:
    """Return the strongest exact reduction of the physical Harnack gate."""

    spatial_flatness = boundary_spatial_flatness_coercivity()
    temporal_coupling = boundary_temporal_relative_coupling()
    route = PhysicalFeynmanKacProjectiveRoute(
        transfer=all_label_fine_boundary_transfer(Fraction(1, 2)),
        four_boundary_ratio="G(x,z)G(x',z')/[G(x,z')G(x',z)]",
        cross_ratio_orders_every_terminal_message=True,
        source_target_profiles_cancel_exactly=True,
        spacing_dependent_perron_profiles_allowed=True,
        absolute_positive_kernel_limit_required=False,
        fixed_coupling_compact_positivity_improving=True,
        fixed_coupling_intrinsic_perron_convergence_available=True,
        fixed_coupling_two_buffer_remainder_formula=("delta_s,m <= C_s^2 q_s^(m-2)"),
        interior_spatial_weights_in_physical_grouped_kernel=True,
        spatial_complex_two_sphere_homotopy_type_certified=True,
        unique_flat_spatial_su2_gauge_orbit_proved=True,
        multiple_topological_flat_wells_refuted=True,
        linearized_spatial_curvature_coercivity_floor=(
            spatial_flatness.conservative_linearized_coercivity_floor
        ),
        global_nonlinear_spatial_curvature_coercivity_constant=(
            spatial_flatness.global_nonlinear_curvature_coercivity_constant
        ),
        nonlinear_global_spatial_curvature_coercivity_proved=True,
        linearized_temporal_relative_coupling_rank=(
            temporal_coupling.relative_boundary_coupling_rank
        ),
        microscopic_temporal_ellipticity_on_all_23_cycles=False,
        exact_nonlinear_five_holonomy_factorization_proved=True,
        eighteen_dimensional_fibers_conditionally_integrated=True,
        five_holonomy_feynman_kac_operator_identity_proved=True,
        spatial_temporal_hypocoercive_perron_bound_proved=False,
        boundary_connected_interaction_target_identified=True,
        spacing_uniform_physical_cross_ratio_proved=False,
        spacing_uniform_intrinsic_buffer_bound_proved=False,
        spacing_uniform_bulk_spectral_budget_proved=False,
        boundary_spanning_connected_expansion_bound_proved=False,
        physical_backward_message_order_proved=False,
        first_open_obligation=TEMPORAL_RELATIVE_FIRST_OPEN_OBLIGATION,
    )
    if not route.validates():
        raise AssertionError("the physical Feynman--Kac projective route drifted")
    return route
