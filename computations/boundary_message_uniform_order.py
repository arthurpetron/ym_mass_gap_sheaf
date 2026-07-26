"""Uniform-order reduction for continuous backward-message channels.

For a strictly positive grouped transfer kernel ``G(x,z)`` and positive
terminal message ``h(z)``, define

    H(x) = integral G(x,z) h(z) dz,
    P(x,dz) = G(x,z) h(z) dz / H(x).

Fix a reference source ``x0``.  If

    alpha <= G(x,z) / G(x0,z) <= beta

for every ``x,z``, integration immediately gives

    alpha <= H(x) / H(x0) <= beta.

Consequently

    P(x,dz) >= (alpha / beta) P(x0,dz).

The terminal boundary condition cancels completely.  Thus the
spacing-uniform backward-message problem is exactly a two-sided Harnack
or row-ratio estimate for the *raw grouped physical transfer kernel*.

Positive endpoint weights do not affect this Markov kernel.  If

    G(x,z) = a(x) Q(x,z) b(z),

then Markovizing ``G`` with terminal ``h`` is identical to Markovizing
``Q`` with terminal ``b*h``; the source multiplier ``a`` cancels.  For the
symmetric Yang--Mills transfer this removes the two endpoint square roots
of the spatial plaquette density.  The remaining analytic object is the
interior Feynman--Kac kernel with spatial weights at intermediate slices.

The module proves the reduction over exact rational finite kernels and
constructs a spacing-uniform kinetic-only benchmark on the enlarged
23-cycle boundary carrier.  Once a grouped heat coordinate is at most
``1/2``, one cycle has the exact bounds

    1055/2272 <= K <= 3489/2272.

The 23-cycle product therefore gives a terminal-independent Markov
minorization of ``(1055/3489)**46``.  This is not yet the physical theorem:
the intermediate spatial Feynman--Kac weights are omitted.  The remaining
BF4 estimate is a spacing-uniform two-sided Harnack bound with those weights
included.  An exact two-state family also shows that positivity of arbitrary
intermediate weights cannot supply such a bound: its common row-order mass
is ``n/(n**2-n+1)``, which tends to zero.
"""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass
from fractions import Fraction
from functools import cache
from typing import TypeAlias

from computations.all_label_whole_slab_tail import (
    heat_character_sup_term,
    single_plaquette_all_label_tail,
)
from computations.boundary_message_markovization import (
    EnlargedFineBoundaryCarrier,
    enlarged_fine_boundary_carrier,
)

RationalVector: TypeAlias = tuple[Fraction, ...]
RationalMatrix: TypeAlias = tuple[RationalVector, ...]

GROUPED_HEAT_CAP = Fraction(1, 2)
ONE_CYCLE_HAAR_FLOOR = Fraction(1055, 2272)
ONE_CYCLE_HAAR_CEILING = Fraction(3489, 2272)


def _vector(values: Iterable[int | Fraction]) -> RationalVector:
    result = tuple(Fraction(value) for value in values)
    if not result:
        raise ValueError("a boundary vector must be nonempty")
    return result


def _positive_matrix(
    rows: Iterable[Iterable[int | Fraction]],
) -> RationalMatrix:
    matrix = tuple(_vector(row) for row in rows)
    if not matrix:
        raise ValueError("a grouped kernel must be nonempty")
    width = len(matrix[0])
    if any(len(row) != width for row in matrix):
        raise ValueError("a grouped kernel must be rectangular")
    if any(value <= 0 for row in matrix for value in row):
        raise ValueError("the grouped order theorem requires strict positivity")
    return matrix


@dataclass(frozen=True)
class FiniteGroupedMessageOrder:
    """Exact finite row-ratio, message-order and Markov minorization theorem."""

    grouped_kernel: RationalMatrix
    terminal_message: RationalVector
    reference_source: int
    backward_message: RationalVector
    markov_kernel: RationalMatrix
    row_ratio_lower: Fraction
    row_ratio_upper: Fraction
    message_ratio_lower: Fraction
    message_ratio_upper: Fraction
    common_reference_mass: Fraction
    reference_markov_row: RationalVector
    terminal_message_independent_coefficient: bool
    exact_markov_minorization: bool

    def validates(self) -> bool:
        try:
            kernel = _positive_matrix(self.grouped_kernel)
            terminal = _vector(self.terminal_message)
        except ValueError:
            return False
        if (
            len(terminal) != len(kernel[0])
            or any(value <= 0 for value in terminal)
            or not 0 <= self.reference_source < len(kernel)
        ):
            return False
        reference = kernel[self.reference_source]
        ratios = tuple(
            kernel[source][target] / reference[target]
            for source in range(len(kernel))
            for target in range(len(reference))
        )
        alpha = min(ratios)
        beta = max(ratios)
        message = tuple(
            sum(
                (
                    kernel[source][target] * terminal[target]
                    for target in range(len(terminal))
                ),
                start=Fraction(0),
            )
            for source in range(len(kernel))
        )
        markov = tuple(
            tuple(
                kernel[source][target]
                * terminal[target]
                / message[source]
                for target in range(len(terminal))
            )
            for source in range(len(kernel))
        )
        reference_message = message[self.reference_source]
        message_ratios = tuple(
            value / reference_message for value in message
        )
        epsilon = alpha / beta
        reference_markov = markov[self.reference_source]
        return (
            self.backward_message == message
            and self.markov_kernel == markov
            and self.row_ratio_lower == alpha
            and self.row_ratio_upper == beta
            and self.message_ratio_lower == min(message_ratios)
            and self.message_ratio_upper == max(message_ratios)
            and alpha <= min(message_ratios)
            and max(message_ratios) <= beta
            and self.common_reference_mass == epsilon
            and 0 < epsilon <= 1
            and self.reference_markov_row == reference_markov
            and self.terminal_message_independent_coefficient
            and self.exact_markov_minorization
            and all(
                markov[source][target]
                >= epsilon * reference_markov[target]
                for source in range(len(markov))
                for target in range(len(reference_markov))
            )
            and all(
                sum(row, start=Fraction(0)) == 1 for row in markov
            )
        )


def finite_grouped_message_order(
    grouped_kernel: Iterable[Iterable[int | Fraction]],
    terminal_message: Iterable[int | Fraction],
    *,
    reference_source: int = 0,
) -> FiniteGroupedMessageOrder:
    """Construct the exact terminal-independent message/order certificate."""

    kernel = _positive_matrix(grouped_kernel)
    terminal = _vector(terminal_message)
    if len(terminal) != len(kernel[0]) or any(value <= 0 for value in terminal):
        raise ValueError("the terminal message must be positive and compatible")
    if not 0 <= reference_source < len(kernel):
        raise ValueError("the reference source leaves the grouped kernel")
    reference = kernel[reference_source]
    ratios = tuple(
        kernel[source][target] / reference[target]
        for source in range(len(kernel))
        for target in range(len(reference))
    )
    alpha = min(ratios)
    beta = max(ratios)
    message = tuple(
        sum(
            (
                kernel[source][target] * terminal[target]
                for target in range(len(terminal))
            ),
            start=Fraction(0),
        )
        for source in range(len(kernel))
    )
    markov = tuple(
        tuple(
            kernel[source][target] * terminal[target] / message[source]
            for target in range(len(terminal))
        )
        for source in range(len(kernel))
    )
    reference_message = message[reference_source]
    message_ratios = tuple(value / reference_message for value in message)
    certificate = FiniteGroupedMessageOrder(
        grouped_kernel=kernel,
        terminal_message=terminal,
        reference_source=reference_source,
        backward_message=message,
        markov_kernel=markov,
        row_ratio_lower=alpha,
        row_ratio_upper=beta,
        message_ratio_lower=min(message_ratios),
        message_ratio_upper=max(message_ratios),
        common_reference_mass=alpha / beta,
        reference_markov_row=markov[reference_source],
        terminal_message_independent_coefficient=True,
        exact_markov_minorization=True,
    )
    if not certificate.validates():
        raise AssertionError("the finite grouped message order drifted")
    return certificate


@dataclass(frozen=True)
class EndpointWeightCancellation:
    """Exact cancellation of positive source/target endpoint multipliers."""

    core_kernel: RationalMatrix
    source_weight: RationalVector
    target_weight: RationalVector
    terminal_message: RationalVector
    weighted_kernel: RationalMatrix
    weighted_markov_kernel: RationalMatrix
    core_updated_terminal_markov_kernel: RationalMatrix
    source_endpoint_weight_cancels: bool
    target_endpoint_weight_absorbed_into_terminal: bool
    exact_identity: bool

    def validates(self) -> bool:
        try:
            core = _positive_matrix(self.core_kernel)
            source = _vector(self.source_weight)
            target = _vector(self.target_weight)
            terminal = _vector(self.terminal_message)
        except ValueError:
            return False
        if (
            len(source) != len(core)
            or len(target) != len(core[0])
            or len(terminal) != len(core[0])
            or any(value <= 0 for value in source + target + terminal)
        ):
            return False
        weighted = tuple(
            tuple(
                source[row] * core[row][column] * target[column]
                for column in range(len(core[0]))
            )
            for row in range(len(core))
        )
        weighted_order = finite_grouped_message_order(
            weighted,
            terminal,
        )
        core_order = finite_grouped_message_order(
            core,
            tuple(
                target[index] * terminal[index]
                for index in range(len(target))
            ),
        )
        return (
            self.weighted_kernel == weighted
            and self.weighted_markov_kernel == weighted_order.markov_kernel
            and self.core_updated_terminal_markov_kernel
            == core_order.markov_kernel
            == weighted_order.markov_kernel
            and self.source_endpoint_weight_cancels
            and self.target_endpoint_weight_absorbed_into_terminal
            and self.exact_identity
        )


def endpoint_weight_cancellation(
    core_kernel: Iterable[Iterable[int | Fraction]],
    source_weight: Iterable[int | Fraction],
    target_weight: Iterable[int | Fraction],
    terminal_message: Iterable[int | Fraction],
) -> EndpointWeightCancellation:
    """Prove exact Markov invariance under positive endpoint multipliers."""

    core = _positive_matrix(core_kernel)
    source = _vector(source_weight)
    target = _vector(target_weight)
    terminal = _vector(terminal_message)
    if (
        len(source) != len(core)
        or len(target) != len(core[0])
        or len(terminal) != len(core[0])
        or any(value <= 0 for value in source + target + terminal)
    ):
        raise ValueError("endpoint weights must be positive and compatible")
    weighted = tuple(
        tuple(
            source[row] * core[row][column] * target[column]
            for column in range(len(core[0]))
        )
        for row in range(len(core))
    )
    weighted_markov = finite_grouped_message_order(
        weighted,
        terminal,
    ).markov_kernel
    core_markov = finite_grouped_message_order(
        core,
        tuple(
            target[index] * terminal[index]
            for index in range(len(target))
        ),
    ).markov_kernel
    certificate = EndpointWeightCancellation(
        core_kernel=core,
        source_weight=source,
        target_weight=target,
        terminal_message=terminal,
        weighted_kernel=weighted,
        weighted_markov_kernel=weighted_markov,
        core_updated_terminal_markov_kernel=core_markov,
        source_endpoint_weight_cancels=True,
        target_endpoint_weight_absorbed_into_terminal=True,
        exact_identity=True,
    )
    if not certificate.validates():
        raise AssertionError("the endpoint weight cancellation drifted")
    return certificate


def _least_steps_below_half(coupling: Fraction) -> int:
    if not 0 < coupling < 1:
        raise ValueError("the microscopic heat coordinate must lie in (0, 1)")
    steps = 1
    grouped = coupling
    while grouped > GROUPED_HEAT_CAP:
        grouped *= coupling
        steps += 1
    return steps


@dataclass(frozen=True)
class KineticBoundaryMessageUniformOrder:
    """Spacing-uniform benchmark before interior spatial weights are added."""

    microscopic_coupling: Fraction
    grouped_steps: int
    grouped_coupling: Fraction
    carrier: EnlargedFineBoundaryCarrier
    gauge_fixed_cycle_count: int
    one_cycle_floor: Fraction
    one_cycle_ceiling: Fraction
    grouped_row_ratio_lower: Fraction
    grouped_row_ratio_upper: Fraction
    backward_message_ratio_lower: Fraction
    backward_message_ratio_upper: Fraction
    markov_common_mass: Fraction
    terminal_message_independent: bool
    spacing_uniform_under_grouped_heat_cap: bool
    interior_spatial_feynman_kac_weights_included: bool
    physical_backward_message_order_proved: bool
    first_open_obligation: str

    def validates(self) -> bool:
        envelope = single_plaquette_all_label_tail(
            GROUPED_HEAT_CAP,
            1,
        )
        first_excited = heat_character_sup_term(GROUPED_HEAT_CAP, 1)
        floor = 1 - first_excited - envelope.tail_bound
        ceiling = envelope.total_upper_bound
        cycles = self.carrier.gauge_fixed_cycle_rank
        lower = (floor / ceiling) ** cycles
        upper = (ceiling / floor) ** cycles
        return (
            0 < self.microscopic_coupling < 1
            and self.grouped_steps
            == _least_steps_below_half(self.microscopic_coupling)
            and self.grouped_coupling
            == self.microscopic_coupling**self.grouped_steps
            <= GROUPED_HEAT_CAP
            and self.carrier.validates()
            and self.gauge_fixed_cycle_count == cycles == 23
            and self.one_cycle_floor
            == floor
            == ONE_CYCLE_HAAR_FLOOR
            and self.one_cycle_ceiling
            == ceiling
            == ONE_CYCLE_HAAR_CEILING
            and self.grouped_row_ratio_lower == lower
            and self.grouped_row_ratio_upper == upper
            and self.backward_message_ratio_lower == lower
            and self.backward_message_ratio_upper == upper
            and self.markov_common_mass
            == lower / upper
            == (floor / ceiling) ** (2 * cycles)
            and self.terminal_message_independent
            and self.spacing_uniform_under_grouped_heat_cap
            and not self.interior_spatial_feynman_kac_weights_included
            and not self.physical_backward_message_order_proved
            and self.first_open_obligation
            == "prove-spacing-uniform-feynman-kac-harnack-with-interior-spatial-weights"
        )


@cache
def kinetic_boundary_message_uniform_order(
    microscopic_coupling: Fraction,
) -> KineticBoundaryMessageUniformOrder:
    """Construct the exact 23-cycle kinetic grouped-order benchmark."""

    steps = _least_steps_below_half(microscopic_coupling)
    envelope = single_plaquette_all_label_tail(
        GROUPED_HEAT_CAP,
        1,
    )
    floor = (
        1
        - heat_character_sup_term(GROUPED_HEAT_CAP, 1)
        - envelope.tail_bound
    )
    ceiling = envelope.total_upper_bound
    carrier = enlarged_fine_boundary_carrier()
    cycles = carrier.gauge_fixed_cycle_rank
    lower = (floor / ceiling) ** cycles
    upper = (ceiling / floor) ** cycles
    certificate = KineticBoundaryMessageUniformOrder(
        microscopic_coupling=microscopic_coupling,
        grouped_steps=steps,
        grouped_coupling=microscopic_coupling**steps,
        carrier=carrier,
        gauge_fixed_cycle_count=cycles,
        one_cycle_floor=floor,
        one_cycle_ceiling=ceiling,
        grouped_row_ratio_lower=lower,
        grouped_row_ratio_upper=upper,
        backward_message_ratio_lower=lower,
        backward_message_ratio_upper=upper,
        markov_common_mass=lower / upper,
        terminal_message_independent=True,
        spacing_uniform_under_grouped_heat_cap=True,
        interior_spatial_feynman_kac_weights_included=False,
        physical_backward_message_order_proved=False,
        first_open_obligation=(
            "prove-spacing-uniform-feynman-kac-harnack-with-interior-spatial-weights"
        ),
    )
    if not certificate.validates():
        raise AssertionError("the kinetic boundary-message order drifted")
    return certificate


@dataclass(frozen=True)
class IntermediatePotentialHarnackObstruction:
    """Two-state no-go for order bounds from arbitrary positive potentials."""

    spacing_denominator: int
    spacing_proxy: Fraction
    kinetic_kernel: RationalMatrix
    intermediate_potential: RationalVector
    grouped_feynman_kac_kernel: RationalMatrix
    row_ratio_lower: Fraction
    row_ratio_upper: Fraction
    terminal_independent_markov_common_mass: Fraction
    common_mass_upper_bound: Fraction
    arbitrary_positive_potential_uniform_order_refuted: bool
    physical_yang_mills_harnack_refuted: bool

    def validates(self) -> bool:
        n = self.spacing_denominator
        if n < 2:
            return False
        spacing = Fraction(1, n)
        kinetic = ((Fraction(1), spacing), (spacing, Fraction(1)))
        potential = (Fraction(1), Fraction(n))
        grouped = (
            (1 + spacing, 1 + spacing),
            (1 + spacing, spacing**2 + Fraction(1, spacing)),
        )
        order = finite_grouped_message_order(grouped, (1, 1))
        common_mass = Fraction(n, n * n - n + 1)
        return (
            self.spacing_proxy == spacing
            and self.kinetic_kernel == kinetic
            and self.intermediate_potential == potential
            and self.grouped_feynman_kac_kernel == grouped
            and self.row_ratio_lower == order.row_ratio_lower == 1
            and self.row_ratio_upper
            == order.row_ratio_upper
            == Fraction(n * n - n + 1, n)
            and self.terminal_independent_markov_common_mass
            == order.common_reference_mass
            == common_mass
            and self.common_mass_upper_bound == Fraction(2, n)
            and common_mass <= self.common_mass_upper_bound
            and self.arbitrary_positive_potential_uniform_order_refuted
            and not self.physical_yang_mills_harnack_refuted
        )


def intermediate_potential_harnack_obstruction(
    spacing_denominator: int,
) -> IntermediatePotentialHarnackObstruction:
    """Show that an uncontrolled interior weight can destroy uniform order.

    With ``a=1/n``, let ``Q_a=((1,a),(a,1))`` and insert the positive
    potential ``D_n=diag(1,n)``.  The two-step Feynman--Kac kernel
    ``Q_a D_n Q_a`` has row-order common mass

        n / (n**2 - n + 1) <= 2/n.

    This refutes any theorem based only on positivity of the interior
    weights.  It does not refute a Yang--Mills-specific Harnack estimate.
    """

    if spacing_denominator < 2:
        raise ValueError("the spacing denominator must be at least two")
    n = spacing_denominator
    spacing = Fraction(1, n)
    kinetic = ((Fraction(1), spacing), (spacing, Fraction(1)))
    potential = (Fraction(1), Fraction(n))
    grouped = (
        (1 + spacing, 1 + spacing),
        (1 + spacing, spacing**2 + Fraction(1, spacing)),
    )
    order = finite_grouped_message_order(grouped, (1, 1))
    certificate = IntermediatePotentialHarnackObstruction(
        spacing_denominator=n,
        spacing_proxy=spacing,
        kinetic_kernel=kinetic,
        intermediate_potential=potential,
        grouped_feynman_kac_kernel=grouped,
        row_ratio_lower=order.row_ratio_lower,
        row_ratio_upper=order.row_ratio_upper,
        terminal_independent_markov_common_mass=order.common_reference_mass,
        common_mass_upper_bound=Fraction(2, n),
        arbitrary_positive_potential_uniform_order_refuted=True,
        physical_yang_mills_harnack_refuted=False,
    )
    if not certificate.validates():
        raise AssertionError("the intermediate-potential obstruction drifted")
    return certificate


@dataclass(frozen=True)
class PhysicalBackwardMessageOrderFrontier:
    """Closed order algebra and the remaining physical Harnack estimate."""

    carrier: EnlargedFineBoundaryCarrier
    finite_grouped_row_ratio_theorem_proved: bool
    backward_message_order_terminal_independent: bool
    endpoint_spatial_weight_cancellation_proved: bool
    correct_relative_message_coordinate: str
    kinetic_23_cycle_spacing_uniform_order_proved: bool
    kinetic_markov_common_mass: Fraction
    interior_spatial_feynman_kac_weights_included: bool
    physical_grouped_two_sided_harnack_proved: bool
    physical_spacing_uniform_backward_message_order_proved: bool
    uniform_positive_kernel_limit_criterion_proved: bool
    physical_grouped_feynman_kac_uniform_limit_proved: bool
    physical_limit_kernel_strictly_positive_proved: bool
    global_floor_ceiling_potential_comparison_usable: bool
    first_open_obligation: str

    def validates(self) -> bool:
        finite = finite_grouped_message_order(
            ((4, 9), (7, 7)),
            (1, 2),
        )
        endpoint = endpoint_weight_cancellation(
            ((2, 1), (1, 3)),
            (5, 7),
            (11, 13),
            (17, 19),
        )
        kinetic = kinetic_boundary_message_uniform_order(Fraction(9, 10))
        potential_no_go = intermediate_potential_harnack_obstruction(10)
        stable_limit = uniform_kernel_limit_message_order(
            ((4, 5), (6, 7)),
            (
                (Fraction(41, 10), Fraction(49, 10)),
                (Fraction(59, 10), Fraction(71, 10)),
            ),
            Fraction(1, 5),
        )
        return (
            self.carrier.validates()
            and finite.validates()
            and endpoint.validates()
            and kinetic.validates()
            and potential_no_go.validates()
            and potential_no_go.arbitrary_positive_potential_uniform_order_refuted
            and not potential_no_go.physical_yang_mills_harnack_refuted
            and self.finite_grouped_row_ratio_theorem_proved
            and self.backward_message_order_terminal_independent
            and self.endpoint_spatial_weight_cancellation_proved
            and self.correct_relative_message_coordinate
            == "g_j=h_j/sqrt(W_spatial)"
            and self.kinetic_23_cycle_spacing_uniform_order_proved
            and self.kinetic_markov_common_mass
            == kinetic.markov_common_mass
            == Fraction(1055, 3489) ** 46
            and not self.interior_spatial_feynman_kac_weights_included
            and not self.physical_grouped_two_sided_harnack_proved
            and not self.physical_spacing_uniform_backward_message_order_proved
            and stable_limit.validates()
            and self.uniform_positive_kernel_limit_criterion_proved
            and not self.physical_grouped_feynman_kac_uniform_limit_proved
            and not self.physical_limit_kernel_strictly_positive_proved
            and not self.global_floor_ceiling_potential_comparison_usable
            and self.first_open_obligation
            == "prove-spacing-uniform-feynman-kac-harnack-with-interior-spatial-weights"
        )


@cache
def physical_backward_message_order_frontier(
) -> PhysicalBackwardMessageOrderFrontier:
    """Return the exact uniform-order reduction and fail-closed physical gate."""

    kinetic = kinetic_boundary_message_uniform_order(Fraction(9, 10))
    frontier = PhysicalBackwardMessageOrderFrontier(
        carrier=enlarged_fine_boundary_carrier(),
        finite_grouped_row_ratio_theorem_proved=True,
        backward_message_order_terminal_independent=True,
        endpoint_spatial_weight_cancellation_proved=True,
        correct_relative_message_coordinate="g_j=h_j/sqrt(W_spatial)",
        kinetic_23_cycle_spacing_uniform_order_proved=True,
        kinetic_markov_common_mass=kinetic.markov_common_mass,
        interior_spatial_feynman_kac_weights_included=False,
        physical_grouped_two_sided_harnack_proved=False,
        physical_spacing_uniform_backward_message_order_proved=False,
        uniform_positive_kernel_limit_criterion_proved=True,
        physical_grouped_feynman_kac_uniform_limit_proved=False,
        physical_limit_kernel_strictly_positive_proved=False,
        global_floor_ceiling_potential_comparison_usable=False,
        first_open_obligation=(
            "prove-spacing-uniform-feynman-kac-harnack-with-interior-spatial-weights"
        ),
    )
    if not frontier.validates():
        raise AssertionError("the physical backward-message frontier drifted")
    return frontier


@dataclass(frozen=True)
class UniformKernelLimitMessageOrder:
    """Stable message order from a positive grouped-kernel limit."""

    limit_kernel: RationalMatrix
    approximating_kernel: RationalMatrix
    certified_uniform_error: Fraction
    actual_uniform_error: Fraction
    limit_floor: Fraction
    limit_ceiling: Fraction
    approximating_floor: Fraction
    approximating_ceiling: Fraction
    grouped_row_ratio_lower: Fraction
    grouped_row_ratio_upper: Fraction
    terminal_independent_markov_common_mass: Fraction
    strict_positive_margin: bool
    uniform_message_order_proved: bool

    def validates(self) -> bool:
        try:
            limit = _positive_matrix(self.limit_kernel)
            approximation = _positive_matrix(self.approximating_kernel)
        except ValueError:
            return False
        if (
            len(limit) != len(approximation)
            or len(limit[0]) != len(approximation[0])
        ):
            return False
        error = max(
            abs(limit[row][column] - approximation[row][column])
            for row in range(len(limit))
            for column in range(len(limit[0]))
        )
        floor = min(value for row in limit for value in row)
        ceiling = max(value for row in limit for value in row)
        lower = floor - self.certified_uniform_error
        upper = ceiling + self.certified_uniform_error
        row_lower = lower / upper
        row_upper = upper / lower
        return (
            self.certified_uniform_error >= error
            and self.actual_uniform_error == error
            and self.limit_floor == floor
            and self.limit_ceiling == ceiling
            and 0 <= self.certified_uniform_error < floor
            and self.approximating_floor == lower > 0
            and self.approximating_ceiling == upper
            and self.grouped_row_ratio_lower == row_lower
            and self.grouped_row_ratio_upper == row_upper
            and self.terminal_independent_markov_common_mass
            == row_lower / row_upper
            == (lower / upper) ** 2
            and self.strict_positive_margin
            and self.uniform_message_order_proved
        )


def uniform_kernel_limit_message_order(
    limit_kernel: Iterable[Iterable[int | Fraction]],
    approximating_kernel: Iterable[Iterable[int | Fraction]],
    certified_uniform_error: Fraction,
) -> UniformKernelLimitMessageOrder:
    """Promote one uniform positive-kernel approximation to message order."""

    limit = _positive_matrix(limit_kernel)
    approximation = _positive_matrix(approximating_kernel)
    if (
        len(limit) != len(approximation)
        or len(limit[0]) != len(approximation[0])
    ):
        raise ValueError("the limit and approximating kernels must have one shape")
    error = max(
        abs(limit[row][column] - approximation[row][column])
        for row in range(len(limit))
        for column in range(len(limit[0]))
    )
    floor = min(value for row in limit for value in row)
    ceiling = max(value for row in limit for value in row)
    if certified_uniform_error < error or not certified_uniform_error < floor:
        raise ValueError("the uniform error must be certified below the limit floor")
    lower = floor - certified_uniform_error
    upper = ceiling + certified_uniform_error
    certificate = UniformKernelLimitMessageOrder(
        limit_kernel=limit,
        approximating_kernel=approximation,
        certified_uniform_error=certified_uniform_error,
        actual_uniform_error=error,
        limit_floor=floor,
        limit_ceiling=ceiling,
        approximating_floor=lower,
        approximating_ceiling=upper,
        grouped_row_ratio_lower=lower / upper,
        grouped_row_ratio_upper=upper / lower,
        terminal_independent_markov_common_mass=(lower / upper) ** 2,
        strict_positive_margin=True,
        uniform_message_order_proved=True,
    )
    if not certificate.validates():
        raise AssertionError("the uniform kernel-limit message order drifted")
    return certificate
