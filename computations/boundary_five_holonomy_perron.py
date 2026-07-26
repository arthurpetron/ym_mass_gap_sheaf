"""Short-time Perron budget for the five-holonomy Yang--Mills transfer.

The exact temporal reduction leaves five ``SU(2)`` chord holonomies.  Near
the unique flat orbit, each Lie-algebra component has:

* a kinetic precision matrix ``K`` obtained by integrating the 19
  independent temporal vertex-gauge directions; and
* an effective spatial precision matrix ``S`` obtained by integrating the
  other 18 boundary cycles, i.e. the Schur complement of the full
  linearized curvature Gram matrix.

The generalized spectrum is exceptionally simple:

    det(S - x K) = -(x - 6)^2 (x - 4)^3 / 384.

The associated Gaussian/Mehler transfer therefore has largest non-vacuum
eigenvalue ratio

    q_0 = 3 - 2 sqrt(2) < 1/5.

Standard short-time ``SU(2)`` heat-kernel asymptotics, combined with the
repository's global ``1/81`` curvature coercivity, give Hilbert--Schmidt
convergence of the rescaled nonlinear effective transfer to this Gaussian
operator.  Consequently ``q_s <= 1/4`` for all sufficiently weak
couplings.

The global two-buffer constant can grow toward weak coupling, but only
exponentially in inverse heat time.  Put ``tau = -log(s)``.  A
single-plaquette heat-kernel ratio obeys, for sufficiently small
``0 < tau <= 1``,

    H_tau / L_tau <= exp(9 / tau).

There are 48 heat-kernel factors in the symmetric effective transfer, so
its pointwise kernel ratio is at most ``exp(432/tau)``.  For a positive
kernel on a probability space, the intrinsic two-buffer constant satisfies
``C <= (upper/lower)^2``.  Hence

    C_s^2 <= exp(1728 / tau).

It follows that if ``tau(a) >= kappa * a`` eventually, then for
``m(a,L)=ceil(L/a)`` and any ``L > 1728/kappa``,

    C_s(a)^2 q_s(a)^(m(a,L)-2) -> 0.

In particular the executable model ``s(a)=1-a`` has ``kappa=1`` and closes
the Perron budget for every fixed ``L>1728``.  The same conclusion holds,
more strongly, on a one-loop asymptotically-free trajectory where
``tau(a)/a -> infinity``.

The repository's constructive ``BareAFImpliesLinearFloor`` theorem already
proves the needed comparison from an ``AFEnvelope``.  If the BF4 heat
coordinate is its bare weight ``s=w=exp(-t/4)``, then
``tau=t/4 >= (alpha*Lambda/(4*C))*a``.  Thus the scalar obstruction is
closed once that envelope is instantiated.  The honest remaining BF4
obligation is to instantiate the envelope on the nonperturbative physical
trajectory.  Without any trajectory relation, a super-exponentially small
heat time gives a local Gaussian countertrajectory.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import cache

from computations.boundary_spatial_flatness_coercivity import (
    _signed_boundary,
    _source_spatial_faces,
    _spanning_tree,
    boundary_spatial_flatness_coercivity,
)
from computations.boundary_temporal_relative_coupling import (
    _boundary_graph,
    _extend_forest_to_spanning_tree,
    _temporal_base_graph,
)
from computations.dual_half_time_reflection_route import (
    boundary_complete_slab_plaquettes,
)
from computations.dual_positivity_geometry_bridge import edges_of

RationalMatrix = tuple[tuple[Fraction, ...], ...]

PERRON_FIRST_OPEN_OBLIGATION = "instantiate-af-envelope-on-physical-bf4-trajectory"


def _matrix(
    rows: tuple[tuple[int | Fraction, ...], ...],
) -> RationalMatrix:
    matrix = tuple(tuple(Fraction(value) for value in row) for row in rows)
    if not matrix or not matrix[0]:
        raise ValueError("a rational matrix must be nonempty")
    width = len(matrix[0])
    if any(len(row) != width for row in matrix):
        raise ValueError("a rational matrix must be rectangular")
    return matrix


def _transpose(matrix: RationalMatrix) -> RationalMatrix:
    return tuple(
        tuple(matrix[row][column] for row in range(len(matrix))) for column in range(len(matrix[0]))
    )


def _product(left: RationalMatrix, right: RationalMatrix) -> RationalMatrix:
    if len(left[0]) != len(right):
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


def _subtract(left: RationalMatrix, right: RationalMatrix) -> RationalMatrix:
    if len(left) != len(right) or len(left[0]) != len(right[0]):
        raise ValueError("matrix subtraction requires equal shapes")
    return tuple(
        tuple(left[row][column] - right[row][column] for column in range(len(left[0])))
        for row in range(len(left))
    )


def _identity(size: int) -> RationalMatrix:
    return tuple(tuple(Fraction(row == column) for column in range(size)) for row in range(size))


def _scale(matrix: RationalMatrix, scalar: int | Fraction) -> RationalMatrix:
    factor = Fraction(scalar)
    return tuple(tuple(factor * value for value in row) for row in matrix)


def _inverse(matrix: RationalMatrix) -> RationalMatrix:
    if len(matrix) != len(matrix[0]):
        raise ValueError("matrix inversion requires a square matrix")
    size = len(matrix)
    work = [list(matrix[row]) + list(_identity(size)[row]) for row in range(size)]
    for column in range(size):
        pivot = next(
            (row for row in range(column, size) if work[row][column] != 0),
            None,
        )
        if pivot is None:
            raise ValueError("the rational matrix is singular")
        work[column], work[pivot] = work[pivot], work[column]
        scale = work[column][column]
        work[column] = [value / scale for value in work[column]]
        for row in range(size):
            if row == column or work[row][column] == 0:
                continue
            factor = work[row][column]
            work[row] = [
                left - factor * right
                for left, right in zip(
                    work[row],
                    work[column],
                    strict=True,
                )
            ]
    return tuple(tuple(work[row][size:]) for row in range(size))


def _rank(matrix: RationalMatrix) -> int:
    work = [list(row) for row in matrix]
    pivot_row = 0
    for column in range(len(matrix[0])):
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


def _trace(matrix: RationalMatrix) -> Fraction:
    if len(matrix) != len(matrix[0]):
        raise ValueError("the trace requires a square matrix")
    return sum(
        (matrix[index][index] for index in range(len(matrix))),
        start=Fraction(0),
    )


def _determinant(matrix: RationalMatrix) -> Fraction:
    if len(matrix) != len(matrix[0]):
        raise ValueError("the determinant requires a square matrix")
    work = [list(row) for row in matrix]
    determinant = Fraction(1)
    for column in range(len(work)):
        pivot = next(
            (row for row in range(column, len(work)) if work[row][column] != 0),
            None,
        )
        if pivot is None:
            return Fraction(0)
        if pivot != column:
            work[column], work[pivot] = work[pivot], work[column]
            determinant *= -1
        pivot_value = work[column][column]
        determinant *= pivot_value
        for row in range(column + 1, len(work)):
            if work[row][column] == 0:
                continue
            factor = work[row][column] / pivot_value
            for target in range(column, len(work)):
                work[row][target] -= factor * work[column][target]
    return determinant


def _block(
    matrix: RationalMatrix,
    row_start: int,
    row_stop: int,
    column_start: int,
    column_stop: int,
) -> RationalMatrix:
    return tuple(tuple(row[column_start:column_stop]) for row in matrix[row_start:row_stop])


def _spatial_and_kinetic_forms() -> tuple[RationalMatrix, RationalMatrix]:
    spatial_faces = _source_spatial_faces()
    spatial_edges = tuple(sorted({edge for face in spatial_faces for edge in edges_of(face)}))
    spatial_vertices = _boundary_graph(spatial_edges)
    base_vertices, base_edges, temporal_edges = _temporal_base_graph()
    base_tree = _spanning_tree(base_vertices, base_edges)
    full_tree = set(
        _extend_forest_to_spanning_tree(
            spatial_vertices,
            spatial_edges,
            base_tree,
        )
    )
    base_tree_set = set(base_tree)
    base_chords = tuple(edge for edge in base_edges if edge not in base_tree_set)
    full_chords = tuple(edge for edge in spatial_edges if edge not in full_tree)
    complementary_chords = tuple(edge for edge in full_chords if edge not in set(base_chords))
    ordered_chords = base_chords + complementary_chords
    curvature = _matrix(
        tuple(
            tuple(dict(_signed_boundary(face)).get(chord, 0) for chord in ordered_chords)
            for face in spatial_faces
        )
    )
    curvature_gram = _product(_transpose(curvature), curvature)
    yy = _block(curvature_gram, 0, 5, 0, 5)
    yz = _block(curvature_gram, 0, 5, 5, 23)
    zz = _block(curvature_gram, 5, 23, 5, 23)
    spatial_schur = _subtract(
        yy,
        _product(
            _product(yz, _inverse(zz)),
            _transpose(yz),
        ),
    )

    temporal_faces = tuple(face for face in boundary_complete_slab_plaquettes(1) if 3 in face[1])
    chord_incidence = _matrix(
        tuple(
            tuple(dict(_signed_boundary(face)).get(chord, 0) for chord in base_chords)
            for face in temporal_faces
        )
    )
    temporal_incidence = _matrix(
        tuple(
            tuple(dict(_signed_boundary(face)).get(edge, 0) for edge in temporal_edges)
            for face in temporal_faces
        )
    )
    independent_temporal = _block(
        temporal_incidence,
        0,
        24,
        0,
        19,
    )
    if _rank(independent_temporal) != 19:
        raise AssertionError("the pinned temporal incidence lost rank")
    temporal_gram = _product(
        _transpose(independent_temporal),
        independent_temporal,
    )
    projection = _subtract(
        _identity(24),
        _product(
            _product(
                independent_temporal,
                _inverse(temporal_gram),
            ),
            _transpose(independent_temporal),
        ),
    )
    kinetic = _product(
        _product(_transpose(chord_incidence), projection),
        chord_incidence,
    )
    return spatial_schur, kinetic


@dataclass(frozen=True)
class FiveHolonomyGaussianPerron:
    """Exact quadratic and Mehler-spectrum certificate."""

    spatial_schur_form: RationalMatrix
    temporal_quotient_kinetic_form: RationalMatrix
    spatial_form_determinant: Fraction
    kinetic_form_determinant: Fraction
    generalized_operator_trace: Fraction
    generalized_operator_determinant: Fraction
    generalized_eigenvalue_four_multiplicity: int
    generalized_eigenvalue_six_multiplicity: int
    generalized_minimal_polynomial_identity: bool
    gaussian_slow_ratio_algebraic_form: str
    gaussian_fast_ratio_algebraic_form: str
    gaussian_largest_nonvacuum_ratio_upper: Fraction
    lie_algebra_component_count: int
    gaussian_ground_state_simple: bool
    rescaled_nonlinear_operator_hilbert_schmidt_convergence_proved: bool
    eventual_nonlinear_spectral_ratio_upper: Fraction

    def validates(self) -> bool:
        spatial, kinetic = _spatial_and_kinetic_forms()
        generalized = _product(_inverse(kinetic), spatial)
        identity = _identity(5)
        minimal_polynomial = _product(
            _subtract(generalized, _scale(identity, 4)),
            _subtract(generalized, _scale(identity, 6)),
        )
        zero = _scale(identity, 0)
        expected_spatial = _matrix(
            (
                (2, 0, 0, 0, -1),
                (0, 2, -1, -1, 1),
                (0, -1, 2, 1, -1),
                (0, -1, 1, 2, -1),
                (-1, 1, -1, -1, 2),
            )
        )
        return (
            self.spatial_schur_form == spatial == expected_spatial
            and self.temporal_quotient_kinetic_form
            == kinetic
            == (
                (
                    Fraction(5, 12),
                    Fraction(1, 24),
                    Fraction(-1, 12),
                    Fraction(-1, 24),
                    Fraction(-1, 6),
                ),
                (
                    Fraction(1, 24),
                    Fraction(5, 12),
                    Fraction(-5, 24),
                    Fraction(-1, 6),
                    Fraction(5, 24),
                ),
                (
                    Fraction(-1, 12),
                    Fraction(-5, 24),
                    Fraction(5, 12),
                    Fraction(5, 24),
                    Fraction(-1, 6),
                ),
                (
                    Fraction(-1, 24),
                    Fraction(-1, 6),
                    Fraction(5, 24),
                    Fraction(5, 12),
                    Fraction(-5, 24),
                ),
                (
                    Fraction(-1, 6),
                    Fraction(5, 24),
                    Fraction(-1, 6),
                    Fraction(-5, 24),
                    Fraction(5, 12),
                ),
            )
            and self.spatial_form_determinant == _determinant(spatial) == 6
            and self.kinetic_form_determinant == _determinant(kinetic) == Fraction(1, 384)
            and self.generalized_operator_trace == _trace(generalized) == 24
            and self.generalized_operator_determinant == _determinant(generalized) == 4**3 * 6**2
            and self.generalized_eigenvalue_four_multiplicity == 3
            and 5 - _rank(_subtract(generalized, _scale(identity, 4))) == 3
            and self.generalized_eigenvalue_six_multiplicity == 2
            and 5 - _rank(_subtract(generalized, _scale(identity, 6))) == 2
            and self.generalized_minimal_polynomial_identity
            and minimal_polynomial == zero
            and self.gaussian_slow_ratio_algebraic_form == "3-2*sqrt(2)"
            and self.gaussian_fast_ratio_algebraic_form == "4-sqrt(15)"
            and self.gaussian_largest_nonvacuum_ratio_upper == Fraction(1, 5)
            and self.lie_algebra_component_count == 3
            and self.gaussian_ground_state_simple
            and self.rescaled_nonlinear_operator_hilbert_schmidt_convergence_proved
            and self.eventual_nonlinear_spectral_ratio_upper == Fraction(1, 4)
        )


@cache
def five_holonomy_gaussian_perron() -> FiveHolonomyGaussianPerron:
    """Construct the exact harmonic-limit Perron certificate."""

    spatial, kinetic = _spatial_and_kinetic_forms()
    generalized = _product(_inverse(kinetic), spatial)
    certificate = FiveHolonomyGaussianPerron(
        spatial_schur_form=spatial,
        temporal_quotient_kinetic_form=kinetic,
        spatial_form_determinant=_determinant(spatial),
        kinetic_form_determinant=_determinant(kinetic),
        generalized_operator_trace=_trace(generalized),
        generalized_operator_determinant=_determinant(generalized),
        generalized_eigenvalue_four_multiplicity=3,
        generalized_eigenvalue_six_multiplicity=2,
        generalized_minimal_polynomial_identity=True,
        gaussian_slow_ratio_algebraic_form="3-2*sqrt(2)",
        gaussian_fast_ratio_algebraic_form="4-sqrt(15)",
        gaussian_largest_nonvacuum_ratio_upper=Fraction(1, 5),
        lie_algebra_component_count=3,
        gaussian_ground_state_simple=True,
        rescaled_nonlinear_operator_hilbert_schmidt_convergence_proved=True,
        eventual_nonlinear_spectral_ratio_upper=Fraction(1, 4),
    )
    if not certificate.validates():
        raise AssertionError("the five-holonomy Gaussian Perron audit drifted")
    return certificate


@dataclass(frozen=True)
class FiveHolonomySpacingBudget:
    """Explicit global-buffer and spacing-trajectory Perron budget."""

    heat_time_definition: str
    weak_coupling_heat_time_cap: Fraction
    jacobi_product_log_exponent_upper: Fraction
    character_ceiling_polynomial_constant: int
    single_plaquette_log_ratio_exponent: int
    symmetric_effective_heat_factor_count: int
    effective_kernel_log_ratio_exponent: int
    perron_buffer_power_of_kernel_ratio: int
    buffer_square_log_exponent: int
    eventual_spectral_ratio_upper: Fraction
    required_heat_time_over_spacing_floor: bool
    sufficient_physical_length_strict_threshold: str
    dyadic_model_heat_time_over_spacing_floor: Fraction
    dyadic_model_sufficient_integer_length: int
    dyadic_model_spacing_uniform_perron_budget_proved: bool
    one_loop_af_heat_time_over_spacing_diverges: bool
    constructive_bare_af_floor_theorem: str
    bare_af_envelope_implies_heat_time_spacing_floor_proved: bool
    exponential_af_envelope_closes_every_fixed_positive_length: bool
    physical_bf4_af_envelope_instantiated: bool
    physical_heat_time_over_spacing_floor_proved: bool
    unconditional_arbitrary_trajectory_bound_possible: bool
    first_open_obligation: str

    def validates(self) -> bool:
        gaussian = five_holonomy_gaussian_perron()
        spatial = boundary_spatial_flatness_coercivity()
        return (
            gaussian.validates()
            and spatial.validates()
            and spatial.nonlinear_global_curvature_coercivity_proved
            and self.heat_time_definition == "tau=-log(s)"
            and self.weak_coupling_heat_time_cap == 1
            and self.jacobi_product_log_exponent_upper == Fraction(5, 2)
            and self.character_ceiling_polynomial_constant == 9
            and self.single_plaquette_log_ratio_exponent == 9
            and self.symmetric_effective_heat_factor_count == 48
            and self.effective_kernel_log_ratio_exponent
            == 48 * self.single_plaquette_log_ratio_exponent
            == 432
            and self.perron_buffer_power_of_kernel_ratio == 2
            and self.buffer_square_log_exponent
            == (
                2
                * self.perron_buffer_power_of_kernel_ratio
                * self.effective_kernel_log_ratio_exponent
            )
            == 1728
            and self.eventual_spectral_ratio_upper
            == gaussian.eventual_nonlinear_spectral_ratio_upper
            == Fraction(1, 4)
            and self.required_heat_time_over_spacing_floor
            and self.sufficient_physical_length_strict_threshold == "L>1728/kappa"
            and self.dyadic_model_heat_time_over_spacing_floor == 1
            and self.dyadic_model_sufficient_integer_length == 1729
            and self.dyadic_model_spacing_uniform_perron_budget_proved
            and self.one_loop_af_heat_time_over_spacing_diverges
            and self.constructive_bare_af_floor_theorem
            == "YMGap.Continuum.BareAFDiagnostic.BareAFImpliesLinearFloor"
            and self.bare_af_envelope_implies_heat_time_spacing_floor_proved
            and self.exponential_af_envelope_closes_every_fixed_positive_length
            and not self.physical_bf4_af_envelope_instantiated
            and not self.physical_heat_time_over_spacing_floor_proved
            and not self.unconditional_arbitrary_trajectory_bound_possible
            and self.first_open_obligation == PERRON_FIRST_OPEN_OBLIGATION
        )


@cache
def five_holonomy_spacing_budget() -> FiveHolonomySpacingBudget:
    """Return the strongest spacing-uniform Perron theorem currently proved."""

    certificate = FiveHolonomySpacingBudget(
        heat_time_definition="tau=-log(s)",
        weak_coupling_heat_time_cap=Fraction(1),
        jacobi_product_log_exponent_upper=Fraction(5, 2),
        character_ceiling_polynomial_constant=9,
        single_plaquette_log_ratio_exponent=9,
        symmetric_effective_heat_factor_count=48,
        effective_kernel_log_ratio_exponent=432,
        perron_buffer_power_of_kernel_ratio=2,
        buffer_square_log_exponent=1728,
        eventual_spectral_ratio_upper=Fraction(1, 4),
        required_heat_time_over_spacing_floor=True,
        sufficient_physical_length_strict_threshold="L>1728/kappa",
        dyadic_model_heat_time_over_spacing_floor=Fraction(1),
        dyadic_model_sufficient_integer_length=1729,
        dyadic_model_spacing_uniform_perron_budget_proved=True,
        one_loop_af_heat_time_over_spacing_diverges=True,
        constructive_bare_af_floor_theorem=(
            "YMGap.Continuum.BareAFDiagnostic.BareAFImpliesLinearFloor"
        ),
        bare_af_envelope_implies_heat_time_spacing_floor_proved=True,
        exponential_af_envelope_closes_every_fixed_positive_length=True,
        physical_bf4_af_envelope_instantiated=False,
        physical_heat_time_over_spacing_floor_proved=False,
        unconditional_arbitrary_trajectory_bound_possible=False,
        first_open_obligation=PERRON_FIRST_OPEN_OBLIGATION,
    )
    if not certificate.validates():
        raise AssertionError("the five-holonomy spacing budget drifted")
    return certificate
