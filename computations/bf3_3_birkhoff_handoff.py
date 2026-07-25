"""BF3.3: exact admissibility fences for the Birkhoff handoff.

BF3.1 constructs a positive cutoff-one reflected density, but that density is
not automatically a strict Birkhoff contraction.  This module audits the
three shortest proposed handoffs to BF4:

* using the 64-dimensional reflected density itself as the positive map;
* using the local reflected fusion Gram as a cutoff-uniform primitive;
* deleting the outside-representation blocks by taking a large cutoff.

All three shortcuts fail for exact, structural reasons.

The whole-slab density has 32 disconnected positive rank-one blocks.  Each
block has projective rate zero, but the full matrix has infinite projective
diameter because it does not mix cut signatures.

For the local reflected fusion Gram at cutoff ``N``, the two parity blocks
are strictly positive.  Nevertheless a concrete spin-``2``/spin-``4N``
cross-ratio has the lower bound

    (N + 1) (3 N^2 + 7 N + 1) / (18 N),

which grows quadratically.  Hence its Birkhoff rate tends to one; no
cutoff-independent ``q < 1`` can come from this primitive.

Finally, the first outside heat feature does decay at every fixed
``0 < s < 1``, but not uniformly in the coupling.  At

    s_N = 1 - 1 / (2 (N + 1) (N + 3))

Bernoulli's inequality gives

    (N + 2) s_N^((N + 1)(N + 3)) >= (N + 2) / 2.

Thus BF3.2 must supply a coupling-dependent cutoff schedule and a normalized
physical tail norm.  BF3.3 closes as an obstruction/admissibility milestone:
it specifies what a valid grouped physical handoff must contain, but does not
claim that BF3.2 or BF4 is closed.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from functools import cache
from typing import TypeAlias

from computations.exact_haar_network import sp_eval
from computations.local_face_projective_census import (
    local_face_fusion_multiplicity,
    local_face_projective_census,
)
from computations.rational_projective_diameter import audit_support_components
from computations.whole_corrected_slab_kraus import (
    binary_whole_slab_kraus_kernel,
)

RationalMatrix: TypeAlias = tuple[tuple[Fraction, ...], ...]

EXPECTED_FIXED_CUTOFF_RATES: tuple[tuple[int, Fraction], ...] = (
    (1, Fraction(7, 15)),
    (2, Fraction(19, 25)),
    (3, Fraction(1333, 1495)),
    (4, Fraction(2603, 2747)),
    (5, Fraction(1544, 1589)),
    (6, Fraction(38351, 38999)),
    (7, Fraction(1715, 1733)),
)


def evaluated_whole_slab_density(coupling: Fraction) -> RationalMatrix:
    """Evaluate the BF3.1 block density as one exact ``64 x 64`` matrix."""

    if not 0 < coupling < 1:
        raise ValueError("the heat coordinate must lie strictly between zero and one")
    kernel = binary_whole_slab_kraus_kernel()
    matrix = [
        [Fraction(0) for _column in range(kernel.boundary_dimension)]
        for _row in range(kernel.boundary_dimension)
    ]
    for block_index, block in enumerate(kernel.blocks):
        offset = 2 * block_index
        for row in range(2):
            for column in range(2):
                matrix[offset + row][offset + column] = sp_eval(
                    block.kernel[row][column],
                    coupling,
                )
    return tuple(tuple(row) for row in matrix)


@dataclass(frozen=True)
class WholeSlabDensityHandoffAudit:
    """Why componentwise rank-one contraction is not global mixing."""

    coupling: Fraction
    boundary_dimension: int
    support_component_count: int
    component_shape_census: tuple[tuple[tuple[int, int], int], ...]
    component_rate_census: tuple[tuple[Fraction, int], ...]
    cross_component_witness: tuple[int, int]
    every_component_rank_one: bool
    global_positive_rectangle: bool
    cut_signature_mixing: bool
    global_projective_diameter_finite: bool

    def validates(self) -> bool:
        matrix = evaluated_whole_slab_density(self.coupling)
        support = audit_support_components(matrix)
        shapes = Counter(
            (len(certificate.rows), len(certificate.columns))
            for certificate in support.certificates
        )
        rates = Counter(certificate.q for certificate in support.certificates)
        first, second = self.cross_component_witness
        determinants_vanish = all(
            matrix[offset][offset] * matrix[offset + 1][offset + 1]
            == matrix[offset][offset + 1] * matrix[offset + 1][offset]
            for offset in range(0, len(matrix), 2)
        )
        cross_zero = (
            0 <= first < len(matrix)
            and 0 <= second < len(matrix)
            and matrix[first][first] > 0
            and matrix[second][second] > 0
            and matrix[first][second] == 0
            and matrix[second][first] == 0
        )
        return (
            self.boundary_dimension == len(matrix) == 64
            and self.support_component_count
            == len(support.certificates)
            == 32
            and not support.obstructed_components
            and self.component_shape_census == tuple(sorted(shapes.items()))
            == (((2, 2), 32),)
            and self.component_rate_census == tuple(sorted(rates.items()))
            == ((Fraction(0), 32),)
            and self.every_component_rank_one
            and determinants_vanish
            and cross_zero
            and not self.global_positive_rectangle
            and not self.cut_signature_mixing
            and not self.global_projective_diameter_finite
        )


@cache
def whole_slab_density_handoff_audit() -> WholeSlabDensityHandoffAudit:
    """Return the exact support audit at one arbitrary positive rational ``s``."""

    matrix = evaluated_whole_slab_density(Fraction(1, 2))
    support = audit_support_components(matrix)
    shapes = Counter(
        (len(certificate.rows), len(certificate.columns))
        for certificate in support.certificates
    )
    rates = Counter(certificate.q for certificate in support.certificates)
    audit = WholeSlabDensityHandoffAudit(
        coupling=Fraction(1, 2),
        boundary_dimension=len(matrix),
        support_component_count=len(support.certificates),
        component_shape_census=tuple(sorted(shapes.items())),
        component_rate_census=tuple(sorted(rates.items())),
        cross_component_witness=(0, 2),
        every_component_rank_one=True,
        global_positive_rectangle=False,
        cut_signature_mixing=False,
        global_projective_diameter_finite=False,
    )
    if not audit.validates():
        raise AssertionError("the BF3.1 density support audit drifted")
    return audit


def diagonal_packet_spin_two_multiplicity(first: int, second: int) -> int:
    """Closed multiplicity for the packet ``(a,a,c,c)`` and output spin two."""

    if first < 0 or second < 0:
        raise ValueError("spins must be nonnegative")
    if first == second:
        return 3 * first
    return 3 * min(first, second) + 1


def restricted_spin_two_corner(cutoff: int) -> int:
    """Sum the squared diagonal-packet multiplicities inside ``G_N[2,2]``."""

    if cutoff < 1:
        raise ValueError("the spin-two witness requires cutoff at least one")
    return sum(
        diagonal_packet_spin_two_multiplicity(first, second) ** 2
        for first in range(cutoff + 1)
        for second in range(cutoff + 1)
    )


def restricted_spin_two_corner_closed_form(cutoff: int) -> int:
    """The exact polynomial value of :func:`restricted_spin_two_corner`."""

    if cutoff < 1:
        raise ValueError("the spin-two witness requires cutoff at least one")
    return cutoff * (cutoff + 1) * (
        3 * cutoff * cutoff + 7 * cutoff + 1
    ) // 2


@dataclass(frozen=True)
class LocalGramSpreadLowerWitness:
    """One all-cutoff cross-ratio lower witness for the reflected local Gram."""

    cutoff: int
    low_spin: int
    high_spin: int
    restricted_low_corner: int
    high_corner: int
    mixed_corner: int
    spread_lower_bound: Fraction
    rate_lower_bound: Fraction
    quadratic_spread_floor: Fraction
    quadratic_rate_floor: Fraction

    def validates(self) -> bool:
        if self.cutoff < 1:
            return False
        closed = restricted_spin_two_corner_closed_form(self.cutoff)
        spread = Fraction(closed, (3 * self.cutoff) ** 2)
        quadratic = Fraction(self.cutoff * self.cutoff, 6)
        quadratic_rate = (quadratic - 1) / (quadratic + 1)
        return (
            self.low_spin == 2
            and self.high_spin == 4 * self.cutoff
            and self.restricted_low_corner
            == restricted_spin_two_corner(self.cutoff)
            == closed
            and self.high_corner == 1
            and self.mixed_corner == 3 * self.cutoff
            and self.spread_lower_bound == spread
            and self.rate_lower_bound == (spread - 1) / (spread + 1)
            and self.quadratic_spread_floor == quadratic
            and spread >= quadratic
            and self.quadratic_rate_floor == quadratic_rate
            and self.rate_lower_bound >= quadratic_rate
        )


def local_gram_spread_lower_witness(cutoff: int) -> LocalGramSpreadLowerWitness:
    """Construct the exact quadratic-growth cross-ratio witness."""

    restricted = restricted_spin_two_corner_closed_form(cutoff)
    spread = Fraction(restricted, (3 * cutoff) ** 2)
    quadratic = Fraction(cutoff * cutoff, 6)
    witness = LocalGramSpreadLowerWitness(
        cutoff=cutoff,
        low_spin=2,
        high_spin=4 * cutoff,
        restricted_low_corner=restricted,
        high_corner=1,
        mixed_corner=3 * cutoff,
        spread_lower_bound=spread,
        rate_lower_bound=(spread - 1) / (spread + 1),
        quadratic_spread_floor=quadratic,
        quadratic_rate_floor=(quadratic - 1) / (quadratic + 1),
    )
    if not witness.validates():
        raise AssertionError("the local Gram lower witness drifted")
    return witness


def direct_multiplicity_identity_holds_through(max_cutoff: int) -> bool:
    """Check the packet formula directly against fusion arithmetic."""

    if max_cutoff < 1:
        raise ValueError("the direct check requires a positive cutoff")
    return all(
        local_face_fusion_multiplicity(
            (first, first, second, second),
            2,
            cutoff,
        )
        == diagonal_packet_spin_two_multiplicity(first, second)
        for cutoff in range(1, max_cutoff + 1)
        for first in range(cutoff + 1)
        for second in range(cutoff + 1)
    ) and all(
        local_face_fusion_multiplicity(
            (cutoff, cutoff, cutoff, cutoff),
            4 * cutoff,
            cutoff,
        )
        == 1
        and local_face_fusion_multiplicity(
            (cutoff, cutoff, cutoff, cutoff),
            2,
            cutoff,
        )
        == 3 * cutoff
        for cutoff in range(1, max_cutoff + 1)
    )


@dataclass(frozen=True)
class UniformRateCounterexample:
    """Constructive response to any proposed cutoff-independent ``q < 1``."""

    proposed_rate: Fraction
    counter_cutoff: int
    quadratic_rate_floor: Fraction
    exact_rate_lower_bound: Fraction

    def validates(self) -> bool:
        if not 0 <= self.proposed_rate < 1 or self.counter_cutoff < 3:
            return False
        witness = local_gram_spread_lower_witness(self.counter_cutoff)
        return (
            self.quadratic_rate_floor == witness.quadratic_rate_floor
            and self.exact_rate_lower_bound == witness.rate_lower_bound
            and self.exact_rate_lower_bound
            >= self.quadratic_rate_floor
            > self.proposed_rate
        )


def counterexample_to_uniform_rate(rate: Fraction) -> UniformRateCounterexample:
    """Return a cutoff whose exact lower rate exceeds a proposed ``q < 1``."""

    if not 0 <= rate < 1:
        raise ValueError("a proposed Birkhoff rate must lie in [0, 1)")
    cutoff = 3
    while Fraction(cutoff * cutoff - 6, cutoff * cutoff + 6) <= rate:
        cutoff += 1
    witness = local_gram_spread_lower_witness(cutoff)
    counterexample = UniformRateCounterexample(
        proposed_rate=rate,
        counter_cutoff=cutoff,
        quadratic_rate_floor=witness.quadratic_rate_floor,
        exact_rate_lower_bound=witness.rate_lower_bound,
    )
    if not counterexample.validates():
        raise AssertionError("the uniform-rate counterexample drifted")
    return counterexample


@cache
def observed_fixed_cutoff_rates() -> tuple[tuple[int, Fraction], ...]:
    """Return the exact componentwise rates through cutoff seven."""

    observed = tuple(
        (cutoff, local_face_projective_census(cutoff).gram_uniform_q)
        for cutoff, _expected in EXPECTED_FIXED_CUTOFF_RATES
    )
    if observed != EXPECTED_FIXED_CUTOFF_RATES:
        raise AssertionError("the fixed-cutoff projective census drifted")
    return observed


@dataclass(frozen=True)
class CouplingUniformCutoffFence:
    """An exact near-continuum witness against a cutoff-only heat-tail modulus."""

    cutoff: int
    outside_label: int
    heat_exponent: int
    coupling: Fraction
    leading_feature: Fraction
    bernoulli_lower_bound: Fraction

    def validates(self) -> bool:
        if self.cutoff < 0:
            return False
        exponent = (self.cutoff + 1) * (self.cutoff + 3)
        coupling = Fraction(1) - Fraction(1, 2 * exponent)
        feature = Fraction(self.cutoff + 2) * coupling**exponent
        return (
            self.outside_label == self.cutoff + 1
            and self.heat_exponent == exponent
            and self.coupling == coupling
            and 0 < self.coupling < 1
            and self.leading_feature == feature
            and self.bernoulli_lower_bound == Fraction(self.cutoff + 2, 2)
            and self.leading_feature >= self.bernoulli_lower_bound
        )


def coupling_uniform_cutoff_fence(cutoff: int) -> CouplingUniformCutoffFence:
    """Choose the exact rational coupling used by the Bernoulli fence."""

    if cutoff < 0:
        raise ValueError("cutoff must be nonnegative")
    exponent = (cutoff + 1) * (cutoff + 3)
    coupling = Fraction(1) - Fraction(1, 2 * exponent)
    witness = CouplingUniformCutoffFence(
        cutoff=cutoff,
        outside_label=cutoff + 1,
        heat_exponent=exponent,
        coupling=coupling,
        leading_feature=Fraction(cutoff + 2) * coupling**exponent,
        bernoulli_lower_bound=Fraction(cutoff + 2, 2),
    )
    if not witness.validates():
        raise AssertionError("the coupling-uniform cutoff fence drifted")
    return witness


@dataclass(frozen=True)
class FixedDistanceDiameterWitness:
    """Witness-bearing exact diameter data for one physical block length."""

    physical_distance: Fraction
    grouped_steps: int
    projective_spread: Fraction
    rational_rate: Fraction

    def validates(self) -> bool:
        return (
            self.physical_distance > 0
            and self.grouped_steps > 0
            and self.projective_spread >= 1
            and self.rational_rate
            == (self.projective_spread - 1) / (self.projective_spread + 1)
            and 0 <= self.rational_rate < 1
        )


@dataclass(frozen=True)
class BF4PhysicalHandoffRequirements:
    """Witness-bearing interface that the future BF3.2 map must inhabit."""

    all_label_physical_kernel_id: str | None
    invariant_positive_carrier_id: str | None
    signed_intertwiner_transport_id: str | None
    global_or_grouped_mixing_id: str | None
    physical_projective_norm_id: str | None
    fixed_distance_diameter: FixedDistanceDiameterWitness | None
    coherent_remainder_bound_id: str | None
    coupling_dependent_cutoff_schedule_id: str | None
    volume_uniform: bool

    @property
    def retained_signed_intertwiner_transport(self) -> bool:
        return self.signed_intertwiner_transport_id is not None

    def ready_for_bf4(self) -> bool:
        identifiers = (
            self.all_label_physical_kernel_id,
            self.invariant_positive_carrier_id,
            self.signed_intertwiner_transport_id,
            self.global_or_grouped_mixing_id,
            self.physical_projective_norm_id,
            self.coherent_remainder_bound_id,
            self.coupling_dependent_cutoff_schedule_id,
        )
        return (
            all(identifier is not None and bool(identifier) for identifier in identifiers)
            and self.fixed_distance_diameter is not None
            and self.fixed_distance_diameter.validates()
            and self.volume_uniform
        )


@dataclass(frozen=True)
class BF33Certificate:
    """Aggregate exact BF3.3 obstruction and handoff certificate."""

    whole_slab_density: WholeSlabDensityHandoffAudit
    fixed_cutoff_rates: tuple[tuple[int, Fraction], ...]
    direct_multiplicity_check_through: int
    uniform_rate_counterexamples: tuple[UniformRateCounterexample, ...]
    coupling_tail_fences: tuple[CouplingUniformCutoffFence, ...]
    handoff: BF4PhysicalHandoffRequirements
    exit_kind: str
    bf32_status: str
    next_gate: str

    def validates(self) -> bool:
        open_handoff_fields = (
            self.handoff.all_label_physical_kernel_id,
            self.handoff.invariant_positive_carrier_id,
            self.handoff.global_or_grouped_mixing_id,
            self.handoff.physical_projective_norm_id,
            self.handoff.coherent_remainder_bound_id,
            self.handoff.coupling_dependent_cutoff_schedule_id,
        )
        return (
            self.whole_slab_density.validates()
            and self.fixed_cutoff_rates == EXPECTED_FIXED_CUTOFF_RATES
            and self.direct_multiplicity_check_through == 7
            and direct_multiplicity_identity_holds_through(
                self.direct_multiplicity_check_through
            )
            and all(item.validates() for item in self.uniform_rate_counterexamples)
            and tuple(
                item.proposed_rate for item in self.uniform_rate_counterexamples
            )
            == (Fraction(1, 2), Fraction(9, 10), Fraction(99, 100))
            and all(item.validates() for item in self.coupling_tail_fences)
            and tuple(item.cutoff for item in self.coupling_tail_fences)
            == (1, 4, 16)
            and self.handoff.retained_signed_intertwiner_transport
            and all(field is None for field in open_handoff_fields)
            and self.handoff.fixed_distance_diameter is None
            and not self.handoff.volume_uniform
            and not self.handoff.ready_for_bf4()
            and self.exit_kind == "exact-obstruction-and-required-repair"
            and self.bf32_status == "open-all-label-physical-kernel-and-remainder"
            and self.next_gate == "BF3.2-before-BF4"
        )


@cache
def bf33_certificate() -> BF33Certificate:
    """Return the complete BF3.3 admissibility/obstruction certificate."""

    certificate = BF33Certificate(
        whole_slab_density=whole_slab_density_handoff_audit(),
        fixed_cutoff_rates=observed_fixed_cutoff_rates(),
        direct_multiplicity_check_through=7,
        uniform_rate_counterexamples=tuple(
            counterexample_to_uniform_rate(rate)
            for rate in (Fraction(1, 2), Fraction(9, 10), Fraction(99, 100))
        ),
        coupling_tail_fences=tuple(
            coupling_uniform_cutoff_fence(cutoff)
            for cutoff in (1, 4, 16)
        ),
        handoff=BF4PhysicalHandoffRequirements(
            all_label_physical_kernel_id=None,
            invariant_positive_carrier_id=None,
            signed_intertwiner_transport_id=(
                "BF3.1-fundamental-adjacent-swap-transport"
            ),
            global_or_grouped_mixing_id=None,
            physical_projective_norm_id=None,
            fixed_distance_diameter=None,
            coherent_remainder_bound_id=None,
            coupling_dependent_cutoff_schedule_id=None,
            volume_uniform=False,
        ),
        exit_kind="exact-obstruction-and-required-repair",
        bf32_status="open-all-label-physical-kernel-and-remainder",
        next_gate="BF3.2-before-BF4",
    )
    if not certificate.validates():
        raise AssertionError("the aggregate BF3.3 certificate drifted")
    return certificate
