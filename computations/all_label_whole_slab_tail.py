"""BF3.2: constructive all-label tail for the exact whole-slab Haar kernel.

For a fixed corrected slab, every matrix coefficient of the all-label Haar
kernel is an absolutely convergent character sum.  The proof uses only the
literal Haar integrand and the sharp elementary character bound

    |chi_n(g)| <= n + 1.

With heat coordinate ``0 < s < 1``, one fine plaquette is therefore
dominated by

    h_n(s) = (n + 1)^2 s^(n(n+2)).

The ratio ``h_(n+1) / h_n`` decreases in ``n``.  Past cutoff ``N`` the full
tail is bounded by the first omitted term divided by one minus the exact
rational ratio.  Tensorizing over the 72 plaquettes gives a computable
Cauchy modulus for every whole-slab Haar coefficient.  Dividing an external
Wilson coefficient by the product of its representation dimensions cancels
all dependence on the external labels.

This is a genuine fixed-block all-label completion of the BF3.1 finite sums.
A differentiated-Jacobi-product floor makes the normalized local truncation
bound constructive for every rational ``0 < s < 1``.  The heat-weighted
Peter--Weyl feature map then lifts that ``L1`` tail to the trace norm of the
BF2 reflected boundary Gram, simultaneously controlling all coherent
``P/Q`` corners and every signed unitary recoupling.

It is not the full BF3.2 exit certificate.  The resulting local theorem
controls representation truncation of an exact conditional Haar law, not
the actual fine-pushforward versus coarse-Gibbs RG remainder.  The latter is
the remaining BF3.2 obstruction before the kernel can be passed to BF4.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import cache
from itertools import product
from math import prod
from typing import TypeAlias

from computations.corrected_slab_haar_network import corrected_slab_haar_complex
from computations.exact_haar_network import casimir4, chi
from computations.hypercube4d_survey import exact_constant
from computations.whole_corrected_slab_kraus import coarse_face_paths

WHOLE_SLAB_FACE_COUNT = 72
CoarseLabels: TypeAlias = tuple[int, ...]


def heat_character_sup_term(coupling: Fraction, label: int) -> Fraction:
    """Return ``(n+1)^2 s^(n(n+2))`` exactly."""

    if not 0 < coupling < 1:
        raise ValueError("the heat coordinate must lie strictly between zero and one")
    if label < 0:
        raise ValueError("a representation label must be nonnegative")
    return Fraction((label + 1) ** 2) * coupling ** (label * (label + 2))


def heat_character_tail_ratio(coupling: Fraction, cutoff: int) -> Fraction:
    """Ratio majorant beginning at the first omitted label ``cutoff + 1``."""

    if cutoff < 0:
        raise ValueError("cutoff must be nonnegative")
    # h_(N+2) / h_(N+1)
    return (
        Fraction((cutoff + 3) ** 2, (cutoff + 2) ** 2)
        * coupling ** (2 * cutoff + 5)
    )


@dataclass(frozen=True)
class SinglePlaquetteAllLabelTail:
    """Exact super-geometric bound for one SU(2) heat-character tail."""

    coupling: Fraction
    cutoff: int
    partial_sum: Fraction
    first_omitted: Fraction
    ratio: Fraction
    tail_bound: Fraction
    total_upper_bound: Fraction

    def validates(self) -> bool:
        if not 0 < self.coupling < 1 or self.cutoff < 0:
            return False
        partial = sum(
            (
                heat_character_sup_term(self.coupling, label)
                for label in range(self.cutoff + 1)
            ),
            start=Fraction(0),
        )
        first = heat_character_sup_term(self.coupling, self.cutoff + 1)
        ratio = heat_character_tail_ratio(self.coupling, self.cutoff)
        return (
            ratio < 1
            and self.partial_sum == partial
            and self.first_omitted == first
            and self.ratio == ratio
            and self.tail_bound == first / (1 - ratio)
            and self.total_upper_bound == partial + self.tail_bound
        )


def single_plaquette_all_label_tail(
    coupling: Fraction,
    cutoff: int,
) -> SinglePlaquetteAllLabelTail:
    """Construct the exact one-plaquette all-label tail certificate."""

    partial = sum(
        (
            heat_character_sup_term(coupling, label)
            for label in range(cutoff + 1)
        ),
        start=Fraction(0),
    )
    first = heat_character_sup_term(coupling, cutoff + 1)
    ratio = heat_character_tail_ratio(coupling, cutoff)
    if ratio >= 1:
        raise ValueError(
            "the selected cutoff is below the geometric-tail threshold"
        )
    certificate = SinglePlaquetteAllLabelTail(
        coupling=coupling,
        cutoff=cutoff,
        partial_sum=partial,
        first_omitted=first,
        ratio=ratio,
        tail_bound=first / (1 - ratio),
        total_upper_bound=partial + first / (1 - ratio),
    )
    if not certificate.validates():
        raise AssertionError("the single-plaquette all-label tail drifted")
    return certificate


def external_dimension(external_labels: tuple[int, ...]) -> int:
    """Product of dimensions of all inserted external Wilson characters."""

    if any(label < 0 for label in external_labels):
        raise ValueError("external labels must be nonnegative")
    return prod((label + 1 for label in external_labels), start=1)


def _validate_coarse_labels(coarse_labels: CoarseLabels) -> None:
    if len(coarse_labels) != len(coarse_face_paths()):
        raise ValueError("the whole slab has exactly nine coarse Wilson paths")
    if any(label < 0 for label in coarse_labels):
        raise ValueError("coarse Wilson labels must be nonnegative")


def finite_cutoff_whole_slab_haar_coefficient(
    coupling: Fraction,
    cutoff: int,
    coarse_labels: CoarseLabels,
) -> Fraction:
    """Evaluate one literal finite-cutoff whole-slab Haar coefficient.

    This is the definition-level exact evaluator.  It is intentionally
    exponential in the 72 face labels; production low-cutoff evaluations use
    BF3.1's incidence and fibre reductions.  Its role here is to give the
    all-label limit an actual computable sequence rather than a formal name.
    """

    if not 0 < coupling < 1:
        raise ValueError("the heat coordinate must lie strictly between zero and one")
    if cutoff < 0:
        raise ValueError("cutoff must be nonnegative")
    _validate_coarse_labels(coarse_labels)
    complex_, faces, _plaquettes = corrected_slab_haar_complex(1)
    external_factors = tuple(
        chi(label, complex_.holonomy_of(path))
        for label, path in zip(
            coarse_labels,
            coarse_face_paths(),
            strict=True,
        )
        if label
    )
    total = Fraction(0)
    for fine_labels in product(range(cutoff + 1), repeat=len(faces)):
        weight = prod(
            (
                Fraction(label + 1)
                * coupling ** casimir4(label)
                for label in fine_labels
            ),
            start=Fraction(1),
        )
        factors = [
            chi(label, complex_.holonomy_of(face))
            for label, face in zip(fine_labels, faces, strict=True)
            if label
        ]
        factors.extend(external_factors)
        amplitude = (
            exact_constant(complex_.contract_invariant(factors))
            if factors
            else Fraction(1)
        )
        total += weight * amplitude
    return total


@dataclass(frozen=True)
class ComputableAllLabelHaarCoefficient:
    """A Cauchy name for one all-label whole-slab Haar coefficient."""

    coupling: Fraction
    coarse_labels: CoarseLabels
    fine_face_count: int
    norm_weight: int
    approximation_kind: str
    cauchy_modulus_kind: str

    def approximation(self, cutoff: int) -> Fraction:
        return finite_cutoff_whole_slab_haar_coefficient(
            self.coupling,
            cutoff,
            self.coarse_labels,
        )

    def limit_error_bound(self, cutoff: int) -> Fraction:
        return whole_slab_all_label_cauchy_certificate(
            self.coupling,
            cutoff,
            self.coarse_labels,
        ).raw_coefficient_tail_bound

    def weighted_limit_error_bound(self, cutoff: int) -> Fraction:
        return self.limit_error_bound(cutoff) / self.norm_weight

    def validates(self) -> bool:
        try:
            _validate_coarse_labels(self.coarse_labels)
            sample_cutoff = 0
            while heat_character_tail_ratio(
                self.coupling,
                sample_cutoff,
            ) >= 1:
                sample_cutoff += 1
            sample = whole_slab_all_label_cauchy_certificate(
                self.coupling,
                sample_cutoff,
                self.coarse_labels,
            )
        except ValueError:
            return False
        return (
            0 < self.coupling < 1
            and self.fine_face_count == WHOLE_SLAB_FACE_COUNT
            and self.norm_weight == external_dimension(self.coarse_labels)
            and sample.external_dimension == self.norm_weight
            and self.approximation_kind
            == "literal-finite-Haar-sum-over-72-face-label-cube"
            and self.cauchy_modulus_kind
            == "dimension-weighted-super-geometric-character-tail"
        )


def computable_all_label_haar_coefficient(
    coupling: Fraction,
    coarse_labels: CoarseLabels,
) -> ComputableAllLabelHaarCoefficient:
    """Return the exact finite-approximation/Cauchy-modulus pair."""

    _validate_coarse_labels(coarse_labels)
    coefficient = ComputableAllLabelHaarCoefficient(
        coupling=coupling,
        coarse_labels=coarse_labels,
        fine_face_count=WHOLE_SLAB_FACE_COUNT,
        norm_weight=external_dimension(coarse_labels),
        approximation_kind="literal-finite-Haar-sum-over-72-face-label-cube",
        cauchy_modulus_kind=(
            "dimension-weighted-super-geometric-character-tail"
        ),
    )
    if not coefficient.validates():
        raise AssertionError("the computable all-label Haar coefficient drifted")
    return coefficient


@dataclass(frozen=True)
class WholeSlabAllLabelCauchyCertificate:
    """Cauchy modulus for one exact whole-slab Haar coefficient."""

    coupling: Fraction
    cutoff: int
    fine_face_count: int
    external_labels: tuple[int, ...]
    external_dimension: int
    plaquette_tail: SinglePlaquetteAllLabelTail
    raw_coefficient_tail_bound: Fraction
    dimension_weighted_tail_bound: Fraction
    fixed_block_volume: bool
    arbitrary_volume_uniform: bool
    literal_haar_character_bound: bool

    def validates(self) -> bool:
        if not self.plaquette_tail.validates():
            return False
        weighted = (
            self.fine_face_count
            * self.plaquette_tail.total_upper_bound
            ** (self.fine_face_count - 1)
            * self.plaquette_tail.tail_bound
        )
        return (
            self.coupling == self.plaquette_tail.coupling
            and self.cutoff == self.plaquette_tail.cutoff
            and self.fine_face_count == WHOLE_SLAB_FACE_COUNT
            and self.external_dimension == external_dimension(self.external_labels)
            and self.dimension_weighted_tail_bound == weighted
            and self.raw_coefficient_tail_bound
            == self.external_dimension * weighted
            and self.fixed_block_volume
            and not self.arbitrary_volume_uniform
            and self.literal_haar_character_bound
        )


def whole_slab_all_label_cauchy_certificate(
    coupling: Fraction,
    cutoff: int,
    external_labels: tuple[int, ...] = (),
) -> WholeSlabAllLabelCauchyCertificate:
    """Bound every term omitted from a 72-face cutoff cube."""

    plaquette = single_plaquette_all_label_tail(coupling, cutoff)
    weighted = (
        WHOLE_SLAB_FACE_COUNT
        * plaquette.total_upper_bound ** (WHOLE_SLAB_FACE_COUNT - 1)
        * plaquette.tail_bound
    )
    dimension = external_dimension(external_labels)
    certificate = WholeSlabAllLabelCauchyCertificate(
        coupling=coupling,
        cutoff=cutoff,
        fine_face_count=WHOLE_SLAB_FACE_COUNT,
        external_labels=external_labels,
        external_dimension=dimension,
        plaquette_tail=plaquette,
        raw_coefficient_tail_bound=dimension * weighted,
        dimension_weighted_tail_bound=weighted,
        fixed_block_volume=True,
        arbitrary_volume_uniform=False,
        literal_haar_character_bound=True,
    )
    if not certificate.validates():
        raise AssertionError("the whole-slab all-label Cauchy certificate drifted")
    return certificate


@dataclass(frozen=True)
class CouplingDependentCutoffPoint:
    """A constructive cutoff selected for one coupling and tolerance."""

    coupling: Fraction
    tolerance: Fraction
    cutoff: int
    tail_bound: Fraction
    previous_cutoff_fails: bool

    def validates(self) -> bool:
        if not 0 < self.coupling < 1 or self.tolerance <= 0 or self.cutoff < 0:
            return False
        current = whole_slab_all_label_cauchy_certificate(
            self.coupling,
            self.cutoff,
        )
        if current.dimension_weighted_tail_bound > self.tolerance:
            return False
        if self.cutoff == 0:
            previous_fails = True
        else:
            try:
                previous = whole_slab_all_label_cauchy_certificate(
                    self.coupling,
                    self.cutoff - 1,
                )
            except ValueError:
                previous_fails = True
            else:
                previous_fails = (
                    previous.dimension_weighted_tail_bound > self.tolerance
                )
        return (
            self.tail_bound == current.dimension_weighted_tail_bound
            and self.previous_cutoff_fails == previous_fails
            and previous_fails
        )


def coupling_dependent_cutoff(
    coupling: Fraction,
    tolerance: Fraction,
) -> CouplingDependentCutoffPoint:
    """Return the least cutoff certified by the fixed-block Cauchy modulus."""

    if not 0 < coupling < 1:
        raise ValueError("the heat coordinate must lie strictly between zero and one")
    if tolerance <= 0:
        raise ValueError("the requested tolerance must be positive")
    cutoff = 0
    while True:
        try:
            certificate = whole_slab_all_label_cauchy_certificate(
                coupling,
                cutoff,
            )
        except ValueError:
            cutoff += 1
            continue
        if certificate.dimension_weighted_tail_bound <= tolerance:
            point = CouplingDependentCutoffPoint(
                coupling=coupling,
                tolerance=tolerance,
                cutoff=cutoff,
                tail_bound=certificate.dimension_weighted_tail_bound,
                previous_cutoff_fails=True,
            )
            if not point.validates():
                raise AssertionError("the coupling-dependent cutoff drifted")
            return point
        cutoff += 1


@dataclass(frozen=True)
class StrongCouplingNormalizedTail:
    """Boundary-uniform conditional Gibbs tail in the positivity corridor.

    Conditioning the ambient lattice law on every link outside the corrected
    slab removes all plaquette factors disjoint from the slab.  The remaining
    holonomies may contain fixed boundary links, but the character estimate is
    uniform in those holonomies.  Thus this fixed 72-face estimate is also
    uniform in the ambient finite volume.  It is still only a truncation-tail
    estimate, not a bound on the fine/coarse RG remainder.
    """

    coupling: Fraction
    cutoff: int
    fine_face_count: int
    plaquette_excitation_upper: Fraction
    plaquette_density_floor: Fraction
    partition_floor: Fraction
    unnormalized_density_l1_tail: Fraction
    normalized_total_variation_tail: Fraction
    truncated_density_positive: bool
    boundary_holonomy_uniform: bool
    ambient_volume_independent: bool
    actual_rg_remainder: bool

    def validates(self) -> bool:
        tail = single_plaquette_all_label_tail(self.coupling, self.cutoff)
        excitation = tail.total_upper_bound - 1
        if not 0 <= excitation < 1:
            return False
        floor = 1 - excitation
        density_tail = (
            self.fine_face_count
            * tail.total_upper_bound ** (self.fine_face_count - 1)
            * tail.tail_bound
        )
        return (
            self.fine_face_count == WHOLE_SLAB_FACE_COUNT
            and self.plaquette_excitation_upper == excitation
            and self.plaquette_density_floor == floor
            and self.partition_floor == floor**self.fine_face_count
            and self.unnormalized_density_l1_tail == density_tail
            and self.normalized_total_variation_tail
            == 2 * density_tail / self.partition_floor
            and self.truncated_density_positive
            and self.boundary_holonomy_uniform
            and self.ambient_volume_independent
            and not self.actual_rg_remainder
        )


def strong_coupling_normalized_tail(
    coupling: Fraction,
    cutoff: int,
) -> StrongCouplingNormalizedTail:
    """Lift the character tail to normalized Gibbs total variation."""

    tail = single_plaquette_all_label_tail(coupling, cutoff)
    excitation = tail.total_upper_bound - 1
    if not 0 <= excitation < 1:
        raise ValueError(
            "the elementary character lower bound is outside its positivity corridor"
        )
    floor = 1 - excitation
    density_tail = (
        WHOLE_SLAB_FACE_COUNT
        * tail.total_upper_bound ** (WHOLE_SLAB_FACE_COUNT - 1)
        * tail.tail_bound
    )
    certificate = StrongCouplingNormalizedTail(
        coupling=coupling,
        cutoff=cutoff,
        fine_face_count=WHOLE_SLAB_FACE_COUNT,
        plaquette_excitation_upper=excitation,
        plaquette_density_floor=floor,
        partition_floor=floor**WHOLE_SLAB_FACE_COUNT,
        unnormalized_density_l1_tail=density_tail,
        normalized_total_variation_tail=2 * density_tail / floor**WHOLE_SLAB_FACE_COUNT,
        truncated_density_positive=True,
        boundary_holonomy_uniform=True,
        ambient_volume_independent=True,
        actual_rg_remainder=False,
    )
    if not certificate.validates():
        raise AssertionError("the normalized strong-coupling tail drifted")
    return certificate


@dataclass(frozen=True)
class StrongCouplingNormalizedCutoffPoint:
    """Least cutoff meeting a normalized total-variation tolerance."""

    coupling: Fraction
    tolerance: Fraction
    cutoff: int
    normalized_tail_bound: Fraction
    previous_cutoff_fails: bool

    def validates(self) -> bool:
        if not 0 < self.coupling < 1 or self.tolerance <= 0 or self.cutoff < 0:
            return False
        current = strong_coupling_normalized_tail(self.coupling, self.cutoff)
        if current.normalized_total_variation_tail > self.tolerance:
            return False
        if self.cutoff == 0:
            previous_fails = True
        else:
            try:
                previous = strong_coupling_normalized_tail(
                    self.coupling,
                    self.cutoff - 1,
                )
            except ValueError:
                previous_fails = True
            else:
                previous_fails = (
                    previous.normalized_total_variation_tail > self.tolerance
                )
        return (
            self.normalized_tail_bound
            == current.normalized_total_variation_tail
            and self.previous_cutoff_fails == previous_fails
            and previous_fails
        )


def strong_coupling_normalized_cutoff(
    coupling: Fraction,
    tolerance: Fraction,
) -> StrongCouplingNormalizedCutoffPoint:
    """Return the least normalized cutoff in the elementary positivity corridor."""

    if not 0 < coupling < 1:
        raise ValueError("the heat coordinate must lie strictly between zero and one")
    if tolerance <= 0:
        raise ValueError("the requested tolerance must be positive")
    cutoff = 0
    while True:
        try:
            certificate = strong_coupling_normalized_tail(coupling, cutoff)
        except ValueError:
            cutoff += 1
            continue
        if certificate.normalized_total_variation_tail <= tolerance:
            point = StrongCouplingNormalizedCutoffPoint(
                coupling=coupling,
                tolerance=tolerance,
                cutoff=cutoff,
                normalized_tail_bound=(
                    certificate.normalized_total_variation_tail
                ),
                previous_cutoff_fails=True,
            )
            if not point.validates():
                raise AssertionError("the normalized cutoff schedule drifted")
            return point
        cutoff += 1


def _jacobi_product_prefix(coupling: Fraction, terms: int) -> Fraction:
    """Finite lower-product prefix from the differentiated Jacobi identity."""

    if not 0 < coupling < 1:
        raise ValueError("the heat coordinate must lie strictly between zero and one")
    if terms < 1:
        raise ValueError("the Jacobi floor requires at least one product term")
    return prod(
        (
            (1 - coupling ** (2 * index))
            * (1 - coupling ** (2 * index - 1)) ** 2
            for index in range(1, terms + 1)
        ),
        start=Fraction(1),
    )


def _jacobi_product_tail_charge(
    coupling: Fraction,
    terms: int,
) -> Fraction:
    """Union-bound charge of every Jacobi factor omitted after ``terms``."""

    if not 0 < coupling < 1:
        raise ValueError("the heat coordinate must lie strictly between zero and one")
    if terms < 1:
        raise ValueError("the Jacobi floor requires at least one product term")
    return (
        coupling ** (2 * terms + 2)
        + 2 * coupling ** (2 * terms + 1)
    ) / (1 - coupling**2)


@dataclass(frozen=True)
class JacobiHeatKernelFloor:
    """Exact rational pointwise floor for one full SU(2) heat kernel.

    The analytic input is the differentiated Jacobi triple-product identity

        K_s(x) = theta_3(x) S_s(x) / (2s).

    The inequalities after that identity are elementary rational estimates:
    every theta factor is bounded by its square completion, the first
    positive ``S`` term is retained, and the omitted infinite product is
    bounded below by one minus the sum of its missing charges.
    """

    coupling: Fraction
    product_terms: int
    finite_product: Fraction
    tail_charge: Fraction
    infinite_product_lower_bound: Fraction
    heat_kernel_floor: Fraction
    uniform_on_conjugacy_interval: bool
    analytic_identity: str
    identity_formalized_in_repo: bool

    def validates(self) -> bool:
        if (
            not 0 < self.coupling < 1
            or self.product_terms < 1
            or not 0 <= self.tail_charge < 1
        ):
            return False
        prefix = _jacobi_product_prefix(
            self.coupling,
            self.product_terms,
        )
        tail = _jacobi_product_tail_charge(
            self.coupling,
            self.product_terms,
        )
        product_floor = prefix * (1 - tail)
        return (
            self.finite_product == prefix
            and self.tail_charge == tail
            and self.infinite_product_lower_bound == product_floor > 0
            and self.heat_kernel_floor
            == product_floor / (1 + self.coupling) ** 2
            > 0
            and self.uniform_on_conjugacy_interval
            and self.analytic_identity
            == "differentiated-Jacobi-triple-product-for-SU2-heat-kernel"
            and not self.identity_formalized_in_repo
        )


def jacobi_heat_kernel_floor(coupling: Fraction) -> JacobiHeatKernelFloor:
    """Construct a positive rational heat-kernel floor for every ``0<s<1``."""

    if not 0 < coupling < 1:
        raise ValueError("the heat coordinate must lie strictly between zero and one")
    terms = 1
    while _jacobi_product_tail_charge(coupling, terms) >= 1:
        terms += 1
    prefix = _jacobi_product_prefix(coupling, terms)
    tail = _jacobi_product_tail_charge(coupling, terms)
    product_floor = prefix * (1 - tail)
    certificate = JacobiHeatKernelFloor(
        coupling=coupling,
        product_terms=terms,
        finite_product=prefix,
        tail_charge=tail,
        infinite_product_lower_bound=product_floor,
        heat_kernel_floor=product_floor / (1 + coupling) ** 2,
        uniform_on_conjugacy_interval=True,
        analytic_identity=(
            "differentiated-Jacobi-triple-product-for-SU2-heat-kernel"
        ),
        identity_formalized_in_repo=False,
    )
    if not certificate.validates():
        raise AssertionError("the Jacobi heat-kernel floor drifted")
    return certificate


@dataclass(frozen=True)
class AllCouplingConditionalNormalizedTail:
    """Boundary-uniform normalized truncation tail for every rational coupling."""

    coupling: Fraction
    cutoff: int
    fine_face_count: int
    plaquette_floor: JacobiHeatKernelFloor
    plaquette_tail: SinglePlaquetteAllLabelTail
    truncated_plaquette_floor: Fraction
    full_partition_floor: Fraction
    unnormalized_density_l1_tail: Fraction
    normalized_total_variation_tail: Fraction
    boundary_holonomy_uniform: bool
    ambient_volume_independent: bool
    actual_rg_remainder: bool

    def validates(self) -> bool:
        if (
            not self.plaquette_floor.validates()
            or not self.plaquette_tail.validates()
            or self.coupling != self.plaquette_floor.coupling
            or self.coupling != self.plaquette_tail.coupling
            or self.cutoff != self.plaquette_tail.cutoff
        ):
            return False
        floor = self.plaquette_floor.heat_kernel_floor
        tail = self.plaquette_tail.tail_bound
        density_tail = (
            self.fine_face_count
            * self.plaquette_tail.total_upper_bound
            ** (self.fine_face_count - 1)
            * tail
        )
        return (
            self.fine_face_count == WHOLE_SLAB_FACE_COUNT
            and self.truncated_plaquette_floor == floor - tail > 0
            and self.full_partition_floor == floor**self.fine_face_count
            and self.unnormalized_density_l1_tail == density_tail
            and self.normalized_total_variation_tail
            == 2 * density_tail / self.full_partition_floor
            and self.boundary_holonomy_uniform
            and self.ambient_volume_independent
            and not self.actual_rg_remainder
        )


def all_coupling_conditional_normalized_tail(
    coupling: Fraction,
    cutoff: int,
) -> AllCouplingConditionalNormalizedTail:
    """Lift the Jacobi floor and character tail to a normalized local law."""

    floor = jacobi_heat_kernel_floor(coupling)
    tail = single_plaquette_all_label_tail(coupling, cutoff)
    if tail.tail_bound >= floor.heat_kernel_floor:
        raise ValueError(
            "the cutoff does not yet make the truncated plaquette kernel positive"
        )
    density_tail = (
        WHOLE_SLAB_FACE_COUNT
        * tail.total_upper_bound ** (WHOLE_SLAB_FACE_COUNT - 1)
        * tail.tail_bound
    )
    certificate = AllCouplingConditionalNormalizedTail(
        coupling=coupling,
        cutoff=cutoff,
        fine_face_count=WHOLE_SLAB_FACE_COUNT,
        plaquette_floor=floor,
        plaquette_tail=tail,
        truncated_plaquette_floor=(
            floor.heat_kernel_floor - tail.tail_bound
        ),
        full_partition_floor=(
            floor.heat_kernel_floor**WHOLE_SLAB_FACE_COUNT
        ),
        unnormalized_density_l1_tail=density_tail,
        normalized_total_variation_tail=(
            2
            * density_tail
            / floor.heat_kernel_floor**WHOLE_SLAB_FACE_COUNT
        ),
        boundary_holonomy_uniform=True,
        ambient_volume_independent=True,
        actual_rg_remainder=False,
    )
    if not certificate.validates():
        raise AssertionError("the all-coupling normalized tail drifted")
    return certificate


@dataclass(frozen=True)
class AllCouplingNormalizedCutoffPoint:
    """Least cutoff certified by the Jacobi floor at one tolerance."""

    coupling: Fraction
    tolerance: Fraction
    cutoff: int
    normalized_tail_bound: Fraction
    truncated_plaquette_floor: Fraction

    def validates(self) -> bool:
        if not 0 < self.coupling < 1 or self.tolerance <= 0 or self.cutoff < 0:
            return False
        current = all_coupling_conditional_normalized_tail(
            self.coupling,
            self.cutoff,
        )
        if current.normalized_total_variation_tail > self.tolerance:
            return False
        previous_fails = self.cutoff == 0
        if self.cutoff > 0:
            try:
                previous = all_coupling_conditional_normalized_tail(
                    self.coupling,
                    self.cutoff - 1,
                )
            except ValueError:
                previous_fails = True
            else:
                previous_fails = (
                    previous.normalized_total_variation_tail > self.tolerance
                )
        return (
            previous_fails
            and self.normalized_tail_bound
            == current.normalized_total_variation_tail
            and self.truncated_plaquette_floor
            == current.truncated_plaquette_floor
            > 0
        )


def all_coupling_normalized_cutoff(
    coupling: Fraction,
    tolerance: Fraction,
) -> AllCouplingNormalizedCutoffPoint:
    """Return the least Jacobi-floor cutoff for a normalized local tolerance."""

    if not 0 < coupling < 1:
        raise ValueError("the heat coordinate must lie strictly between zero and one")
    if tolerance <= 0:
        raise ValueError("the requested tolerance must be positive")
    cutoff = 0
    while True:
        try:
            certificate = all_coupling_conditional_normalized_tail(
                coupling,
                cutoff,
            )
        except ValueError:
            cutoff += 1
            continue
        if certificate.normalized_total_variation_tail <= tolerance:
            point = AllCouplingNormalizedCutoffPoint(
                coupling=coupling,
                tolerance=tolerance,
                cutoff=cutoff,
                normalized_tail_bound=(
                    certificate.normalized_total_variation_tail
                ),
                truncated_plaquette_floor=(
                    certificate.truncated_plaquette_floor
                ),
            )
            if not point.validates():
                raise AssertionError("the all-coupling cutoff schedule drifted")
            return point
        cutoff += 1


@dataclass(frozen=True)
class BF2TraceKernelTail:
    """Trace-norm lift of a local Gibbs tail to the BF2 boundary Gram.

    Each boundary holonomy uses the heat-weighted Peter--Weyl feature vector

        sqrt((n+1) s^(n(n+2))) D^n_mk(g).

    Unitarity of ``D^n`` makes its squared evaluation norm

        sum_n (n+1)^2 s^(n(n+2)).

    Tensoring over the nine coarse holonomies raises this bound to the ninth
    power.  Integrating ``|v><v|`` against a signed measure of ``L1`` mass
    ``epsilon`` then has trace norm at most ``H(s)^9 epsilon``.  Orthogonal
    compressions and unitary recouplings do not increase that norm.
    """

    coupling: Fraction
    cutoff: int
    boundary_feature_slots: int
    normalized_density_tail: AllCouplingConditionalNormalizedTail
    evaluation_norm_squared_upper: Fraction
    trace_norm_tail_bound: Fraction
    retained_block_bound: Fraction
    retained_to_outside_block_bound: Fraction
    outside_to_retained_block_bound: Fraction
    outside_block_bound: Fraction
    complete_magnetic_features: bool
    complete_intertwiner_projection: bool
    unitary_recoupling_invariant: bool
    ambient_volume_independent: bool
    actual_fine_coarse_rg_remainder: bool

    def validates(self) -> bool:
        if (
            not self.normalized_density_tail.validates()
            or self.coupling != self.normalized_density_tail.coupling
            or self.cutoff != self.normalized_density_tail.cutoff
            or self.boundary_feature_slots != len(coarse_face_paths())
        ):
            return False
        heat_upper = (
            self.normalized_density_tail.plaquette_tail.total_upper_bound
        )
        evaluation = heat_upper**self.boundary_feature_slots
        trace_bound = (
            evaluation
            * self.normalized_density_tail.normalized_total_variation_tail
        )
        return (
            self.evaluation_norm_squared_upper == evaluation
            and self.trace_norm_tail_bound == trace_bound
            and self.retained_block_bound == trace_bound
            and self.retained_to_outside_block_bound == trace_bound
            and self.outside_to_retained_block_bound == trace_bound
            and self.outside_block_bound == trace_bound
            and self.complete_magnetic_features
            and self.complete_intertwiner_projection
            and self.unitary_recoupling_invariant
            and self.ambient_volume_independent
            and not self.actual_fine_coarse_rg_remainder
        )


def bf2_trace_kernel_tail(
    coupling: Fraction,
    cutoff: int,
) -> BF2TraceKernelTail:
    """Lift an all-coupling conditional tail to all coherent BF2 blocks."""

    normalized = all_coupling_conditional_normalized_tail(
        coupling,
        cutoff,
    )
    slots = len(coarse_face_paths())
    evaluation = normalized.plaquette_tail.total_upper_bound**slots
    trace_bound = evaluation * normalized.normalized_total_variation_tail
    certificate = BF2TraceKernelTail(
        coupling=coupling,
        cutoff=cutoff,
        boundary_feature_slots=slots,
        normalized_density_tail=normalized,
        evaluation_norm_squared_upper=evaluation,
        trace_norm_tail_bound=trace_bound,
        retained_block_bound=trace_bound,
        retained_to_outside_block_bound=trace_bound,
        outside_to_retained_block_bound=trace_bound,
        outside_block_bound=trace_bound,
        complete_magnetic_features=True,
        complete_intertwiner_projection=True,
        unitary_recoupling_invariant=True,
        ambient_volume_independent=True,
        actual_fine_coarse_rg_remainder=False,
    )
    if not certificate.validates():
        raise AssertionError("the BF2 trace-kernel tail drifted")
    return certificate


@dataclass(frozen=True)
class BF32AllLabelFrontier:
    """Fail-closed adjudication of the all-label progress toward BF3.2."""

    fixed_block_all_label_kernel: bool
    computable_haar_cauchy_name: bool
    literal_haar_tail: bool
    external_label_uniform_weighted_norm: bool
    coupling_dependent_cutoff_constructed: bool
    normalized_strong_coupling_tail: bool
    conditional_tail_boundary_uniform: bool
    conditional_tail_ambient_volume_uniform: bool
    all_coupling_positive_floor_schedule: bool
    jacobi_floor_identity_formalized: bool
    complete_boundary_trace_cauchy_name: bool
    bf2_psd_norm_identified: bool
    actual_rg_remainder_bounded: bool
    bf32_closed: bool
    first_open_obligation: str
    next_gate: str

    def validates(self) -> bool:
        return (
            self.fixed_block_all_label_kernel
            and self.computable_haar_cauchy_name
            and self.literal_haar_tail
            and self.external_label_uniform_weighted_norm
            and self.coupling_dependent_cutoff_constructed
            and self.normalized_strong_coupling_tail
            and self.conditional_tail_boundary_uniform
            and self.conditional_tail_ambient_volume_uniform
            and self.all_coupling_positive_floor_schedule
            and not self.jacobi_floor_identity_formalized
            and self.complete_boundary_trace_cauchy_name
            and self.bf2_psd_norm_identified
            and not self.actual_rg_remainder_bounded
            and not self.bf32_closed
            and self.first_open_obligation
            == "construct-and-bound-actual-fine-coarse-RG-remainder"
            and self.next_gate == "BF3.2-remains-before-BF4"
        )


@cache
def bf32_all_label_frontier() -> BF32AllLabelFrontier:
    """Return the honest fixed-block completion and remaining BF3.2 frontier."""

    # These calls pin actual exact witnesses rather than Boolean-only claims.
    fixed = whole_slab_all_label_cauchy_certificate(
        Fraction(1, 2),
        5,
        (1, 2, 3),
    )
    coefficient = computable_all_label_haar_coefficient(
        Fraction(1, 2),
        (0,) * len(coarse_face_paths()),
    )
    schedule = coupling_dependent_cutoff(Fraction(3, 4), Fraction(1, 100))
    normalized = strong_coupling_normalized_cutoff(
        Fraction(1, 2),
        Fraction(1, 100),
    )
    normalized_tail = strong_coupling_normalized_tail(
        normalized.coupling,
        normalized.cutoff,
    )
    jacobi_schedule = all_coupling_normalized_cutoff(
        Fraction(3, 4),
        Fraction(1, 10),
    )
    trace_tail = bf2_trace_kernel_tail(
        jacobi_schedule.coupling,
        jacobi_schedule.cutoff,
    )
    frontier = BF32AllLabelFrontier(
        fixed_block_all_label_kernel=fixed.validates(),
        computable_haar_cauchy_name=(
            coefficient.validates()
            and coefficient.approximation(0) == Fraction(1)
        ),
        literal_haar_tail=fixed.literal_haar_character_bound,
        external_label_uniform_weighted_norm=(
            fixed.raw_coefficient_tail_bound
            == fixed.external_dimension * fixed.dimension_weighted_tail_bound
        ),
        coupling_dependent_cutoff_constructed=schedule.validates(),
        normalized_strong_coupling_tail=(
            normalized.validates() and normalized_tail.validates()
        ),
        conditional_tail_boundary_uniform=(
            normalized_tail.boundary_holonomy_uniform
        ),
        conditional_tail_ambient_volume_uniform=(
            normalized_tail.ambient_volume_independent
        ),
        all_coupling_positive_floor_schedule=jacobi_schedule.validates(),
        jacobi_floor_identity_formalized=False,
        complete_boundary_trace_cauchy_name=trace_tail.validates(),
        bf2_psd_norm_identified=(
            trace_tail.unitary_recoupling_invariant
            and trace_tail.complete_intertwiner_projection
        ),
        actual_rg_remainder_bounded=False,
        bf32_closed=False,
        first_open_obligation=(
            "construct-and-bound-actual-fine-coarse-RG-remainder"
        ),
        next_gate="BF3.2-remains-before-BF4",
    )
    if not frontier.validates():
        raise AssertionError("the BF3.2 all-label frontier drifted")
    return frontier
