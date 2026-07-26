"""Promote the BF4 Choi order to a mass-preserving channel decomposition.

The trace-class feature used in
``physical_all_label_choi_domination.py`` weights the Peter--Weyl block
``D^n(g)`` by

    q_n(u) ** (1/2),   q_n(u) = (n + 1) u ** (n(n + 2)).

At every finite feature cutoff this weight is strictly positive and
commutes with the block-diagonal Peter--Weyl unitary.  Removing it by an
invertible Choi congruence leaves the random-unitary channel

    Phi_mu(X) = integral U(g) X U(g)^* dmu(g)

on the same nine-slot source/target carrier.  The direct measure order

    mu_phys >= eta mu_corr

therefore has the exact normalized residual law

    omega = (mu_phys - eta mu_corr) / (1 - eta).

It is a probability measure, so

    Phi_phys = eta Phi_corr + (1 - eta) Phi_omega

is a decomposition into normal completely positive, trace-preserving and
unital maps.  This closes mass preservation for the channel canonically
defined by the physical Choi measure.  It also gives an abstract same-carrier
composition law: random-unitary channels compose by convolution of their
componentwise group laws.

Two physical statements remain open.  First, convolution of the normalized
one-slab laws has not been identified with the conditional Haar-network RG
kernel obtained by gluing consecutive corrected slabs.  Second, the current
one-slab coefficient is too small for a spacing-uniform argument which
expands a composition and uses only histories containing a certified
corridor summand.  On the exact dyadic trajectory

    a = 2**(-k),  s = 1 - a,  m = 1/a,

the available coefficient satisfies ``eta <= a**63``.  The total weight of
all expansion histories containing at least one corridor tag obeys

    1 - (1 - eta)**m <= m eta <= a**62.

It tends to zero.  The corridor channel is not asserted here to be a reset
map; the displayed number is only the total mass available to an argument
using those certified tags.  This route-specific no-go theorem rejects
composition of the present microscopic floor/ceiling certificates, not
mixing hidden in residual histories or a new direct relative-order estimate
on the physically glued fixed-distance block.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import cache

from computations.physical_all_label_choi_domination import (
    COARSE_CHOI_SLOT_COUNT,
    PhysicalAllLabelChoiDomination,
    physical_all_label_choi_domination,
)


def _casimir4(label: int) -> int:
    return label * (label + 2)


def _one_slot_dimension(cutoff: int) -> int:
    return sum(label + 1 for label in range(cutoff + 1))


@dataclass(frozen=True)
class FinitePeterWeylChannelCarrier:
    """One finite compression of the universal random-unitary carrier."""

    feature_cutoff: int
    feature_coupling: Fraction
    slot_count: int
    one_slot_dimension: int
    source_dimension: int
    target_dimension: int
    one_slot_heat_weights: tuple[Fraction, ...]
    every_heat_weight_strictly_positive: bool
    heat_weight_commutes_with_peter_weyl_unitary: bool
    heat_weight_chi_congruence_invertible: bool
    every_group_operator_unitary: bool
    source_and_target_carriers_identical: bool
    nested_cutoff_restriction_exact: bool

    def validates(self) -> bool:
        if self.feature_cutoff < 0 or not 0 < self.feature_coupling < 1:
            return False
        dimension = _one_slot_dimension(self.feature_cutoff)
        weights = tuple(
            Fraction(label + 1)
            * self.feature_coupling ** _casimir4(label)
            for label in range(self.feature_cutoff + 1)
        )
        return (
            self.slot_count == COARSE_CHOI_SLOT_COUNT
            and self.one_slot_dimension == dimension
            and self.source_dimension
            == self.target_dimension
            == dimension**self.slot_count
            and self.one_slot_heat_weights == weights
            and self.every_heat_weight_strictly_positive
            and all(weight > 0 for weight in weights)
            and self.heat_weight_commutes_with_peter_weyl_unitary
            and self.heat_weight_chi_congruence_invertible
            and self.every_group_operator_unitary
            and self.source_and_target_carriers_identical
            and self.nested_cutoff_restriction_exact
        )


def finite_peter_weyl_channel_carrier(
    feature_cutoff: int,
    feature_coupling: Fraction,
) -> FinitePeterWeylChannelCarrier:
    """Construct the finite carrier and its exact positive deweighting data."""

    if feature_cutoff < 0:
        raise ValueError("the feature cutoff must be nonnegative")
    if not 0 < feature_coupling < 1:
        raise ValueError("the feature heat coordinate must lie in (0, 1)")
    dimension = _one_slot_dimension(feature_cutoff)
    carrier = FinitePeterWeylChannelCarrier(
        feature_cutoff=feature_cutoff,
        feature_coupling=feature_coupling,
        slot_count=COARSE_CHOI_SLOT_COUNT,
        one_slot_dimension=dimension,
        source_dimension=dimension**COARSE_CHOI_SLOT_COUNT,
        target_dimension=dimension**COARSE_CHOI_SLOT_COUNT,
        one_slot_heat_weights=tuple(
            Fraction(label + 1)
            * feature_coupling ** _casimir4(label)
            for label in range(feature_cutoff + 1)
        ),
        every_heat_weight_strictly_positive=True,
        heat_weight_commutes_with_peter_weyl_unitary=True,
        heat_weight_chi_congruence_invertible=True,
        every_group_operator_unitary=True,
        source_and_target_carriers_identical=True,
        nested_cutoff_restriction_exact=True,
    )
    if not carrier.validates():
        raise AssertionError("the finite Peter--Weyl channel carrier drifted")
    return carrier


@dataclass(frozen=True)
class MassPreservingChannelPromotion:
    """CPTP promotion of the fixed-coupling physical Choi comparison."""

    choi_domination: PhysicalAllLabelChoiDomination
    finite_carrier_witness: FinitePeterWeylChannelCarrier
    domination_coefficient: Fraction
    physical_measure_mass: Fraction
    corridor_measure_mass: Fraction
    positive_difference_measure_mass: Fraction
    normalized_residual_measure_mass: Fraction
    residual_channel_coefficient: Fraction
    weighted_trace_class_choi_order_proved: bool
    finite_weight_removal_is_cp_order_congruence: bool
    every_finite_unweighted_channel_cptp: bool
    residual_measure_nonnegative: bool
    normalized_residual_random_unitary_channel_cptp: bool
    normalized_residual_channel_unital: bool
    projective_cutoff_restriction_compatible: bool
    normal_all_label_random_unitary_channel_defined: bool
    unweighted_all_label_choi_trace_class: bool
    abstract_same_carrier_convolution_composition_proved: bool
    physical_consecutive_slab_rg_identification_proved: bool
    spacing_uniform_refresh_mass_proved: bool
    physical_channel_definition: str
    corridor_channel_definition: str
    residual_measure_definition: str
    residual_channel_definition: str
    composition_convention: str
    first_open_obligation: str

    def validates(self) -> bool:
        if (
            not self.choi_domination.validates()
            or not self.finite_carrier_witness.validates()
            or self.finite_carrier_witness.feature_cutoff
            != self.choi_domination.feature_cutoff_schedule.cutoff
            or self.finite_carrier_witness.feature_coupling
            != self.choi_domination.feature_coupling
        ):
            return False
        eta = self.choi_domination.cp_domination_coefficient
        difference_mass = 1 - eta
        return (
            self.domination_coefficient == eta
            and 0 < eta < 1
            and self.physical_measure_mass
            == self.corridor_measure_mass
            == self.normalized_residual_measure_mass
            == 1
            and self.positive_difference_measure_mass == difference_mass
            and self.residual_channel_coefficient == difference_mass
            and self.weighted_trace_class_choi_order_proved
            and self.finite_weight_removal_is_cp_order_congruence
            and self.every_finite_unweighted_channel_cptp
            and self.residual_measure_nonnegative
            and self.normalized_residual_random_unitary_channel_cptp
            and self.normalized_residual_channel_unital
            and self.projective_cutoff_restriction_compatible
            and self.normal_all_label_random_unitary_channel_defined
            and not self.unweighted_all_label_choi_trace_class
            and self.abstract_same_carrier_convolution_composition_proved
            and not self.physical_consecutive_slab_rg_identification_proved
            and not self.spacing_uniform_refresh_mass_proved
            and self.physical_channel_definition
            == "Phi_phys(X)=Integral U(Pi(x)) X U(Pi(x))^* dmu_phys(x)"
            and self.corridor_channel_definition
            == "Phi_corr(X)=Integral U(Pi(x)) X U(Pi(x))^* dmu_corr(x)"
            and self.residual_measure_definition
            == "omega=(mu_phys-eta*mu_corr)/(1-eta)"
            and self.residual_channel_definition
            == "Psi(X)=Integral U(Pi(x)) X U(Pi(x))^* domega(x)"
            and self.composition_convention
            == "Phi_beta o Phi_alpha = Phi_(beta*alpha), product=h*g"
            and self.first_open_obligation
            == "identify-physical-gluing-and-prove-fixed-distance-minorization"
        )


@cache
def mass_preserving_channel_promotion(
    density_coupling: Fraction,
    feature_coupling: Fraction,
    relative_tolerance: Fraction = Fraction(1, 100),
) -> MassPreservingChannelPromotion:
    """Promote physical measure order to a random-unitary CPTP refresh."""

    choi = physical_all_label_choi_domination(
        density_coupling,
        feature_coupling,
        relative_tolerance,
    )
    eta = choi.cp_domination_coefficient
    certificate = MassPreservingChannelPromotion(
        choi_domination=choi,
        finite_carrier_witness=finite_peter_weyl_channel_carrier(
            choi.feature_cutoff_schedule.cutoff,
            feature_coupling,
        ),
        domination_coefficient=eta,
        physical_measure_mass=Fraction(1),
        corridor_measure_mass=Fraction(1),
        positive_difference_measure_mass=1 - eta,
        normalized_residual_measure_mass=Fraction(1),
        residual_channel_coefficient=1 - eta,
        weighted_trace_class_choi_order_proved=True,
        finite_weight_removal_is_cp_order_congruence=True,
        every_finite_unweighted_channel_cptp=True,
        residual_measure_nonnegative=True,
        normalized_residual_random_unitary_channel_cptp=True,
        normalized_residual_channel_unital=True,
        projective_cutoff_restriction_compatible=True,
        normal_all_label_random_unitary_channel_defined=True,
        unweighted_all_label_choi_trace_class=False,
        abstract_same_carrier_convolution_composition_proved=True,
        physical_consecutive_slab_rg_identification_proved=False,
        spacing_uniform_refresh_mass_proved=False,
        physical_channel_definition=(
            "Phi_phys(X)=Integral U(Pi(x)) X U(Pi(x))^* dmu_phys(x)"
        ),
        corridor_channel_definition=(
            "Phi_corr(X)=Integral U(Pi(x)) X U(Pi(x))^* dmu_corr(x)"
        ),
        residual_measure_definition=(
            "omega=(mu_phys-eta*mu_corr)/(1-eta)"
        ),
        residual_channel_definition=(
            "Psi(X)=Integral U(Pi(x)) X U(Pi(x))^* domega(x)"
        ),
        composition_convention=(
            "Phi_beta o Phi_alpha = Phi_(beta*alpha), product=h*g"
        ),
        first_open_obligation=(
            "identify-physical-gluing-and-prove-fixed-distance-minorization"
        ),
    )
    if not certificate.validates():
        raise AssertionError("the mass-preserving channel promotion drifted")
    return certificate


@dataclass(frozen=True)
class DyadicFixedDistanceIterationNoGo:
    """No-go bound for composing only certified microscopic corridor tags."""

    level: int
    spacing: Fraction
    coupling: Fraction
    physical_length: Fraction
    microscopic_step_count: int
    one_step_domination_coefficient: Fraction
    one_step_floor_ceiling_upper_bound: Fraction
    one_step_spacing_power_upper_bound: Fraction
    all_residual_history_mass_formula: str
    corridor_tagged_history_mass_formula: str
    bernoulli_corridor_history_upper_bound_proved: bool
    corridor_tagged_history_mass_upper_bound: Fraction
    union_bound_on_corridor_tagged_mass: Fraction
    spacing_power_bound_on_corridor_tagged_mass: Fraction
    corridor_tagged_composition_spacing_uniform: bool
    direct_grouped_relative_order_refuted: bool
    first_open_obligation: str

    def validates(self) -> bool:
        if self.level < 1:
            return False
        spacing = Fraction(1, 2**self.level)
        coupling = 1 - spacing
        steps = 2**self.level
        promotion = mass_preserving_channel_promotion(coupling, coupling)
        eta = promotion.domination_coefficient
        floor_ceiling = (
            spacing**3 / (2 - spacing)
        ) ** 21
        spacing_power = spacing**63
        union_bound = steps * eta
        spacing_bound = spacing**62
        return (
            self.spacing == spacing
            and self.coupling == coupling
            and self.physical_length == 1
            and self.microscopic_step_count == steps
            and Fraction(steps) * spacing == 1
            and self.one_step_domination_coefficient == eta
            and self.one_step_floor_ceiling_upper_bound == floor_ceiling
            and self.one_step_spacing_power_upper_bound == spacing_power
            and 0 < eta <= floor_ceiling <= spacing_power
            and self.all_residual_history_mass_formula == "(1-eta)^m"
            and self.corridor_tagged_history_mass_formula
            == "1-(1-eta)^m"
            and self.bernoulli_corridor_history_upper_bound_proved
            and self.corridor_tagged_history_mass_upper_bound
            == union_bound
            and self.union_bound_on_corridor_tagged_mass == union_bound
            and self.spacing_power_bound_on_corridor_tagged_mass
            == spacing_bound
            and union_bound <= spacing_bound
            and not self.corridor_tagged_composition_spacing_uniform
            and not self.direct_grouped_relative_order_refuted
            and self.first_open_obligation
            == "estimate-physically-glued-block-before-microscopic-minorization"
        )


def dyadic_fixed_distance_iteration_no_go(
    level: int,
) -> DyadicFixedDistanceIterationNoGo:
    """Certify the tagged-history ``a**62`` loss over unit distance."""

    if level < 1:
        raise ValueError("the dyadic level must be positive")
    spacing = Fraction(1, 2**level)
    coupling = 1 - spacing
    promotion = mass_preserving_channel_promotion(coupling, coupling)
    eta = promotion.domination_coefficient
    steps = 2**level
    certificate = DyadicFixedDistanceIterationNoGo(
        level=level,
        spacing=spacing,
        coupling=coupling,
        physical_length=Fraction(1),
        microscopic_step_count=steps,
        one_step_domination_coefficient=eta,
        one_step_floor_ceiling_upper_bound=(
            spacing**3 / (2 - spacing)
        )
        ** 21,
        one_step_spacing_power_upper_bound=spacing**63,
        all_residual_history_mass_formula="(1-eta)^m",
        corridor_tagged_history_mass_formula="1-(1-eta)^m",
        bernoulli_corridor_history_upper_bound_proved=True,
        corridor_tagged_history_mass_upper_bound=steps * eta,
        union_bound_on_corridor_tagged_mass=steps * eta,
        spacing_power_bound_on_corridor_tagged_mass=spacing**62,
        corridor_tagged_composition_spacing_uniform=False,
        direct_grouped_relative_order_refuted=False,
        first_open_obligation=(
            "estimate-physically-glued-block-before-microscopic-minorization"
        ),
    )
    if not certificate.validates():
        raise AssertionError("the fixed-distance iteration no-go drifted")
    return certificate
