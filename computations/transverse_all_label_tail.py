"""Uniform all-label tail for the BF4 21-face transverse residual.

The grouped-corridor audit leaves a residual with a connected 15-face core
and six one-face decorations.  The core contains five unprotected normalized
Haar variables; all remaining links are corridor-protected boundary data.

For the SU(2) heat coordinate ``0 < s < 1``, one character term is uniformly
bounded by

    h_n(s) = (n + 1)^2 s^(n(n+2)).

The one-plaquette tail from ``all_label_whole_slab_tail`` therefore controls
the product of all 21 residual heat kernels by a telescoping estimate.
Normalized Haar integration has operator norm one in the uniform norm, so it
cannot enlarge the connected-core error.  This yields a constructive,
boundary-uniform all-label Cauchy modulus for the exact residual function.

This certificate does not expose the individual all-label recoupling
coefficients and does not prove complete-positive corridor domination.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import cache

from computations.all_label_whole_slab_tail import (
    SinglePlaquetteAllLabelTail,
    single_plaquette_all_label_tail,
)

CONNECTED_CORE_FACE_COUNT = 15
DECORATION_FACE_COUNT = 6
TRANSVERSE_RESIDUAL_FACE_COUNT = (
    CONNECTED_CORE_FACE_COUNT + DECORATION_FACE_COUNT
)
INTERNAL_NORMALIZED_HAAR_LINK_COUNT = 5
PROTECTED_BOUNDARY_LINK_COUNT = 18


@dataclass(frozen=True)
class TransverseAllLabelUniformTail:
    """Exact telescoping bound for one common representation cutoff."""

    coupling: Fraction
    cutoff: int
    plaquette_tail: SinglePlaquetteAllLabelTail
    connected_core_face_count: int
    decoration_face_count: int
    residual_face_count: int
    internal_normalized_haar_link_count: int
    protected_boundary_link_count: int
    one_face_sup_upper: Fraction
    connected_core_product_sup_upper: Fraction
    decoration_product_sup_upper: Fraction
    residual_product_sup_upper: Fraction
    connected_core_uniform_tail_bound: Fraction
    decoration_uniform_tail_bound: Fraction
    residual_uniform_tail_bound: Fraction
    composed_residual_uniform_tail_bound: Fraction
    normalized_haar_is_uniformly_nonexpansive: bool
    boundary_uniform: bool
    ambient_volume_independent: bool
    spacing_uniform_in_weak_coupling_limit: bool
    coherent_all_label_residual_function_constructed: bool
    recoupling_amplitudes_controlled_by_this_tail: bool
    cp_order_domination_proved: bool
    first_open_obligation: str

    def validates(self) -> bool:
        if (
            not self.plaquette_tail.validates()
            or self.coupling != self.plaquette_tail.coupling
            or self.cutoff != self.plaquette_tail.cutoff
        ):
            return False
        upper = self.plaquette_tail.total_upper_bound
        tail = self.plaquette_tail.tail_bound
        core_tail = (
            CONNECTED_CORE_FACE_COUNT
            * upper ** (CONNECTED_CORE_FACE_COUNT - 1)
            * tail
        )
        decoration_tail = (
            DECORATION_FACE_COUNT
            * upper ** (DECORATION_FACE_COUNT - 1)
            * tail
        )
        residual_tail = (
            TRANSVERSE_RESIDUAL_FACE_COUNT
            * upper ** (TRANSVERSE_RESIDUAL_FACE_COUNT - 1)
            * tail
        )
        composed_tail = (
            core_tail * upper**DECORATION_FACE_COUNT
            + upper**CONNECTED_CORE_FACE_COUNT * decoration_tail
        )
        return (
            self.connected_core_face_count == CONNECTED_CORE_FACE_COUNT
            and self.decoration_face_count == DECORATION_FACE_COUNT
            and self.residual_face_count == TRANSVERSE_RESIDUAL_FACE_COUNT
            and self.internal_normalized_haar_link_count
            == INTERNAL_NORMALIZED_HAAR_LINK_COUNT
            and self.protected_boundary_link_count
            == PROTECTED_BOUNDARY_LINK_COUNT
            and self.one_face_sup_upper == upper
            and self.connected_core_product_sup_upper
            == upper**CONNECTED_CORE_FACE_COUNT
            and self.decoration_product_sup_upper
            == upper**DECORATION_FACE_COUNT
            and self.residual_product_sup_upper
            == upper**TRANSVERSE_RESIDUAL_FACE_COUNT
            and self.connected_core_uniform_tail_bound == core_tail
            and self.decoration_uniform_tail_bound == decoration_tail
            and self.residual_uniform_tail_bound == residual_tail
            and self.composed_residual_uniform_tail_bound
            == composed_tail
            == residual_tail
            and self.normalized_haar_is_uniformly_nonexpansive
            and self.boundary_uniform
            and self.ambient_volume_independent
            and not self.spacing_uniform_in_weak_coupling_limit
            and self.coherent_all_label_residual_function_constructed
            and not self.recoupling_amplitudes_controlled_by_this_tail
            and not self.cp_order_domination_proved
            and self.first_open_obligation
            == "combine-recoupling-carrier-with-tail-and-reconstruct-open-index-choi"
        )


@cache
def transverse_all_label_uniform_tail(
    coupling: Fraction,
    cutoff: int,
) -> TransverseAllLabelUniformTail:
    """Construct the exact uniform residual-tail certificate."""

    plaquette = single_plaquette_all_label_tail(coupling, cutoff)
    upper = plaquette.total_upper_bound
    tail = plaquette.tail_bound
    core_tail = (
        CONNECTED_CORE_FACE_COUNT
        * upper ** (CONNECTED_CORE_FACE_COUNT - 1)
        * tail
    )
    decoration_tail = (
        DECORATION_FACE_COUNT
        * upper ** (DECORATION_FACE_COUNT - 1)
        * tail
    )
    residual_tail = (
        TRANSVERSE_RESIDUAL_FACE_COUNT
        * upper ** (TRANSVERSE_RESIDUAL_FACE_COUNT - 1)
        * tail
    )
    certificate = TransverseAllLabelUniformTail(
        coupling=coupling,
        cutoff=cutoff,
        plaquette_tail=plaquette,
        connected_core_face_count=CONNECTED_CORE_FACE_COUNT,
        decoration_face_count=DECORATION_FACE_COUNT,
        residual_face_count=TRANSVERSE_RESIDUAL_FACE_COUNT,
        internal_normalized_haar_link_count=(
            INTERNAL_NORMALIZED_HAAR_LINK_COUNT
        ),
        protected_boundary_link_count=PROTECTED_BOUNDARY_LINK_COUNT,
        one_face_sup_upper=upper,
        connected_core_product_sup_upper=upper**CONNECTED_CORE_FACE_COUNT,
        decoration_product_sup_upper=upper**DECORATION_FACE_COUNT,
        residual_product_sup_upper=upper**TRANSVERSE_RESIDUAL_FACE_COUNT,
        connected_core_uniform_tail_bound=core_tail,
        decoration_uniform_tail_bound=decoration_tail,
        residual_uniform_tail_bound=residual_tail,
        composed_residual_uniform_tail_bound=(
            core_tail * upper**DECORATION_FACE_COUNT
            + upper**CONNECTED_CORE_FACE_COUNT * decoration_tail
        ),
        normalized_haar_is_uniformly_nonexpansive=True,
        boundary_uniform=True,
        ambient_volume_independent=True,
        spacing_uniform_in_weak_coupling_limit=False,
        coherent_all_label_residual_function_constructed=True,
        recoupling_amplitudes_controlled_by_this_tail=False,
        cp_order_domination_proved=False,
        first_open_obligation=(
            "combine-recoupling-carrier-with-tail-and-reconstruct-open-index-choi"
        ),
    )
    if not certificate.validates():
        raise AssertionError("the transverse all-label tail drifted")
    return certificate


@dataclass(frozen=True)
class TransverseAllLabelCutoffPoint:
    """Least cutoff certified to meet one positive rational tolerance."""

    coupling: Fraction
    tolerance: Fraction
    cutoff: int
    residual_uniform_tail_bound: Fraction
    least_certified_cutoff: bool

    def validates(self) -> bool:
        if (
            not 0 < self.coupling < 1
            or self.tolerance <= 0
            or self.cutoff < 0
            or not self.least_certified_cutoff
        ):
            return False
        current = transverse_all_label_uniform_tail(
            self.coupling,
            self.cutoff,
        )
        if (
            self.residual_uniform_tail_bound
            != current.residual_uniform_tail_bound
            or current.residual_uniform_tail_bound > self.tolerance
        ):
            return False
        if self.cutoff == 0:
            return True
        try:
            previous = transverse_all_label_uniform_tail(
                self.coupling,
                self.cutoff - 1,
            )
        except ValueError:
            return True
        return previous.residual_uniform_tail_bound > self.tolerance


def least_transverse_all_label_cutoff(
    coupling: Fraction,
    tolerance: Fraction,
) -> TransverseAllLabelCutoffPoint:
    """Search the constructive uniform Cauchy modulus."""

    if not 0 < coupling < 1:
        raise ValueError("the heat coordinate must lie strictly between zero and one")
    if tolerance <= 0:
        raise ValueError("the requested tolerance must be positive")
    cutoff = 0
    while True:
        try:
            certificate = transverse_all_label_uniform_tail(
                coupling,
                cutoff,
            )
        except ValueError:
            cutoff += 1
            continue
        if certificate.residual_uniform_tail_bound <= tolerance:
            point = TransverseAllLabelCutoffPoint(
                coupling=coupling,
                tolerance=tolerance,
                cutoff=cutoff,
                residual_uniform_tail_bound=(
                    certificate.residual_uniform_tail_bound
                ),
                least_certified_cutoff=True,
            )
            if not point.validates():
                raise AssertionError("the transverse cutoff point drifted")
            return point
        cutoff += 1
