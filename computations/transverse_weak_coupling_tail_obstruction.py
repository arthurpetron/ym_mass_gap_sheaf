"""Exact obstruction to a spacing-uniform fixed Peter--Weyl cutoff.

For the SU(2) heat kernel in the repository's rational coordinate,

    K_s(e) = sum_{n >= 0} (n + 1)^2 s^(n(n+2)).

All terms are positive at the group identity.  At representation cutoff
``N``, the first omitted label is ``N + 1`` and therefore gives an actual
lower bound on the uniform truncation error, not merely a majorant.

For exponent ``C = (N + 1)(N + 3)``, choose

    s_N = 1 - 1/(2C).

Bernoulli's inequality gives ``s_N^C >= 1/2``.  Hence the first omitted term
is at least ``(N + 2)^2 / 2`` at a legitimate coupling ``0 < s_N < 1``.
No fixed cutoff can therefore provide a small absolute uniform tail over the
weak-coupling interval ``0 < s < 1``.

The obstruction is relative as well.  At
``s = 1 - 1/(2(2N+1)(2N+3))``, the omitted block
``N+1, ..., 2N+1`` is larger than the entire retained head, so the relative
tail share exceeds one half.  This still does not reject a
spacing-dependent cutoff, all-label regrouping, or the positive full
heat-kernel Choi operator.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import cache

from computations.all_label_whole_slab_tail import (
    heat_character_sup_term,
)
from computations.exact_haar_network import casimir4


@dataclass(frozen=True)
class FixedCutoffWeakCouplingObstruction:
    """One explicit weak-coupling witness for a fixed face-label cutoff."""

    cutoff: int
    first_omitted_label: int
    first_omitted_casimir4: int
    witness_coupling: Fraction
    bernoulli_power_floor: Fraction
    actual_identity_tail_term: Fraction
    certified_identity_tail_lower_bound: Fraction
    relative_block_last_label: int
    relative_witness_coupling: Fraction
    retained_identity_head_upper_bound: int
    omitted_identity_block_lower_bound: Fraction
    relative_tail_margin: Fraction
    omitted_block_exceeds_retained_head: bool
    fixed_cutoff_uniform_absolute_tail_possible: bool
    fixed_cutoff_uniform_relative_tail_possible: bool
    spacing_uniform_residual_product_modulus_proved: bool
    spacing_dependent_cutoff_or_all_label_regrouping_required: bool
    first_open_obligation: str

    def validates(self) -> bool:
        if self.cutoff < 0:
            return False
        label = self.cutoff + 1
        exponent = casimir4(label)
        coupling = 1 - Fraction(1, 2 * exponent)
        lower = Fraction((label + 1) ** 2, 2)
        actual = heat_character_sup_term(coupling, label)
        last_label = 2 * self.cutoff + 1
        relative_exponent = casimir4(last_label)
        relative_coupling = 1 - Fraction(1, 2 * relative_exponent)
        retained_upper = sum(
            (retained + 1) ** 2
            for retained in range(self.cutoff + 1)
        )
        omitted_lower = Fraction(
            sum(
                (omitted + 1) ** 2
                for omitted in range(self.cutoff + 1, last_label + 1)
            ),
            2,
        )
        retained_count = self.cutoff + 1
        margin = Fraction(
            retained_count
            * (2 * retained_count + 1)
            * (5 * retained_count - 1),
            12,
        )
        return (
            self.first_omitted_label == label
            and self.first_omitted_casimir4 == exponent
            and self.witness_coupling == coupling
            and 0 < self.witness_coupling < 1
            and self.bernoulli_power_floor == Fraction(1, 2)
            and self.witness_coupling**exponent
            >= self.bernoulli_power_floor
            and self.actual_identity_tail_term == actual >= lower
            and self.certified_identity_tail_lower_bound == lower
            and self.relative_block_last_label == last_label
            and self.relative_witness_coupling == relative_coupling
            and 0 < self.relative_witness_coupling < 1
            and self.relative_witness_coupling**relative_exponent
            >= Fraction(1, 2)
            and self.retained_identity_head_upper_bound == retained_upper
            and self.omitted_identity_block_lower_bound == omitted_lower
            and self.relative_tail_margin
            == omitted_lower - retained_upper
            == margin
            > 0
            and self.omitted_block_exceeds_retained_head
            and omitted_lower > retained_upper
            and not self.fixed_cutoff_uniform_absolute_tail_possible
            and not self.fixed_cutoff_uniform_relative_tail_possible
            and not self.spacing_uniform_residual_product_modulus_proved
            and self.spacing_dependent_cutoff_or_all_label_regrouping_required
            and self.first_open_obligation
            == "build-spacing-dependent-or-all-label-open-index-choi-tail"
        )


@cache
def fixed_cutoff_weak_coupling_obstruction(
    cutoff: int,
) -> FixedCutoffWeakCouplingObstruction:
    """Construct the exact Bernoulli witness at one fixed cutoff."""

    if cutoff < 0:
        raise ValueError("the representation cutoff must be nonnegative")
    label = cutoff + 1
    exponent = casimir4(label)
    coupling = 1 - Fraction(1, 2 * exponent)
    last_label = 2 * cutoff + 1
    relative_exponent = casimir4(last_label)
    retained_upper = sum(
        (retained + 1) ** 2
        for retained in range(cutoff + 1)
    )
    omitted_lower = Fraction(
        sum(
            (omitted + 1) ** 2
            for omitted in range(cutoff + 1, last_label + 1)
        ),
        2,
    )
    certificate = FixedCutoffWeakCouplingObstruction(
        cutoff=cutoff,
        first_omitted_label=label,
        first_omitted_casimir4=exponent,
        witness_coupling=coupling,
        bernoulli_power_floor=Fraction(1, 2),
        actual_identity_tail_term=heat_character_sup_term(
            coupling,
            label,
        ),
        certified_identity_tail_lower_bound=Fraction(
            (label + 1) ** 2,
            2,
        ),
        relative_block_last_label=last_label,
        relative_witness_coupling=(
            1 - Fraction(1, 2 * relative_exponent)
        ),
        retained_identity_head_upper_bound=retained_upper,
        omitted_identity_block_lower_bound=omitted_lower,
        relative_tail_margin=omitted_lower - retained_upper,
        omitted_block_exceeds_retained_head=(
            omitted_lower > retained_upper
        ),
        fixed_cutoff_uniform_absolute_tail_possible=False,
        fixed_cutoff_uniform_relative_tail_possible=False,
        spacing_uniform_residual_product_modulus_proved=False,
        spacing_dependent_cutoff_or_all_label_regrouping_required=True,
        first_open_obligation=(
            "build-spacing-dependent-or-all-label-open-index-choi-tail"
        ),
    )
    if not certificate.validates():
        raise AssertionError("the weak-coupling tail obstruction drifted")
    return certificate


def fixed_cutoff_fails_requested_uniform_tolerance(
    cutoff: int,
    tolerance: Fraction,
) -> FixedCutoffWeakCouplingObstruction:
    """Return a witness whenever the requested tolerance is below the floor."""

    if tolerance < 0:
        raise ValueError("the requested absolute tolerance must be nonnegative")
    certificate = fixed_cutoff_weak_coupling_obstruction(cutoff)
    if tolerance >= certificate.certified_identity_tail_lower_bound:
        raise ValueError(
            "this witness only rejects tolerances below its explicit floor"
        )
    return certificate
