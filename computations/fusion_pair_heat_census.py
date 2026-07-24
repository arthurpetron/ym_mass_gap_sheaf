"""Exact heat-polynomial census of intersecting binary-surface pairs.

The existing four-cube survey proved positivity of the *unweighted* complete
fusion sum on 100 intersecting pair orbits.  The physical dual activity
weights each fixed-face channel by

    prod_f (j_f + 1) w^(j_f (j_f + 2)).

Signed channels at different heat exponents therefore cannot be combined
before this weighting is inserted.  This module performs the stronger exact
census and checks positivity coefficient by coefficient.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from functools import cache

from computations.exact_haar_network import (
    SPoly,
    casimir4,
    dimension,
    sp_clean,
)
from computations.hypercube4d_survey import (
    FaceMeta,
    hypercube,
    kernel_basis,
    pair_orbits,
    surface_pair_fusion_expansion,
    surfaces,
    symmetry_maps,
    vertex_sixj_product,
)


def surface_pair_heat_activity(
    meta: list[FaceMeta],
    left: int,
    right: int,
) -> SPoly:
    """Return the exact heat-weighted complete fusion activity."""

    activity, _negative, _positive, _zero = _surface_pair_heat_ledger(
        meta, left, right
    )
    return activity


def _surface_pair_heat_ledger(
    meta: list[FaceMeta],
    left: int,
    right: int,
) -> tuple[SPoly, int, int, int]:
    """Evaluate heat coefficients and channel signs in one exact pass."""

    activity: SPoly = {}
    negative = 0
    positive = 0
    zero = 0
    for spins in surface_pair_fusion_expansion(left, right, len(meta)):
        amplitude = vertex_sixj_product(meta, spins)
        if not amplitude:
            zero += 1
            continue
        if amplitude < 0:
            negative += 1
        else:
            positive += 1
        coefficient = amplitude
        exponent = 0
        for spin in spins:
            coefficient *= dimension(spin)
            exponent += casimir4(spin)
        activity[exponent] = (
            activity.get(exponent, Fraction(0)) + coefficient
        )
        if not activity[exponent]:
            del activity[exponent]
    return sp_clean(activity), negative, positive, zero


@dataclass(frozen=True)
class PairHeatOrbitRecord:
    """One symmetry orbit with its exact signed-channel and heat ledger."""

    representative: tuple[int, int]
    orbit_size: int
    negative_channels: int
    positive_channels: int
    zero_channels: int
    heat_activity: SPoly

    @property
    def coefficientwise_positive(self) -> bool:
        return bool(self.heat_activity) and all(
            coefficient > 0 for coefficient in self.heat_activity.values()
        )


@cache
def intersecting_pair_heat_census() -> tuple[PairHeatOrbitRecord, ...]:
    """Classify and evaluate all intersecting nonempty pair orbits."""

    complex_, _faces, meta = hypercube()
    binary_surfaces = surfaces(kernel_basis(complex_, _faces))
    orbits = pair_orbits(
        binary_surfaces[1:],
        symmetry_maps(meta),
        intersecting_only=True,
    )
    records: list[PairHeatOrbitRecord] = []
    for orbit in orbits:
        left, right = orbit[0]
        activity, negative, positive, zero = _surface_pair_heat_ledger(
            meta, left, right
        )
        records.append(
            PairHeatOrbitRecord(
                representative=(left, right),
                orbit_size=len(orbit),
                negative_channels=negative,
                positive_channels=positive,
                zero_channels=zero,
                heat_activity=activity,
            )
        )
    return tuple(records)


@dataclass(frozen=True)
class PairHeatCensusCertificate:
    """Pinned finite certificate for the complete hard pair sector."""

    orbit_count: int
    raw_pair_count: int
    distinct_heat_polynomials: int
    heat_term_count_distribution: dict[int, int]
    negative_channel_profile: dict[tuple[int, int], int]
    minimum_positive_coefficient: Fraction
    all_coefficientwise_positive: bool

    def validates(self) -> bool:
        return (
            self.orbit_count == 100
            and self.raw_pair_count == 7997
            and self.distinct_heat_polynomials == 77
            and self.heat_term_count_distribution
            == {2: 40, 3: 19, 4: 23, 5: 5, 6: 9, 7: 2, 9: 2}
            and self.negative_channel_profile
            == {(4, 12): 3, (16, 48): 2, (64, 192): 1}
            and self.minimum_positive_coefficient == Fraction(1, 6561)
            and self.all_coefficientwise_positive
        )


def pair_heat_census_certificate() -> PairHeatCensusCertificate:
    """Compute and validate the exact 100-orbit physical certificate."""

    records = intersecting_pair_heat_census()
    certificate = PairHeatCensusCertificate(
        orbit_count=len(records),
        raw_pair_count=sum(record.orbit_size for record in records),
        distinct_heat_polynomials=len(
            {
                tuple(sorted(record.heat_activity.items()))
                for record in records
            }
        ),
        heat_term_count_distribution=dict(
            Counter(len(record.heat_activity) for record in records)
        ),
        negative_channel_profile=dict(
            Counter(
                (record.negative_channels, record.positive_channels)
                for record in records
                if record.negative_channels
            )
        ),
        minimum_positive_coefficient=min(
            coefficient
            for record in records
            for coefficient in record.heat_activity.values()
        ),
        all_coefficientwise_positive=all(
            record.coefficientwise_positive for record in records
        ),
    )
    if not certificate.validates():
        raise AssertionError("the pair heat census certificate drifted")
    return certificate
