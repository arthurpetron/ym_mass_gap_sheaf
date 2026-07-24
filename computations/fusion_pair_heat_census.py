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
    GaugeFixedComplex,
    SPoly,
    casimir4,
    dimension,
    sp_clean,
    sp_mul,
)
from computations.hypercube4d_survey import (
    Face,
    FaceMeta,
    hypercube,
    kernel_basis,
    mask_orbits,
    pair_orbits,
    surface_cell_counts,
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


def surface_face_components(
    faces: list[Face],
    mask: int,
) -> tuple[int, ...]:
    """Split a binary surface into edge-connected face masks."""

    if mask < 0 or mask >> len(faces):
        raise ValueError("surface mask leaves the supplied face set")
    remaining = {
        face_index
        for face_index in range(len(faces))
        if (mask >> face_index) & 1
    }
    components: list[int] = []
    while remaining:
        seed = min(remaining)
        stack = [seed]
        remaining.remove(seed)
        component = 0
        while stack:
            current = stack.pop()
            component |= 1 << current
            current_edges = {
                edge for edge, _orientation in faces[current]
            }
            neighbours = {
                candidate
                for candidate in remaining
                if current_edges
                & {
                    edge
                    for edge, _orientation in faces[candidate]
                }
            }
            remaining.difference_update(neighbours)
            stack.extend(sorted(neighbours, reverse=True))
        components.append(component)
    return tuple(sorted(components))


def diagonal_surface_heat_activity(
    complex_: GaugeFixedComplex,
    faces: list[Face],
    mask: int,
) -> SPoly:
    """Physical activity of two identical fundamental surface strands.

    Each component contributes its vacuum channel and its uniform label-two
    channel; all proper nonempty subsets have a boundary and vanish.
    """

    activity: SPoly = {0: Fraction(1)}
    for component in surface_face_components(faces, mask):
        _vertices, _edges, face_count, euler = surface_cell_counts(
            complex_, faces, component
        )
        component_factor = {
            0: Fraction(1),
            8 * face_count: Fraction(3) ** euler,
        }
        activity = sp_mul(activity, component_factor)
    return sp_clean(activity)


@dataclass(frozen=True)
class DiagonalHeatOrbitRecord:
    """One nonempty binary-surface orbit with its duplicate activity."""

    representative: int
    orbit_size: int
    component_count: int
    heat_activity: SPoly

    @property
    def coefficientwise_positive(self) -> bool:
        return bool(self.heat_activity) and all(
            coefficient > 0 for coefficient in self.heat_activity.values()
        )


@cache
def diagonal_surface_heat_census() -> tuple[DiagonalHeatOrbitRecord, ...]:
    """Evaluate all eight nonempty duplicate-surface orbits structurally."""

    complex_, faces, meta = hypercube()
    binary_surfaces = surfaces(kernel_basis(complex_, faces))
    records = [
        DiagonalHeatOrbitRecord(
            representative=orbit[0],
            orbit_size=len(orbit),
            component_count=len(
                surface_face_components(faces, orbit[0])
            ),
            heat_activity=diagonal_surface_heat_activity(
                complex_, faces, orbit[0]
            ),
        )
        for orbit in mask_orbits(binary_surfaces[1:], symmetry_maps(meta))
    ]
    if (
        len(records) != 8
        or sum(record.orbit_size for record in records) != 127
        or not all(record.coefficientwise_positive for record in records)
    ):
        raise AssertionError("the diagonal surface heat census drifted")
    return tuple(records)
