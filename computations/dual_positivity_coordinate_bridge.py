"""Exact coupling/cutoff bridge for the unit-rim dual manifest.

This module closes only the coordinate part of the Python-to-physical CD-2
map.  It checks that the manifest's doubled-spin convention, dimensions, and
``4*C2`` exponents agree with the Schur-normalized physical face weight

``(spin + 1) * coupling ** (spin * (spin + 2))``.

It also distinguishes support of the fixed unit rim (cutoff at least one)
from completeness of the induced page-spin sum (cutoff at least two).
Geometry, integrator semantics, complete reflected channels, and the physical
block kernel remain explicit false fields in :class:`CD2SemanticFrontier`.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import prod

from computations.dual_positivity_manifest import (
    SCHEMA,
    UnitRimManifest,
    build_unit_rim_manifest,
    manifest_sha256,
)
from computations.dual_positivity_survival import rim_channel_activity
from computations.exact_haar_network import casimir4, dim

PINNED_UNIT_RIM_MANIFEST_SHA256 = (
    "f7ad2fd06add0c8e5bc51e4aa340bdb0e86687f52d664d3ce3397f21be5d2e52"
)


def _as_fraction(numerator: int, denominator: int) -> Fraction:
    """Construct one exact manifest rational and reject malformed data."""

    if denominator <= 0:
        raise ValueError("a manifest rational denominator must be positive")
    return Fraction(numerator, denominator)


def physical_schur_face_weight(coupling: Fraction, spin: int) -> Fraction:
    """Return ``dim(spin) * coupling^(4*C2(spin))`` exactly."""

    if coupling < 0:
        raise ValueError("the physical rational coupling must be nonnegative")
    if spin < 0:
        raise ValueError("a doubled spin must be nonnegative")
    return dim(spin) * coupling ** casimir4(spin)


@dataclass(frozen=True)
class CD2SemanticFrontier:
    """A field-by-field status report for the physical CD-2 semantic bridge."""

    manifest_integrity: bool
    coupling_coordinate_pinned: bool
    boundary_channel_supported: bool
    page_sum_cutoff_complete: bool
    geometry_pinned: bool = False
    integrator_semantics_proved: bool = False
    complete_reflected_channels: bool = False
    physical_kernel_constructed: bool = False
    overlap_remainder_constructed: bool = False

    def closed_fields(self) -> tuple[str, ...]:
        """Return the semantic fields actually discharged."""

        fields = (
            ("manifest_integrity", self.manifest_integrity),
            ("coupling_coordinate_pinned", self.coupling_coordinate_pinned),
            ("boundary_channel_supported", self.boundary_channel_supported),
            ("page_sum_cutoff_complete", self.page_sum_cutoff_complete),
            ("geometry_pinned", self.geometry_pinned),
            ("integrator_semantics_proved", self.integrator_semantics_proved),
            ("complete_reflected_channels", self.complete_reflected_channels),
            ("physical_kernel_constructed", self.physical_kernel_constructed),
            ("overlap_remainder_constructed", self.overlap_remainder_constructed),
        )
        return tuple(name for name, closed in fields if closed)

    def first_open_field(self) -> str | None:
        """Return the first field in the required semantic dependency order."""

        ordered = (
            ("manifest_integrity", self.manifest_integrity),
            ("geometry_pinned", self.geometry_pinned),
            ("integrator_semantics_proved", self.integrator_semantics_proved),
            ("coupling_coordinate_pinned", self.coupling_coordinate_pinned),
            ("boundary_channel_supported", self.boundary_channel_supported),
            ("page_sum_cutoff_complete", self.page_sum_cutoff_complete),
            ("complete_reflected_channels", self.complete_reflected_channels),
            ("physical_kernel_constructed", self.physical_kernel_constructed),
            ("overlap_remainder_constructed", self.overlap_remainder_constructed),
        )
        for name, closed in ordered:
            if not closed:
                return name
        return None

    def is_cd2_closed(self) -> bool:
        """Decide the whole semantic bridge, not merely the coordinate slice."""

        return self.first_open_field() is None


@dataclass(frozen=True)
class UnitRimCoordinateBridge:
    """Exact interpretation of one manifest at pinned physical parameters."""

    coupling: Fraction
    physical_cutoff: int
    box_extent: int
    manifest: UnitRimManifest

    def __post_init__(self) -> None:
        if self.coupling < 0:
            raise ValueError("the physical rational coupling must be nonnegative")
        if self.physical_cutoff < 0:
            raise ValueError("the physical cutoff must be nonnegative")
        if self.box_extent < 0:
            raise ValueError("the box extent must be nonnegative")

    def manifest_integrity(self) -> bool:
        """Check schema, canonical digest, and the exact public conventions."""

        conventions = self.manifest.conventions
        return (
            self.manifest.schema == SCHEMA
            and manifest_sha256(self.manifest) == PINNED_UNIT_RIM_MANIFEST_SHA256
            and conventions.spin_labels == "nonnegative doubled spins n=2j"
            and conventions.irrep_dimension == "dim(n)=n+1"
            and conventions.casimir == "C2(n)=n(n+2)/4"
            and conventions.heat_coordinate == "s=exp(-t/4)"
            and conventions.heat_exponent == "4*C2(n)=n(n+2)"
        )

    def boundary_channel_supported(self) -> bool:
        """Check that every fixed rim label lies below the physical cutoff."""

        return max(self.manifest.rim_spins, default=0) <= self.physical_cutoff

    def page_sum_cutoff_complete(self) -> bool:
        """Check that all induced heat-kernel page labels are retained."""

        return self.manifest.page_spin_cutoff <= self.physical_cutoff

    def sector_coordinate_identity(self) -> bool:
        """Check every raw Haar sector against physical Schur face weights."""

        for sector in self.manifest.sectors:
            raw_amplitude = _as_fraction(
                sector.wheel_amplitude.numerator,
                sector.wheel_amplitude.denominator,
            )
            weighted_coefficient = _as_fraction(
                sector.weighted_coefficient.numerator,
                sector.weighted_coefficient.denominator,
            )
            expected_exponent = sum(casimir4(spin) for spin in sector.page_spins)
            expected_dimension_product = prod(dim(spin) for spin in sector.page_spins)
            schur_weighted_value = raw_amplitude * prod(
                physical_schur_face_weight(self.coupling, spin)
                for spin in sector.page_spins
            )
            manifest_weighted_value = (
                weighted_coefficient * self.coupling**sector.heat_exponent
            )
            if (
                sector.heat_exponent != expected_exponent
                or sector.dimension_product != expected_dimension_product
                or weighted_coefficient
                != raw_amplitude * expected_dimension_product
                or schur_weighted_value != manifest_weighted_value
            ):
                return False
        return True

    def sector_activity(self) -> Fraction:
        """Evaluate the complete exact sector ledger at the pinned coupling."""

        return sum(
            (
                _as_fraction(
                    sector.weighted_coefficient.numerator,
                    sector.weighted_coefficient.denominator,
                )
                * self.coupling**sector.heat_exponent
                for sector in self.manifest.sectors
            ),
            start=Fraction(0),
        )

    def compressed_activity(self) -> Fraction:
        """Evaluate the exponent-compressed manifest polynomial."""

        return sum(
            (
                _as_fraction(term.coefficient.numerator, term.coefficient.denominator)
                * self.coupling**term.heat_exponent
                for term in self.manifest.activity
            ),
            start=Fraction(0),
        )

    def directly_contracted_activity(self) -> Fraction:
        """Evaluate the independent exact-Haar activity polynomial."""

        polynomial = rim_channel_activity(self.manifest.rim_spins)
        return sum(
            (
                coefficient * self.coupling**exponent
                for exponent, coefficient in polynomial.items()
            ),
            start=Fraction(0),
        )

    def coupling_coordinate_pinned(self) -> bool:
        """Check sector, compressed, and direct forms in the same coordinate."""

        return (
            self.sector_coordinate_identity()
            and self.sector_activity() == self.compressed_activity()
            and self.compressed_activity() == self.directly_contracted_activity()
        )

    def semantic_frontier(self) -> CD2SemanticFrontier:
        """Return the honest partial CD-2 status after this bridge."""

        return CD2SemanticFrontier(
            manifest_integrity=self.manifest_integrity(),
            coupling_coordinate_pinned=self.coupling_coordinate_pinned(),
            boundary_channel_supported=self.boundary_channel_supported(),
            page_sum_cutoff_complete=self.page_sum_cutoff_complete(),
        )


def build_unit_rim_coordinate_bridge(
    coupling: Fraction,
    physical_cutoff: int,
    box_extent: int,
) -> UnitRimCoordinateBridge:
    """Build the exact coordinate bridge from the recomputed manifest."""

    return UnitRimCoordinateBridge(
        coupling=coupling,
        physical_cutoff=physical_cutoff,
        box_extent=box_extent,
        manifest=build_unit_rim_manifest(),
    )
