"""Machine-readable certificate export for the unit-spin wheel rim probe.

This module is deliberately an export boundary, not a semantic theorem.  It
recomputes the ``rim = (1,1,1,1)`` ledger from the actual oriented wheel
topology and exact Haar-network contraction, checks that the sector ledger
resums to the independently contracted heat activity, and serializes the
result in a stable schema suitable for a later Lean translation.

Nothing in the activity row is entered independently: sector amplitudes come
from ``wheel_value``, weighted sector coefficients come from
``rim_channel_decomposition``, and the aggregate is formed by summing that
decomposition before it is compared with ``rim_channel_activity``.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from fractions import Fraction
from functools import cache
from math import prod
from typing import TypeAlias

from computations.dual_positivity_survival import (
    OrientedWord,
    rim_channel_activity,
    rim_channel_decomposition,
    wheel_oriented_words,
    wheel_value,
)
from computations.exact_haar_network import (
    SPoly,
    casimir4,
    dim,
    sign_on_unit_interval,
    sp_add,
)

JsonObject: TypeAlias = dict[str, object]
FourSpins: TypeAlias = tuple[int, int, int, int]

SCHEMA = "ymgap.dual-positivity.unit-rim-wheel.v1"
UNIT_RIM: FourSpins = (1, 1, 1, 1)


@dataclass(frozen=True)
class RationalCertificate:
    """A reduced exact rational in a language-neutral representation."""

    numerator: int
    denominator: int

    @classmethod
    def from_fraction(cls, value: Fraction) -> RationalCertificate:
        return cls(value.numerator, value.denominator)

    def to_json_object(self) -> JsonObject:
        return {
            "numerator": self.numerator,
            "denominator": self.denominator,
        }


@dataclass(frozen=True)
class ConventionCertificate:
    """The mathematical conventions required to interpret the ledger."""

    spin_labels: str
    irrep_dimension: str
    casimir: str
    heat_coordinate: str
    heat_exponent: str
    character: str
    group_coordinates: str
    haar_measure: str

    def to_json_object(self) -> JsonObject:
        return {
            "spin_labels": self.spin_labels,
            "irrep_dimension": self.irrep_dimension,
            "casimir": self.casimir,
            "heat_coordinate": self.heat_coordinate,
            "heat_exponent": self.heat_exponent,
            "character": self.character,
            "group_coordinates": self.group_coordinates,
            "haar_measure": self.haar_measure,
        }


@dataclass(frozen=True)
class WordCertificate:
    """One ordered quaternion word, encoded as ``[link, orientation]`` steps."""

    index: int
    role: str
    steps: OrientedWord

    def to_json_object(self) -> JsonObject:
        return {
            "index": self.index,
            "role": self.role,
            "steps": [[link, orientation] for link, orientation in self.steps],
        }


@dataclass(frozen=True)
class TopologyCertificate:
    """The gauge-fixed four-page wheel incidence data."""

    integrated_links: FourSpins
    page_words: tuple[
        WordCertificate,
        WordCertificate,
        WordCertificate,
        WordCertificate,
    ]
    rim_words: tuple[
        WordCertificate,
        WordCertificate,
        WordCertificate,
        WordCertificate,
    ]

    def to_json_object(self) -> JsonObject:
        return {
            "integrated_links": list(self.integrated_links),
            "page_words": [word.to_json_object() for word in self.page_words],
            "rim_words": [word.to_json_object() for word in self.rim_words],
        }


@dataclass(frozen=True)
class SectorCertificate:
    """One nonzero page-spin sector of the exact rim decomposition."""

    page_spins: FourSpins
    heat_exponent: int
    wheel_amplitude: RationalCertificate
    dimension_product: int
    weighted_coefficient: RationalCertificate

    def to_json_object(self) -> JsonObject:
        return {
            "page_spins": list(self.page_spins),
            "heat_exponent": self.heat_exponent,
            "wheel_amplitude": self.wheel_amplitude.to_json_object(),
            "dimension_product": self.dimension_product,
            "weighted_coefficient": self.weighted_coefficient.to_json_object(),
        }


@dataclass(frozen=True)
class ActivityTermCertificate:
    """One coefficient in the aggregated exact heat activity."""

    heat_exponent: int
    sector_count: int
    coefficient: RationalCertificate

    def to_json_object(self) -> JsonObject:
        return {
            "heat_exponent": self.heat_exponent,
            "sector_count": self.sector_count,
            "coefficient": self.coefficient.to_json_object(),
        }


@dataclass(frozen=True)
class UnitRimManifest:
    """Complete finite certificate payload for the ``(1,1,1,1)`` probe."""

    schema: str
    scope: str
    conventions: ConventionCertificate
    topology: TopologyCertificate
    rim_spins: FourSpins
    page_spin_cutoff: int
    sectors: tuple[SectorCertificate, ...]
    activity: tuple[ActivityTermCertificate, ...]
    sign_on_open_unit_interval: str

    def to_json_object(self) -> JsonObject:
        return {
            "schema": self.schema,
            "scope": self.scope,
            "conventions": self.conventions.to_json_object(),
            "topology": self.topology.to_json_object(),
            "rim_spins": list(self.rim_spins),
            "page_spin_cutoff": self.page_spin_cutoff,
            "sectors": [sector.to_json_object() for sector in self.sectors],
            "activity": [term.to_json_object() for term in self.activity],
            "sign_on_open_unit_interval": self.sign_on_open_unit_interval,
        }


def _conventions() -> ConventionCertificate:
    return ConventionCertificate(
        spin_labels="nonnegative doubled spins n=2j",
        irrep_dimension="dim(n)=n+1",
        casimir="C2(n)=n(n+2)/4",
        heat_coordinate="s=exp(-t/4)",
        heat_exponent="4*C2(n)=n(n+2)",
        character="chi_n(q)=U_n(scalar(q)); chi_0=1; chi_1=2w",
        group_coordinates="unit quaternion q=(w,x,y,z)",
        haar_measure="normalized uniform probability measure on S^3",
    )


def _topology() -> TopologyCertificate:
    page_words, rim_words = wheel_oriented_words()
    pages = tuple(
        WordCertificate(index, "page:X_i", word)
        for index, word in enumerate(page_words)
    )
    rims = tuple(
        WordCertificate(index, "rim:X_i*X_(i+1)^-1", word)
        for index, word in enumerate(rim_words)
    )
    return TopologyCertificate(
        integrated_links=(0, 1, 2, 3),
        page_words=(pages[0], pages[1], pages[2], pages[3]),
        rim_words=(rims[0], rims[1], rims[2], rims[3]),
    )


def _single_term(p: SPoly, context: str) -> tuple[int, Fraction]:
    if len(p) != 1:
        raise AssertionError(f"{context} must have one heat monomial; got {p}")
    return next(iter(p.items()))


@cache
def build_unit_rim_manifest() -> UnitRimManifest:
    """Recompute, cross-check, and package the unit-rim certificate."""

    decomposition = rim_channel_decomposition(UNIT_RIM)
    aggregate: SPoly = {}
    sector_counts: dict[int, int] = {}
    sectors: list[SectorCertificate] = []

    for page_spins_raw, weighted_poly in sorted(decomposition.items()):
        if len(page_spins_raw) != 4:
            raise AssertionError(f"malformed page sector {page_spins_raw}")
        pages: FourSpins = (
            page_spins_raw[0],
            page_spins_raw[1],
            page_spins_raw[2],
            page_spins_raw[3],
        )
        exponent, weighted_coefficient = _single_term(
            weighted_poly, f"weighted sector {pages}"
        )
        raw_exponent, wheel_amplitude = _single_term(
            wheel_value(pages, UNIT_RIM), f"wheel sector {pages}"
        )
        if raw_exponent != 0:
            raise AssertionError(f"fixed-spin wheel sector depends on s: {pages}")

        expected_exponent = sum(casimir4(spin) for spin in pages)
        dimension_product = prod(dim(spin) for spin in pages)
        if exponent != expected_exponent:
            raise AssertionError(
                f"sector {pages} exponent {exponent} != {expected_exponent}"
            )
        if weighted_coefficient != dimension_product * wheel_amplitude:
            raise AssertionError(f"sector {pages} has inconsistent weighting")

        aggregate = sp_add(aggregate, weighted_poly)
        sector_counts[exponent] = sector_counts.get(exponent, 0) + 1
        sectors.append(
            SectorCertificate(
                page_spins=pages,
                heat_exponent=exponent,
                wheel_amplitude=RationalCertificate.from_fraction(wheel_amplitude),
                dimension_product=dimension_product,
                weighted_coefficient=RationalCertificate.from_fraction(
                    weighted_coefficient
                ),
            )
        )

    directly_contracted = rim_channel_activity(UNIT_RIM)
    if aggregate != directly_contracted:
        raise AssertionError(
            "sector decomposition does not resum to the contracted activity"
        )

    activity = tuple(
        ActivityTermCertificate(
            heat_exponent=exponent,
            sector_count=sector_counts[exponent],
            coefficient=RationalCertificate.from_fraction(coefficient),
        )
        for exponent, coefficient in sorted(aggregate.items())
    )
    cutoff = max(
        UNIT_RIM[(index - 1) % 4] + UNIT_RIM[index]
        for index in range(4)
    )
    return UnitRimManifest(
        schema=SCHEMA,
        scope="finite exact computation certificate; not a semantic theorem",
        conventions=_conventions(),
        topology=_topology(),
        rim_spins=UNIT_RIM,
        page_spin_cutoff=cutoff,
        sectors=tuple(sectors),
        activity=activity,
        sign_on_open_unit_interval=sign_on_unit_interval(aggregate),
    )


def canonical_manifest_json(manifest: UnitRimManifest | None = None) -> str:
    """Serialize a manifest with stable key order and no insignificant space."""

    payload = build_unit_rim_manifest() if manifest is None else manifest
    return json.dumps(
        payload.to_json_object(),
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
    )


def manifest_sha256(manifest: UnitRimManifest | None = None) -> str:
    """Return the lowercase SHA-256 digest of the canonical JSON bytes."""

    return hashlib.sha256(canonical_manifest_json(manifest).encode("utf-8")).hexdigest()


def main() -> None:
    """Print the canonical certificate followed by its digest."""

    print(canonical_manifest_json())
    print(manifest_sha256())


if __name__ == "__main__":
    main()
