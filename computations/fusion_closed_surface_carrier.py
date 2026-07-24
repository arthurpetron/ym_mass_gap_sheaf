"""Exact candidate carrier for fusion-closed corrected-slab activities.

The basis data are closed labelled surface strands, not preselected face
labels.  When strands overlap, every SU(2) character-product channel is
retained with its exact fusion multiplicity.  This is the smallest finite
carrier currently known to contain the positive surface-pair witness while
also retaining the signed fixed-face channels that it resums.

The module deliberately separates three claims:

* closure is algebraic and is implemented here;
* direct Haar evaluation equals the complete fixed-face fusion ledger, which
  is checked exactly here;
* nonnegativity of every heat-weighted family activity is the open positivity
  gate and is not assumed by the data type.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Sequence

from computations.corrected_slab_haar_network import (
    corrected_slab_haar_complex,
    evaluate_corrected_slab_assignment,
)
from computations.exact_haar_network import (
    P_ONE,
    SPoly,
    casimir4,
    chi,
    dimension,
    fusion_labels,
    sign_on_unit_interval,
    sp_add_into,
    sp_clean,
)
from computations.hypercube4d_survey import exact_constant


SpinAssignment = tuple[int, ...]
FusionLedger = dict[SpinAssignment, int]


def character_product_channels(labels: Sequence[int]) -> dict[int, int]:
    """Expand a product of SU(2) characters into irreducible characters.

    Labels are doubled spins.  Values are exact fusion-path multiplicities,
    so, for example, ``chi_1**3 = 2 chi_1 + chi_3``.
    """

    packet: dict[int, int] = {0: 1}
    for label in labels:
        if label < 0:
            raise ValueError("doubled SU(2) labels must be nonnegative")
        following: dict[int, int] = {}
        for intermediate, multiplicity in packet.items():
            for output in fusion_labels(intermediate, label):
                following[output] = following.get(output, 0) + multiplicity
        packet = following
    return packet


def is_closed_binary_surface(extent: int, mask: int) -> bool:
    """Decide mod-two edge closure for a corrected-slab face mask."""

    complex_, faces, _plaquettes = corrected_slab_haar_complex(extent)
    if mask < 0 or mask >> len(faces):
        return False
    return all(
        sum(
            1
            for face_index, face in enumerate(faces)
            if (mask >> face_index) & 1
            and any(face_edge == edge for face_edge, _orientation in face)
        )
        % 2
        == 0
        for edge in range(len(complex_.edges))
    )


@dataclass(frozen=True, order=True)
class ClosedSurfaceStrand:
    """One non-vacuum SU(2) label carried by a closed binary surface."""

    mask: int
    label: int


@dataclass(frozen=True)
class FusionClosedSurfaceFamily:
    """A canonical finite multiset of closed labelled surface strands."""

    extent: int
    strands: tuple[ClosedSurfaceStrand, ...]

    def __post_init__(self) -> None:
        if self.extent < 1:
            raise ValueError("corrected-slab extent must be positive")
        canonical = tuple(sorted(self.strands))
        object.__setattr__(self, "strands", canonical)
        for strand in canonical:
            if strand.label <= 0:
                raise ValueError("surface strands must carry a non-vacuum label")
            if strand.mask == 0:
                raise ValueError("a surface strand must contain at least one face")
            if not is_closed_binary_surface(self.extent, strand.mask):
                raise ValueError("surface strand has a nonzero mod-two boundary")

    def union(
        self, other: FusionClosedSurfaceFamily
    ) -> FusionClosedSurfaceFamily:
        """Close the carrier under insertion of another surface family."""

        if self.extent != other.extent:
            raise ValueError("surface families live on different slabs")
        return FusionClosedSurfaceFamily(
            self.extent, self.strands + other.strands
        )


def face_strand_labels(
    family: FusionClosedSurfaceFamily,
) -> tuple[tuple[int, ...], ...]:
    """List the labels crossing each face, retaining duplicate strands."""

    _complex, faces, _plaquettes = corrected_slab_haar_complex(family.extent)
    return tuple(
        tuple(
            strand.label
            for strand in family.strands
            if (strand.mask >> face_index) & 1
        )
        for face_index in range(len(faces))
    )


def complete_fusion_ledger(
    family: FusionClosedSurfaceFamily,
) -> FusionLedger:
    """Expand every face overlap and collect identical spin assignments."""

    ledger: FusionLedger = {(): 1}
    for labels in face_strand_labels(family):
        face_channels = character_product_channels(labels)
        following: FusionLedger = {}
        for prefix, prefix_multiplicity in ledger.items():
            for output, face_multiplicity in face_channels.items():
                assignment = prefix + (output,)
                following[assignment] = following.get(assignment, 0) + (
                    prefix_multiplicity * face_multiplicity
                )
        ledger = following
    return ledger


def evaluate_surface_family_direct(
    family: FusionClosedSurfaceFamily,
) -> SPoly:
    """Integrate the unfused product of all surface-strand characters."""

    complex_, faces, _plaquettes = corrected_slab_haar_complex(family.extent)
    factors = [
        chi(strand.label, complex_.holonomy_of(face))
        for strand in family.strands
        for face_index, face in enumerate(faces)
        if (strand.mask >> face_index) & 1
    ]
    return complex_.contract_invariant(factors or [dict(P_ONE)])


def evaluate_surface_family_by_channels(
    family: FusionClosedSurfaceFamily,
) -> SPoly:
    """Resum the complete fixed-face ledger with fusion multiplicities."""

    ledger = complete_fusion_ledger(family)
    channel_values = {
        spins: evaluate_corrected_slab_assignment(family.extent, spins)
        for spins in ledger
    }
    return _resum_channel_values(ledger, channel_values)


def _resum_channel_values(
    ledger: FusionLedger,
    channel_values: dict[SpinAssignment, SPoly],
) -> SPoly:
    """Resum an already-evaluated ledger without repeating Haar integrals."""

    total: SPoly = {}
    for spins, multiplicity in ledger.items():
        sp_add_into(
            total,
            channel_values[spins],
            Fraction(multiplicity),
        )
    return sp_clean(total)


def heat_weighted_fusion_activity(
    family: FusionClosedSurfaceFamily,
) -> SPoly:
    """Return the exact physical heat-weighted fusion-family activity.

    The heat coordinate is the repository's ``w``/``s`` coordinate:
    ``coeffW(w, n) = (n+1) w^(n(n+2))``.  The result is therefore a sparse
    exact polynomial whose sign on ``0 < w < 1`` is decidable for finite
    families by the existing Sturm-chain implementation.
    """

    ledger = complete_fusion_ledger(family)
    channel_values = {
        spins: evaluate_corrected_slab_assignment(family.extent, spins)
        for spins in ledger
    }
    return _heat_activity_from_channel_values(ledger, channel_values)


def _heat_activity_from_channel_values(
    ledger: FusionLedger,
    channel_values: dict[SpinAssignment, SPoly],
) -> SPoly:
    """Insert heat weights into an already-evaluated fusion ledger."""

    total: SPoly = {}
    for spins, fusion_multiplicity in ledger.items():
        amplitude = exact_constant(channel_values[spins])
        coefficient = amplitude * fusion_multiplicity
        exponent = 0
        for spin in spins:
            coefficient *= dimension(spin)
            exponent += casimir4(spin)
        if coefficient:
            total[exponent] = total.get(exponent, Fraction(0)) + coefficient
    return sp_clean(total)


@dataclass(frozen=True)
class FusionCarrierAudit:
    """Exact finite certificate for one candidate carrier element."""

    ledger_size: int
    fusion_path_count: int
    negative_fixed_channels: int
    direct_haar_amplitude: SPoly
    resummed_haar_amplitude: SPoly
    heat_activity: SPoly
    heat_sign: str

    def validates(self) -> bool:
        return (
            self.ledger_size > 0
            and self.fusion_path_count >= self.ledger_size
            and self.negative_fixed_channels >= 0
            and self.direct_haar_amplitude == self.resummed_haar_amplitude
            and self.heat_activity == sp_clean(self.heat_activity)
            and self.heat_sign == sign_on_unit_interval(self.heat_activity)
        )


def audit_surface_family(
    family: FusionClosedSurfaceFamily,
) -> FusionCarrierAudit:
    """Produce the exact closure, resummation, sign, and channel census."""

    ledger = complete_fusion_ledger(family)
    channel_polynomials = {
        spins: evaluate_corrected_slab_assignment(family.extent, spins)
        for spins in ledger
    }
    channel_constants = {
        spins: exact_constant(value)
        for spins, value in channel_polynomials.items()
    }
    direct = evaluate_surface_family_direct(family)
    resummed = _resum_channel_values(ledger, channel_polynomials)
    heat_activity = _heat_activity_from_channel_values(
        ledger, channel_polynomials
    )
    audit = FusionCarrierAudit(
        ledger_size=len(ledger),
        fusion_path_count=sum(ledger.values()),
        negative_fixed_channels=sum(
            value < 0 for value in channel_constants.values()
        ),
        direct_haar_amplitude=direct,
        resummed_haar_amplitude=resummed,
        heat_activity=heat_activity,
        heat_sign=sign_on_unit_interval(heat_activity),
    )
    if not audit.validates():
        raise AssertionError("fusion-closed carrier audit failed")
    return audit
