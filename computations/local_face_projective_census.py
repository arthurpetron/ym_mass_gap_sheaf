"""Exact projective census of the corrected-slab local face kernel.

For a fine four-spin packet ``(a,b,c,d)`` and retained coarse spin ``s``,
the local kernel in
``Z4DyadicSlabCharacterFusionConditionalKernel.lean`` is

    K_w[(a,b,c,d),s] = coeffW(w,s) * M[(a,b,c,d),s],

where

    M[p,s] = sum_{x,y} N_ab^x N_cd^y N_xy^s.

Thus the heat-kernel activity is a target-column scaling and cancels from
every matrix cross-ratio.  This module computes the remaining integer
fusion geometry exactly.

The one-step support is audited without silently deleting fusion zeros.  We
also audit the reflected Gram primitive ``M.T @ M``, the smallest square
positive operator naturally suggested by the slab's reflection/SOS
factorization.  A positive Gram block gives a valid finite Birkhoff
certificate at a fixed cutoff; it does *not* by itself give a uniform
cutoff bound.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import product

from computations.core_b_pilot import coeff_w, fusion_ind
from computations.rational_projective_diameter import (
    SupportAudit,
    audit_support_components,
    common_uniform_spread,
)


Packet = tuple[int, int, int, int]
IntegerMatrix = tuple[tuple[int, ...], ...]
RationalMatrix = tuple[tuple[Fraction, ...], ...]


def face_packets(cutoff: int) -> tuple[Packet, ...]:
    """The exact four-character packet state space at ``cutoff``."""

    if cutoff < 0:
        raise ValueError("cutoff must be nonnegative")
    return tuple(product(range(cutoff + 1), repeat=4))


def local_face_fusion_multiplicity(
    packet: Packet,
    retained_spin: int,
    cutoff: int,
) -> int:
    """Return ``sum N_ab^x N_cd^y N_xy^s`` with the Lean channel bounds."""

    if cutoff < 0 or retained_spin < 0:
        raise ValueError("cutoff and retained spin must be nonnegative")
    if any(spin < 0 or spin > cutoff for spin in packet):
        raise ValueError("packet lies outside the selected cutoff")
    a, b, c, d = packet
    return sum(
        fusion_ind(a, b, left)
        * fusion_ind(c, d, right)
        * fusion_ind(left, right, retained_spin)
        for left in range(2 * cutoff + 1)
        for right in range(2 * cutoff + 1)
    )


def local_face_multiplicity_matrix(cutoff: int) -> IntegerMatrix:
    """Rows are fine packets; columns are spins ``0..4*cutoff``."""

    return tuple(
        tuple(
            local_face_fusion_multiplicity(packet, retained_spin, cutoff)
            for retained_spin in range(4 * cutoff + 1)
        )
        for packet in face_packets(cutoff)
    )


def physical_local_face_matrix(cutoff: int, coupling: Fraction) -> RationalMatrix:
    """Evaluate the literal local face kernel at an exact rational coupling."""

    if coupling <= 0:
        raise ValueError("the projective census requires positive coupling")
    multiplicities = local_face_multiplicity_matrix(cutoff)
    column_scales = tuple(
        Fraction(coeff_w(coupling, retained_spin))
        for retained_spin in range(4 * cutoff + 1)
    )
    return tuple(
        tuple(
            Fraction(entry) * column_scales[column]
            for column, entry in enumerate(row)
        )
        for row in multiplicities
    )


def reflected_gram(matrix: IntegerMatrix | RationalMatrix) -> RationalMatrix:
    """Return the exact square Gram primitive ``matrix.T @ matrix``."""

    if not matrix or not matrix[0]:
        raise ValueError("matrix must be nonempty")
    width = len(matrix[0])
    if any(len(row) != width for row in matrix):
        raise ValueError("matrix must be rectangular")
    return tuple(
        tuple(
            sum(
                (Fraction(row[left]) * Fraction(row[right]) for row in matrix),
                Fraction(0),
            )
            for right in range(width)
        )
        for left in range(width)
    )


@dataclass(frozen=True)
class LocalFaceProjectiveCensus:
    """Exact one-step and reflected-primitive audits at one cutoff."""

    cutoff: int
    one_step: SupportAudit
    reflected_gram: SupportAudit
    gram_uniform_spread: Fraction
    gram_uniform_q: Fraction


def local_face_projective_census(cutoff: int) -> LocalFaceProjectiveCensus:
    """Audit the literal fusion support and its reflected Gram primitive."""

    multiplicities = local_face_multiplicity_matrix(cutoff)
    one_step = audit_support_components(multiplicities)
    gram_audit = audit_support_components(reflected_gram(multiplicities))
    spread, q = common_uniform_spread(gram_audit.certificates)
    return LocalFaceProjectiveCensus(
        cutoff=cutoff,
        one_step=one_step,
        reflected_gram=gram_audit,
        gram_uniform_spread=spread,
        gram_uniform_q=q,
    )


def _main() -> None:
    for cutoff in range(1, 8):
        census = local_face_projective_census(cutoff)
        print(
            f"N={cutoff}: "
            f"one-step-obstructions={len(census.one_step.obstructed_components)}, "
            f"gram-positive-sectors={len(census.reflected_gram.certificates)}, "
            f"R={census.gram_uniform_spread}, q={census.gram_uniform_q} "
            f"({float(census.gram_uniform_q):.12f})"
        )


if __name__ == "__main__":
    _main()
