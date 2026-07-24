"""Exact local kernel for two fundamental SU(2) surface strands.

The four-strand Haar integral is the projector onto the two-dimensional
invariant space in ``(1/2)^(tensor 4)``.  This module records that projector
in three equivalent exact normalizations:

* the identity/swap diagram Gram matrix and its inverse;
* the rational Wigner-6j table for the spin-zero/spin-one fusion channels;
* the dimension-stripped two-state crossing weight used by the signed
  four-cube surface-pair ledgers.

The local projector is positive semidefinite, although its diagram expansion
has negative off-diagonal coefficients.  For the cancellation-requiring
four-cube pairs, the crossing graph is complete bipartite and its full
channel sum has a manifestly positive binomial resummation.
"""

from __future__ import annotations

from fractions import Fraction
from math import comb
from typing import TypeAlias

Matrix2: TypeAlias = tuple[
    tuple[Fraction, Fraction],
    tuple[Fraction, Fraction],
]
FusionBit: TypeAlias = int


# The raw identity and swap tensors have squared norm four and mutual inner
# product two.
DIAGRAM_GRAM: Matrix2 = (
    (Fraction(4), Fraction(2)),
    (Fraction(2), Fraction(4)),
)

# Weingarten coefficients for the normalized two-copy SU(2) Haar integral.
DIAGRAM_GRAM_INVERSE: Matrix2 = (
    (Fraction(1, 3), Fraction(-1, 6)),
    (Fraction(-1, 6), Fraction(1, 3)),
)

# J[a,b] = {1/2 1/2 a; 1/2 1/2 b}, for a,b in {0,1}.
FUNDAMENTAL_SIXJ: Matrix2 = (
    (Fraction(-1, 2), Fraction(1, 2)),
    (Fraction(1, 2), Fraction(1, 6)),
)

# After division by the singlet background J[0,0] = -1/2 and the harmless
# channel gauge g = (1,-1), the crossing weight is entrywise positive except
# for the triplet-triplet entry.
CROSSING_WEIGHT: Matrix2 = (
    (Fraction(1), Fraction(1)),
    (Fraction(1), Fraction(-1, 3)),
)


def matrix_product(left: Matrix2, right: Matrix2) -> Matrix2:
    """Multiply two exact 2x2 matrices."""

    return (
        (
            left[0][0] * right[0][0] + left[0][1] * right[1][0],
            left[0][0] * right[0][1] + left[0][1] * right[1][1],
        ),
        (
            left[1][0] * right[0][0] + left[1][1] * right[1][0],
            left[1][0] * right[0][1] + left[1][1] * right[1][1],
        ),
    )


def matrix_power(matrix: Matrix2, exponent: int) -> Matrix2:
    """Raise an exact 2x2 matrix to a nonnegative integer power."""

    if exponent < 0:
        raise ValueError("matrix exponent must be nonnegative")
    result: Matrix2 = (
        (Fraction(1), Fraction(0)),
        (Fraction(0), Fraction(1)),
    )
    factor = matrix
    remaining = exponent
    while remaining:
        if remaining % 2:
            result = matrix_product(result, factor)
        factor = matrix_product(factor, factor)
        remaining //= 2
    return result


def trace_power(matrix: Matrix2, exponent: int) -> Fraction:
    """Return the exact trace of a nonnegative matrix power."""

    power = matrix_power(matrix, exponent)
    return power[0][0] + power[1][1]


def crossing_graph_weight(
    channel_mask: int,
    vertex_count: int,
    edges: tuple[tuple[int, int], ...],
) -> Fraction:
    """Evaluate one resolved zero/triplet assignment on a crossing graph."""

    if channel_mask < 0 or channel_mask >> vertex_count:
        raise ValueError("channel mask leaves the crossing graph")
    value = Fraction(1)
    for left, right in edges:
        if left not in range(vertex_count) or right not in range(vertex_count) or left == right:
            raise ValueError("crossing edges must join distinct graph vertices")
        left_channel = (channel_mask >> left) & 1
        right_channel = (channel_mask >> right) & 1
        value *= CROSSING_WEIGHT[left_channel][right_channel]
    return value


def complete_bipartite_channel_parities(
    channel_mask: int,
    left_size: int,
    right_size: int,
) -> tuple[int, int]:
    """Return the two channel parities on ``K_(left_size,right_size)``."""

    vertex_count = left_size + right_size
    if channel_mask < 0 or channel_mask >> vertex_count:
        raise ValueError("channel mask leaves the crossing graph")
    left_parity = (channel_mask & ((1 << left_size) - 1)).bit_count() % 2
    right_parity = (channel_mask >> left_size).bit_count() % 2
    return left_parity, right_parity


def crossing_quadratic_refinement(
    channel_mask: int,
    left_size: int,
    right_size: int,
) -> int:
    """Return the exact sign exponent ``q(x)=parity_L(x)*parity_R(x)``.

    Its polarization is the standard alternating form on the two-dimensional
    parity quotient.  Redistributing selected channels within either
    bipartition lies in the radical and does not affect the sign.
    """

    left_parity, right_parity = complete_bipartite_channel_parities(
        channel_mask,
        left_size,
        right_size,
    )
    return left_parity * right_parity


def crossing_polarization(
    left_mask: int,
    right_mask: int,
    left_size: int,
    right_size: int,
) -> int:
    """Polarize ``q`` over GF(2)."""

    return (
        crossing_quadratic_refinement(
            left_mask ^ right_mask,
            left_size,
            right_size,
        )
        ^ crossing_quadratic_refinement(left_mask, left_size, right_size)
        ^ crossing_quadratic_refinement(right_mask, left_size, right_size)
    )


def spin_parity_sector_partition(
    left_size: int,
    right_size: int,
) -> tuple[Fraction, Fraction, Fraction, Fraction]:
    """Return positive magnitudes in parity sectors ``00,01,10,11``.

    The signed complete partition is ``Z00 + Z01 + Z10 - Z11``.  This is the
    exact four-sector decomposition suggested by the spin-structure analogy;
    no geometric identification with a global spin structure is assumed.
    """

    if left_size < 0 or right_size < 0:
        raise ValueError("bipartition sizes must be nonnegative")
    sectors = [Fraction(0), Fraction(0), Fraction(0), Fraction(0)]
    for left_selected in range(left_size + 1):
        for right_selected in range(right_size + 1):
            sector = 2 * (left_selected % 2) + right_selected % 2
            sectors[sector] += (
                Fraction(comb(left_size, left_selected))
                * Fraction(comb(right_size, right_selected))
                * Fraction(1, 3) ** (left_selected * right_selected)
            )
    return sectors[0], sectors[1], sectors[2], sectors[3]


def signed_spin_parity_partition(
    left_size: int,
    right_size: int,
) -> Fraction:
    """Resume the four parity sectors with the quadratic-refinement sign."""

    sector_00, sector_01, sector_10, sector_11 = spin_parity_sector_partition(left_size, right_size)
    return sector_00 + sector_01 + sector_10 - sector_11


def spin_structure_twisted_partition(
    left_size: int,
    right_size: int,
    left_twist: int,
    right_twist: int,
) -> Fraction:
    """Resume the sectors with ``q(a,b)=ab+left_twist*a+right_twist*b``.

    The four binary twists are all quadratic refinements of the same
    polarization.  They redistribute, rather than remove, the negative
    parity sectors.
    """

    if left_twist not in (0, 1) or right_twist not in (0, 1):
        raise ValueError("spin-structure twists must be binary")
    sectors = spin_parity_sector_partition(left_size, right_size)
    return sum(
        (
            (-1)
            ** (left_parity * right_parity + left_twist * left_parity + right_twist * right_parity)
            * sectors[2 * left_parity + right_parity]
            for left_parity in (0, 1)
            for right_parity in (0, 1)
        ),
        start=Fraction(0),
    )


def arf_unsigned_reconstruction(
    left_size: int,
    right_size: int,
) -> Fraction:
    """Apply the torus Arf transform to the four twisted partitions.

    With ``Arf(q+alpha*a+beta*b)=alpha*beta``, the half-sum

    ``1/2 sum_(alpha,beta) (-1)^(alpha*beta) P_(alpha,beta)``

    reconstructs the sum of the four *positive magnitude* sectors.  It does
    not reconstruct the untwisted physical SU(2) partition ``P_(0,0)``.
    """

    return Fraction(1, 2) * sum(
        (
            (-1) ** (left_twist * right_twist)
            * spin_structure_twisted_partition(
                left_size,
                right_size,
                left_twist,
                right_twist,
            )
            for left_twist in (0, 1)
            for right_twist in (0, 1)
        ),
        start=Fraction(0),
    )


def complete_bipartite_edges(left_size: int, right_size: int) -> tuple[tuple[int, int], ...]:
    """Return the canonical edge set of ``K_(left_size,right_size)``."""

    if left_size < 0 or right_size < 0:
        raise ValueError("bipartition sizes must be nonnegative")
    return tuple(
        (left, left_size + right) for left in range(left_size) for right in range(right_size)
    )


def complete_bipartite_partition(left_size: int, right_size: int) -> Fraction:
    """Sum every crossing channel on a complete bipartite graph.

    If exactly ``chosen`` vertices on the left carry the triplet channel,
    summing one right-hand channel gives

    ``1 + (-1/3)^chosen``.

    Consequently every summand in the returned binomial formula is strictly
    positive.  This proves positivity without enumerating ``2^(m+n)``
    resolved channels.
    """

    if left_size < 0 or right_size < 0:
        raise ValueError("bipartition sizes must be nonnegative")
    triplet_weight = Fraction(-1, 3)
    return sum(
        (
            Fraction(comb(left_size, chosen)) * (Fraction(1) + triplet_weight**chosen) ** right_size
            for chosen in range(left_size + 1)
        ),
        start=Fraction(0),
    )


def explicit_complete_bipartite_partition(left_size: int, right_size: int) -> Fraction:
    """Enumerate the same complete-bipartite channel sum as an exact check."""

    edges = complete_bipartite_edges(left_size, right_size)
    vertex_count = left_size + right_size
    return sum(
        (
            crossing_graph_weight(channel_mask, vertex_count, edges)
            for channel_mask in range(1 << vertex_count)
        ),
        start=Fraction(0),
    )
