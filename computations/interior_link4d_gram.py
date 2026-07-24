"""Exact Gram-cone certificate for the six-valent composite-surface family.

The minimal ``(1,2,2,2)`` brick contains 12 independent elementary
three-cell boundaries through its central direction-zero link.  This module
uses the 66 symmetric differences of two such boundaries.  For their
fundamental surface observables,

``G[S,T] = integral O_S(U) O_T(U) dU``,

the diagonal has two exact values and the 2,145 off-diagonal entries reduce
to 65 stabilizer orbits.

The complete orbit census was produced by
``recompute_composite_pair_censuses``.  It is recorded below as a compact
certificate so the inexpensive regression suite can check its consequences.
An opt-in test recomputes all 65 exact Haar contractions from geometry.

The key consequence is stronger than entrywise positivity.  The smallest
diagonal exceeds 65 times the largest off-diagonal, so every row is strictly
diagonally dominant.  Together with nonnegative entries this gives the
explicit completely-positive factorization

``G = sum_i r_i e_i e_i^T
       + sum_(i<j) G_ij (e_i+e_j)(e_i+e_j)^T``,

where ``r_i = G_ii - sum_(j != i) G_ij > 0``.

This is a finite certificate for one 66-observable gluing family, not an
all-surface theorem for the brick's 44-dimensional binary kernel.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
from math import comb

from computations.interior_link4d_probe import (
    central_link_stabilizer_maps,
    composite_pair_probe_survey,
    elementary_surfaces,
    evaluate_duplicate_pair,
    minimal_interior_link_brick,
    permute_mask,
    two_cube_composite_surfaces,
    unordered_pair_orbits,
)

COMPOSITE_SURFACE_COUNT = 66

# Counts of the 65 off-diagonal stabilizer orbits by exact amplitude.
COMPOSITE_OFFDIAGONAL_ORBIT_CENSUS: tuple[tuple[Fraction, int], ...] = (
    (Fraction(1, 12288), 7),
    (Fraction(1, 16384), 16),
    (Fraction(1, 32768), 14),
    (Fraction(1, 65536), 3),
    (Fraction(1, 8192), 4),
    (Fraction(31, 3888), 1),
    (Fraction(41, 10368), 10),
    (Fraction(41, 5184), 7),
    (Fraction(5, 36864), 1),
    (Fraction(7, 27648), 2),
)

# Counts of all 2,145 raw unordered off-diagonal pairs by exact amplitude.
COMPOSITE_OFFDIAGONAL_RAW_CENSUS: tuple[tuple[Fraction, int], ...] = (
    (Fraction(1, 12288), 198),
    (Fraction(1, 16384), 540),
    (Fraction(1, 32768), 498),
    (Fraction(1, 65536), 42),
    (Fraction(1, 8192), 144),
    (Fraction(31, 3888), 24),
    (Fraction(41, 10368), 372),
    (Fraction(41, 5184), 264),
    (Fraction(5, 36864), 48),
    (Fraction(7, 27648), 15),
)

# The four surface orbits have sizes 24, 12, 24, and 6.
COMPOSITE_DIAGONAL_RAW_CENSUS: tuple[tuple[Fraction, int], ...] = (
    (Fraction(6562, 6561), 36),
    (Fraction(6724, 6561), 30),
)


@dataclass(frozen=True)
class UniformGramConeCertificate:
    """A sufficient exact certificate for a nonnegative Gram cone."""

    dimension: int
    diagonal_floor: Fraction
    offdiagonal_ceiling: Fraction

    @property
    def residual_floor(self) -> Fraction:
        """Lower-bound every diagonal-dominance residual."""

        return self.diagonal_floor - (self.dimension - 1) * self.offdiagonal_ceiling

    @property
    def is_strict(self) -> bool:
        """Whether the certificate proves strict diagonal dominance."""

        return self.residual_floor > 0


def composite_gram_cone_certificate() -> UniformGramConeCertificate:
    """Return the exact uniform certificate for the 66-surface Gram."""

    return UniformGramConeCertificate(
        dimension=COMPOSITE_SURFACE_COUNT,
        diagonal_floor=min(value for value, _count in COMPOSITE_DIAGONAL_RAW_CENSUS),
        offdiagonal_ceiling=max(value for value, _count in COMPOSITE_OFFDIAGONAL_ORBIT_CENSUS),
    )


def _mask_orbits(
    masks: tuple[int, ...],
    maps: tuple[tuple[int, ...], ...],
) -> tuple[tuple[int, ...], ...]:
    """Classify a symmetry-stable mask family."""

    remaining = set(masks)
    orbits: list[tuple[int, ...]] = []
    while remaining:
        representative = min(remaining)
        orbit = tuple(sorted({permute_mask(representative, permutation) for permutation in maps}))
        if not set(orbit) <= remaining:
            raise ValueError("composite surface family is not symmetry-stable")
        remaining.difference_update(orbit)
        orbits.append(orbit)
    return tuple(orbits)


def elementary_generator_rank() -> int:
    """Return the GF(2) rank of the 12 central-link cube boundaries."""

    _complex, _faces, meta, _central_edge = minimal_interior_link_brick()
    pivots: dict[int, int] = {}
    for surface in elementary_surfaces(meta):
        row = surface.mask
        while row:
            pivot = row.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = row
                break
            row ^= pivots[pivot]
    return len(pivots)


def elementary_generator_shell(weight: int) -> tuple[int, ...]:
    """Return XORs of exactly ``weight`` of the 12 independent generators."""

    _complex, _faces, meta, _central_edge = minimal_interior_link_brick()
    generators = tuple(surface.mask for surface in elementary_surfaces(meta))
    if weight not in range(len(generators) + 1):
        raise ValueError("generator weight must lie between zero and twelve")
    masks: list[int] = []
    for selected in combinations(range(len(generators)), weight):
        mask = 0
        for index in selected:
            mask ^= generators[index]
        masks.append(mask)
    if len(set(masks)) != comb(len(generators), weight):
        raise AssertionError("elementary boundary generators are not independent")
    return tuple(sorted(masks))


def elementary_generator_shell_orbits(
    weight: int,
) -> tuple[tuple[int, ...], ...]:
    """Classify one generator-weight shell under central-link symmetry."""

    _complex, _faces, meta, _central_edge = minimal_interior_link_brick()
    return _mask_orbits(
        elementary_generator_shell(weight),
        central_link_stabilizer_maps(meta),
    )


def elementary_generator_shell_pair_orbit_count(weight: int) -> int:
    """Count distinct unordered pair orbits within one generator shell."""

    _complex, _faces, meta, _central_edge = minimal_interior_link_brick()
    return len(
        unordered_pair_orbits(
            elementary_generator_shell(weight),
            central_link_stabilizer_maps(meta),
        )
    )


def composite_surface_orbits() -> tuple[tuple[int, ...], ...]:
    """Classify the 66 composite surfaces under the central-link stabilizer."""

    _complex, _faces, meta, _central_edge = minimal_interior_link_brick()
    return _mask_orbits(
        two_cube_composite_surfaces(meta),
        central_link_stabilizer_maps(meta),
    )


def recompute_composite_diagonal_census() -> Counter[Fraction]:
    """Recompute the 66 diagonal entries from four exact orbit representatives."""

    complex_, faces, _meta, _central_edge = minimal_interior_link_brick()
    census: Counter[Fraction] = Counter()
    for orbit in composite_surface_orbits():
        value = evaluate_duplicate_pair(
            complex_,
            faces,
            orbit[0],
            orbit[0],
        )
        census[value] += len(orbit)
    return census


def recompute_composite_pair_censuses() -> tuple[Counter[Fraction], Counter[Fraction]]:
    """Recompute all 65 exact off-diagonal orbit representatives.

    The first counter counts stabilizer orbits.  The second expands each
    representative by its orbit size and therefore counts all 2,145 raw
    pairs.  This is deliberately opt-in in the regression suite because two
    representatives dominate the exact-Haar runtime.
    """

    probes = composite_pair_probe_survey()
    orbit_census = Counter(probe.value for probe in probes)
    raw_census: Counter[Fraction] = Counter()
    for probe in probes:
        raw_census[probe.value] += probe.orbit_size
    return orbit_census, raw_census
