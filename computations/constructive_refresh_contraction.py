"""Exact finite search certificates for the intuitionistic BF4 route.

For a finite row-stochastic kernel ``K``, define its columnwise common floor

    floor[y] = min_x K[x, y].

The total common mass

    epsilon = sum_y floor[y]

is the largest coefficient of an input-independent packet obtainable by
entrywise minorization.  When ``epsilon > 0``,

    reference[y] = floor[y] / epsilon

and the exact residual kernel give

    K = epsilon * reference + (1 - epsilon) * residual.

This is the finite Dobrushin/refresh certificate formalized abstractly in
``ConstructiveRefreshContraction.lean``.  The code here is a search
instrument for candidate *grouped physical* kernels.  It makes no claim that
the current Yang--Mills Haar kernel has a spacing-uniform common mass.
"""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from typing import TypeAlias

RationalRow: TypeAlias = tuple[Fraction, ...]
RationalKernel: TypeAlias = tuple[RationalRow, ...]


def _fraction_row(values: Iterable[int | Fraction]) -> RationalRow:
    return tuple(Fraction(value) for value in values)


def rational_kernel(
    rows: Iterable[Iterable[int | Fraction]],
) -> RationalKernel:
    """Normalize input types and validate a nonempty stochastic rectangle."""

    kernel = tuple(_fraction_row(row) for row in rows)
    if not kernel or not kernel[0]:
        raise ValueError("a refresh kernel must be a nonempty rectangle")
    width = len(kernel[0])
    if any(len(row) != width for row in kernel):
        raise ValueError("all refresh-kernel rows must have equal length")
    if any(value < 0 for row in kernel for value in row):
        raise ValueError("a refresh kernel must be nonnegative")
    if any(sum(row, start=Fraction(0)) != 1 for row in kernel):
        raise ValueError("every refresh-kernel row must have mass one")
    return kernel


def normalize_positive_rows(
    rows: Iterable[Iterable[int | Fraction]],
) -> RationalKernel:
    """Normalize a nonnegative matrix with strictly positive row masses."""

    matrix = tuple(_fraction_row(row) for row in rows)
    if not matrix or not matrix[0]:
        raise ValueError("a positive-row matrix must be nonempty")
    width = len(matrix[0])
    if any(len(row) != width for row in matrix):
        raise ValueError("all positive-row matrix rows must have equal length")
    if any(value < 0 for row in matrix for value in row):
        raise ValueError("a positive-row matrix cannot contain negative entries")
    masses = tuple(sum(row, start=Fraction(0)) for row in matrix)
    if any(mass <= 0 for mass in masses):
        raise ValueError("every positive-row matrix row must have positive mass")
    return rational_kernel(
        tuple(
            tuple(value / masses[index] for value in row)
            for index, row in enumerate(matrix)
        )
    )


def pushforward(
    mass: Iterable[int | Fraction],
    kernel: RationalKernel,
) -> RationalRow:
    """Push one exact source mass through a finite kernel."""

    weights = _fraction_row(mass)
    if len(weights) != len(kernel):
        raise ValueError("source mass and kernel have different dimensions")
    return tuple(
        sum(
            (
                weights[source] * kernel[source][target]
                for source in range(len(kernel))
            ),
            start=Fraction(0),
        )
        for target in range(len(kernel[0]))
    )


def l1_distance(
    left: Iterable[int | Fraction],
    right: Iterable[int | Fraction],
) -> Fraction:
    """Exact finite ``l1`` distance."""

    left_row = _fraction_row(left)
    right_row = _fraction_row(right)
    if len(left_row) != len(right_row):
        raise ValueError("the two masses have different dimensions")
    return sum(
        (abs(a - b) for a, b in zip(left_row, right_row, strict=True)),
        start=Fraction(0),
    )


def compose_markov(
    first: RationalKernel,
    second: RationalKernel,
) -> RationalKernel:
    """Compose exact row-stochastic kernels: apply ``first``, then ``second``."""

    left = rational_kernel(first)
    right = rational_kernel(second)
    if len(left[0]) != len(right):
        raise ValueError("the two kernel dimensions do not compose")
    return rational_kernel(
        tuple(
            tuple(
                sum(
                    (
                        left[source][middle] * right[middle][target]
                        for middle in range(len(right))
                    ),
                    start=Fraction(0),
                )
                for target in range(len(right[0]))
            )
            for source in range(len(left))
        )
    )


def kernel_power(kernel: RationalKernel, exponent: int) -> RationalKernel:
    """Exact power of a square stochastic kernel."""

    if exponent < 1:
        raise ValueError("a grouped refresh power must be positive")
    base = rational_kernel(kernel)
    if len(base) != len(base[0]):
        raise ValueError("only square kernels can be iterated")
    result = base
    for _ in range(exponent - 1):
        result = compose_markov(result, base)
    return result


@dataclass(frozen=True)
class FiniteRefreshSearchCertificate:
    """Largest entrywise common-packet certificate for a finite kernel."""

    kernel: RationalKernel
    common_floor: RationalRow
    epsilon: Fraction
    reference: RationalRow
    rate: Fraction
    residual: RationalKernel
    strict_refresh: bool
    exact_decomposition: bool
    maximal_entrywise_common_mass: bool

    def validates(self) -> bool:
        try:
            kernel = rational_kernel(self.kernel)
            residual = rational_kernel(self.residual)
        except ValueError:
            return False
        floor = tuple(
            min(kernel[source][target] for source in range(len(kernel)))
            for target in range(len(kernel[0]))
        )
        epsilon = sum(floor, start=Fraction(0))
        if (
            self.common_floor != floor
            or self.epsilon != epsilon
            or self.rate != 1 - epsilon
            or not 0 <= epsilon <= 1
            or self.strict_refresh != (epsilon > 0)
            or self.maximal_entrywise_common_mass is not True
            or len(residual) != len(kernel)
            or len(residual[0]) != len(kernel[0])
        ):
            return False

        if epsilon > 0:
            reference = tuple(value / epsilon for value in floor)
        else:
            # No positive common packet exists.  Keep a normalized explicit
            # placeholder so the fail-closed certificate remains total.
            reference = tuple(
                Fraction(int(target == 0))
                for target in range(len(kernel[0]))
            )
        if self.reference != reference or sum(reference, Fraction(0)) != 1:
            return False

        reconstructed = tuple(
            tuple(
                epsilon * reference[target]
                + (1 - epsilon) * residual[source][target]
                for target in range(len(reference))
            )
            for source in range(len(kernel))
        )
        return (
            reconstructed == kernel
            and self.exact_decomposition
            and all(
                kernel[source][target] >= floor[target]
                for source, target in product(
                    range(len(kernel)),
                    range(len(kernel[0])),
                )
            )
        )

    def contraction_holds(
        self,
        left: Iterable[int | Fraction],
        right: Iterable[int | Fraction],
    ) -> bool:
        """Check the exact refresh contraction for one equal-mass pair."""

        left_row = _fraction_row(left)
        right_row = _fraction_row(right)
        if sum(left_row, Fraction(0)) != sum(right_row, Fraction(0)):
            raise ValueError("refresh cancellation requires equal total mass")
        return l1_distance(
            pushforward(left_row, self.kernel),
            pushforward(right_row, self.kernel),
        ) <= self.rate * l1_distance(left_row, right_row)


def maximal_refresh_certificate(
    rows: Iterable[Iterable[int | Fraction]],
) -> FiniteRefreshSearchCertificate:
    """Construct the exact maximal entrywise refresh certificate."""

    kernel = rational_kernel(rows)
    floor = tuple(
        min(kernel[source][target] for source in range(len(kernel)))
        for target in range(len(kernel[0]))
    )
    epsilon = sum(floor, start=Fraction(0))
    rate = 1 - epsilon
    if epsilon > 0:
        reference = tuple(value / epsilon for value in floor)
    else:
        reference = tuple(
            Fraction(int(target == 0))
            for target in range(len(kernel[0]))
        )
    if rate > 0:
        residual = tuple(
            tuple(
                (kernel[source][target] - floor[target]) / rate
                for target in range(len(kernel[0]))
            )
            for source in range(len(kernel))
        )
    else:
        # Every row equals the reference and the contraction rate is zero.
        # Any stochastic residual is valid; choosing the reference is total
        # and avoids division by zero.
        residual = tuple(reference for _ in kernel)
    certificate = FiniteRefreshSearchCertificate(
        kernel=kernel,
        common_floor=floor,
        epsilon=epsilon,
        reference=reference,
        rate=rate,
        residual=residual,
        strict_refresh=epsilon > 0,
        exact_decomposition=True,
        maximal_entrywise_common_mass=True,
    )
    if not certificate.validates():
        raise AssertionError("the exact refresh certificate drifted")
    return certificate


def grouped_refresh_certificates(
    kernel: RationalKernel,
    maximum_power: int,
) -> tuple[FiniteRefreshSearchCertificate, ...]:
    """Compute common-packet certificates for consecutive grouped powers."""

    if maximum_power < 1:
        raise ValueError("the grouped refresh census must be nonempty")
    base = rational_kernel(kernel)
    return tuple(
        maximal_refresh_certificate(kernel_power(base, exponent))
        for exponent in range(1, maximum_power + 1)
    )
