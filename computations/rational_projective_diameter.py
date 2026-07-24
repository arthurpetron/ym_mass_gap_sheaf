"""Exact projective-diameter certificates for finite positive kernels.

This is the executable companion to
``lean/YMGap/Continuum/RationalCrossRatioDiameter.lean``.

The engine never takes logarithms and never uses floating-point arithmetic.
For a strictly positive row/column sector it computes

    theta = max K[x,y] K[x',y'] / (K[x,y'] K[x',y])

over every ordered quadruple.  It then uses the conservative exact rational
spread ``R = theta`` (``theta >= 1``), which certainly satisfies
``theta <= R**2``, and reports

    q = (R - 1) / (R + 1) < 1.

The support-component audit is deliberately strict.  A connected component
with a zero hole is not a positive rectangle and is rejected: fusion zeros
must be removed by an honest unbranched-sector decomposition or by passing to
a proved positive primitive iterate before a Birkhoff certificate is valid.

This module certifies finite matrices only.  It does not prove that a physical
block-spin activity map is linear, that its sector is volume-local, or that
one spread works uniformly in cutoff and volume.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Sequence


RationalMatrix = tuple[tuple[Fraction, ...], ...]


def _as_fraction_matrix(
    matrix: Sequence[Sequence[int | Fraction]],
) -> RationalMatrix:
    """Normalize a rectangular nonnegative matrix to exact fractions."""

    rows = tuple(tuple(Fraction(value) for value in row) for row in matrix)
    if not rows:
        raise ValueError("a projective kernel must have at least one row")
    width = len(rows[0])
    if width == 0:
        raise ValueError("a projective kernel must have at least one column")
    if any(len(row) != width for row in rows):
        raise ValueError("the kernel matrix must be rectangular")
    if any(value < 0 for row in rows for value in row):
        raise ValueError("the positive-cone kernel cannot contain negatives")
    return rows


@dataclass(frozen=True)
class PositiveSectorCertificate:
    """Exact certificate data for one strictly positive matrix rectangle."""

    rows: tuple[int, ...]
    columns: tuple[int, ...]
    max_cross_ratio: Fraction
    spread: Fraction
    q: Fraction

    def validates(self, matrix: Sequence[Sequence[int | Fraction]]) -> bool:
        """Recheck every certificate condition directly in exact arithmetic."""

        kernel = _as_fraction_matrix(matrix)
        if not self.rows or not self.columns:
            return False
        if self.spread < 1:
            return False
        if self.q != (self.spread - 1) / (self.spread + 1):
            return False
        if not (0 <= self.q < 1):
            return False
        if any(row < 0 or row >= len(kernel) for row in self.rows):
            return False
        if any(column < 0 or column >= len(kernel[0]) for column in self.columns):
            return False
        if any(kernel[row][column] <= 0 for row in self.rows for column in self.columns):
            return False

        observed = Fraction(1)
        for first in self.rows:
            for second in self.rows:
                for left in self.columns:
                    for right in self.columns:
                        ratio = (
                            kernel[first][left]
                            * kernel[second][right]
                            / (
                                kernel[first][right]
                                * kernel[second][left]
                            )
                        )
                        observed = max(observed, ratio)
                        if (
                            kernel[first][left] * kernel[second][right]
                            > self.spread
                            * self.spread
                            * kernel[first][right]
                            * kernel[second][left]
                        ):
                            return False
        return observed == self.max_cross_ratio


@dataclass(frozen=True)
class SupportComponent:
    """One connected component of the nonzero bipartite support graph."""

    rows: tuple[int, ...]
    columns: tuple[int, ...]
    is_positive_rectangle: bool


@dataclass(frozen=True)
class SupportAudit:
    """Certified positive components and components obstructed by zero holes."""

    certificates: tuple[PositiveSectorCertificate, ...]
    obstructed_components: tuple[SupportComponent, ...]

    def is_fully_unbranched(self) -> bool:
        """Whether every nonzero support component is a positive rectangle."""

        return not self.obstructed_components


def certify_positive_sector(
    matrix: Sequence[Sequence[int | Fraction]],
    rows: Sequence[int],
    columns: Sequence[int],
) -> PositiveSectorCertificate:
    """Compute the exact cross-ratio certificate on a selected rectangle."""

    kernel = _as_fraction_matrix(matrix)
    selected_rows = tuple(dict.fromkeys(rows))
    selected_columns = tuple(dict.fromkeys(columns))
    if not selected_rows or not selected_columns:
        raise ValueError("a positive sector must select rows and columns")
    if any(row < 0 or row >= len(kernel) for row in selected_rows):
        raise IndexError("selected row lies outside the kernel")
    if any(column < 0 or column >= len(kernel[0]) for column in selected_columns):
        raise IndexError("selected column lies outside the kernel")
    if any(
        kernel[row][column] <= 0
        for row in selected_rows
        for column in selected_columns
    ):
        raise ValueError("selected sector contains a fusion-zero hole")

    theta = Fraction(1)
    for first in selected_rows:
        for second in selected_rows:
            for left in selected_columns:
                for right in selected_columns:
                    theta = max(
                        theta,
                        kernel[first][left]
                        * kernel[second][right]
                        / (
                            kernel[first][right]
                            * kernel[second][left]
                        ),
                    )

    # Taking R = theta is conservative but exact and certificate-friendly:
    # theta >= 1 implies theta <= theta^2.
    spread = theta
    q = (spread - 1) / (spread + 1)
    certificate = PositiveSectorCertificate(
        rows=selected_rows,
        columns=selected_columns,
        max_cross_ratio=theta,
        spread=spread,
        q=q,
    )
    if not certificate.validates(kernel):
        raise AssertionError("internally generated projective certificate failed")
    return certificate


def support_components(
    matrix: Sequence[Sequence[int | Fraction]],
) -> tuple[SupportComponent, ...]:
    """Decompose the nonzero bipartite support graph into exact components."""

    kernel = _as_fraction_matrix(matrix)
    row_count = len(kernel)
    column_count = len(kernel[0])
    row_neighbors = tuple(
        tuple(column for column in range(column_count) if kernel[row][column] > 0)
        for row in range(row_count)
    )
    column_neighbors = tuple(
        tuple(row for row in range(row_count) if kernel[row][column] > 0)
        for column in range(column_count)
    )

    seen_rows: set[int] = set()
    seen_columns: set[int] = set()
    components: list[SupportComponent] = []

    for starting_row in range(row_count):
        if starting_row in seen_rows or not row_neighbors[starting_row]:
            continue
        pending_rows = [starting_row]
        component_rows: set[int] = set()
        component_columns: set[int] = set()
        while pending_rows:
            row = pending_rows.pop()
            if row in component_rows:
                continue
            component_rows.add(row)
            seen_rows.add(row)
            for column in row_neighbors[row]:
                if column not in component_columns:
                    component_columns.add(column)
                    seen_columns.add(column)
                    pending_rows.extend(column_neighbors[column])

        rows = tuple(sorted(component_rows))
        columns = tuple(sorted(component_columns))
        rectangle = all(kernel[row][column] > 0 for row in rows for column in columns)
        components.append(
            SupportComponent(
                rows=rows,
                columns=columns,
                is_positive_rectangle=rectangle,
            )
        )

    # A nonzero column always has a neighboring row and was therefore reached.
    if any(
        column_neighbors[column] and column not in seen_columns
        for column in range(column_count)
    ):
        raise AssertionError("bipartite support traversal missed a nonzero column")
    return tuple(components)


def audit_support_components(
    matrix: Sequence[Sequence[int | Fraction]],
) -> SupportAudit:
    """Certify complete positive components and report zero-hole obstructions."""

    kernel = _as_fraction_matrix(matrix)
    certificates: list[PositiveSectorCertificate] = []
    obstructed: list[SupportComponent] = []
    for component in support_components(kernel):
        if component.is_positive_rectangle:
            certificates.append(
                certify_positive_sector(
                    kernel,
                    component.rows,
                    component.columns,
                )
            )
        else:
            obstructed.append(component)
    return SupportAudit(tuple(certificates), tuple(obstructed))


def common_uniform_spread(
    certificates: Sequence[PositiveSectorCertificate],
) -> tuple[Fraction, Fraction]:
    """Aggregate finitely many sectors under one exact spread and rate."""

    if not certificates:
        raise ValueError("at least one sector certificate is required")
    spread = max(certificate.spread for certificate in certificates)
    if spread < 1:
        raise AssertionError("a sector spread cannot be below one")
    return spread, (spread - 1) / (spread + 1)

