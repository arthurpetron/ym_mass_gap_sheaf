"""Emit Lean-checkable exact boundary-message rank-one certificates.

The input is a finite positive rational matrix, positive source/target
profiles, and a positive terminal message.  This program checks with Python
``Fraction`` arithmetic that every relative entry error is at most ``1/16``
and emits Lean source containing the literal data.  Lean still rechecks every
entry, constructs the cross-ratio certificate, and proves terminal-message
quarter contraction.

This executable is an untrusted certificate producer.  A successful Python,
Rust, or C run is never treated as a proof; only compilation of the emitted
Lean declarations is load-bearing.

JSON schema::

    {
      "kernel": [["21/2", "19/10"], ["57/4", "63/20"]],
      "source_profile": ["2", "3"],
      "target_profile": ["5", "1"],
      "terminal": ["7", "11"]
    }

Finite-prefix/tail schema::

    {
      "prefix_errors": ["1/32", "1/20", "1/16"]
    }

Computed-floor prefix/tail schema::

    {
      "prefix_error_majorants": ["1/8192", "3/16384", "1/2048"],
      "prefix_floors": ["1/2", "3/4", "1"]
    }

Canonical regularized rank-one matrix-prefix schema::

    {
      "scales": [
        {
          "amplitude": [["1", "1"], ["2", "2"]],
          "pseudocount": "1"
        },
        {
          "amplitude": [["4096", "4095"]],
          "pseudocount": "1"
        }
      ]
    }

For each scale this mode forms the aggregate column profile

``(pseudocount + column sum) / (total mass + columns * pseudocount)``

with exact ``Fraction`` arithmetic, then computes ``row mass * profile``, the
maximum entry defect, the maximum pairwise cross-row residual, the induced
finite-statistical defect budget, and the minimum projected entry.  The
emitted Lean file contains every literal matrix and rechecks the pairwise,
statistical-budget, defect, and floor inequalities.  As in the other prefix
modes, identification with the genuine BF4 amplitude and the infinite
cross-tail inequality remain explicit inputs.

Each error majorant must be at most ``1/2048`` times the corresponding
strictly positive floor.  The emitted Lean constructor rechecks those finite
inequalities and keeps the all-tail division-free cross inequality explicit.

The final entry is the threshold error.  The prefix emitter checks every
listed value against ``1/16`` and emits a Lean constructor which still asks
its caller for exact identification with the physical error stream and for
the analytic antitone-tail theorem.  Thus finite computation cannot silently
stand in for the infinite argument.

Run the built-in exact example with::

    python3 computations/boundary_message_lean_certificate.py --demo

Or consume a JSON certificate produced by another exact program with::

    python3 computations/boundary_message_lean_certificate.py \
      --input certificate.json --name bf4Pilot

Emit a finite-prefix/analytic-tail adapter with::

    python3 computations/boundary_message_lean_certificate.py \
      --prefix-input prefix.json --name bf4Prefix

Emit the computed-floor physical-error prefix adapter with::

    python3 computations/boundary_message_lean_certificate.py \
      --floor-prefix-input floor-prefix.json --name bf4FloorPrefix

Derive that adapter from exact finite amplitude matrices with::

    python3 computations/boundary_message_lean_certificate.py \
      --regularized-prefix-input matrices.json --name bf4RegularizedPrefix
"""

from __future__ import annotations

import argparse
import json
import os
import re
from concurrent.futures import ProcessPoolExecutor
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any


RELATIVE_TOLERANCE = Fraction(1, 16)
PHYSICAL_ERROR_TOLERANCE = Fraction(1, 2048)


def _fraction(value: Any) -> Fraction:
    if isinstance(value, bool):
        raise ValueError("Boolean values are not rational certificate entries")
    try:
        return Fraction(value)
    except (TypeError, ValueError, ZeroDivisionError) as error:
        raise ValueError(f"invalid rational certificate entry: {value!r}") from error


def _vector(values: Any, *, label: str) -> tuple[Fraction, ...]:
    if not isinstance(values, list) or not values:
        raise ValueError(f"{label} must be a nonempty JSON list")
    vector = tuple(_fraction(value) for value in values)
    if any(value <= 0 for value in vector):
        raise ValueError(f"{label} must be strictly positive")
    return vector


@dataclass(frozen=True)
class RelativeRankOneLeanCertificate:
    """Exact finite data accepted by the Lean rank-one producer."""

    kernel: tuple[tuple[Fraction, ...], ...]
    source_profile: tuple[Fraction, ...]
    target_profile: tuple[Fraction, ...]
    terminal: tuple[Fraction, ...]

    @classmethod
    def from_json(cls, payload: dict[str, Any]) -> "RelativeRankOneLeanCertificate":
        if not isinstance(payload, dict):
            raise ValueError("the certificate payload must be a JSON object")
        source_profile = _vector(payload.get("source_profile"), label="source_profile")
        target_profile = _vector(payload.get("target_profile"), label="target_profile")
        terminal = _vector(payload.get("terminal"), label="terminal")
        raw_kernel = payload.get("kernel")
        if not isinstance(raw_kernel, list) or not raw_kernel:
            raise ValueError("kernel must be a nonempty JSON matrix")
        kernel = tuple(
            _vector(row, label=f"kernel row {row_index}")
            for row_index, row in enumerate(raw_kernel)
        )
        if len(kernel) != len(source_profile):
            raise ValueError("kernel height must match source_profile")
        if any(len(row) != len(target_profile) for row in kernel):
            raise ValueError("kernel width must match target_profile")
        if len(terminal) != len(target_profile):
            raise ValueError("terminal length must match target_profile")
        certificate = cls(
            kernel=kernel,
            source_profile=source_profile,
            target_profile=target_profile,
            terminal=terminal,
        )
        certificate.require_relative_tolerance()
        return certificate

    @property
    def relative_errors(self) -> tuple[tuple[Fraction, ...], ...]:
        return tuple(
            tuple(
                abs(entry - self.source_profile[row] * self.target_profile[column])
                / (self.source_profile[row] * self.target_profile[column])
                for column, entry in enumerate(kernel_row)
            )
            for row, kernel_row in enumerate(self.kernel)
        )

    @property
    def maximum_relative_error(self) -> Fraction:
        return max(error for row in self.relative_errors for error in row)

    def require_relative_tolerance(self) -> None:
        error = self.maximum_relative_error
        if error > RELATIVE_TOLERANCE:
            raise ValueError(
                f"maximum relative error {error} exceeds {RELATIVE_TOLERANCE}"
            )


@dataclass(frozen=True)
class QuarterErrorPrefixLeanCertificate:
    """Finite exact relative-error values through one tail threshold."""

    errors: tuple[Fraction, ...]

    @classmethod
    def from_json(cls, payload: dict[str, Any]) -> "QuarterErrorPrefixLeanCertificate":
        if not isinstance(payload, dict):
            raise ValueError("the certificate payload must be a JSON object")
        raw_errors = payload.get("prefix_errors")
        if not isinstance(raw_errors, list) or not raw_errors:
            raise ValueError("prefix_errors must be a nonempty JSON list")
        errors = tuple(_fraction(value) for value in raw_errors)
        if any(value < 0 for value in errors):
            raise ValueError("prefix_errors must be nonnegative")
        certificate = cls(errors=errors)
        certificate.require_relative_tolerance()
        return certificate

    @property
    def threshold(self) -> int:
        return len(self.errors) - 1

    @property
    def maximum_error(self) -> Fraction:
        return max(self.errors)

    def require_relative_tolerance(self) -> None:
        error = self.maximum_error
        if error > RELATIVE_TOLERANCE:
            raise ValueError(
                f"maximum prefix error {error} exceeds {RELATIVE_TOLERANCE}"
            )


@dataclass(frozen=True)
class ComputedFloorPrefixLeanCertificate:
    """Finite exact error majorants and positive ideal floors."""

    errors: tuple[Fraction, ...]
    floors: tuple[Fraction, ...]

    @classmethod
    def from_json(cls, payload: dict[str, Any]) -> "ComputedFloorPrefixLeanCertificate":
        if not isinstance(payload, dict):
            raise ValueError("the certificate payload must be a JSON object")
        raw_errors = payload.get("prefix_error_majorants")
        raw_floors = payload.get("prefix_floors")
        if not isinstance(raw_errors, list) or not raw_errors:
            raise ValueError("prefix_error_majorants must be a nonempty JSON list")
        if not isinstance(raw_floors, list) or not raw_floors:
            raise ValueError("prefix_floors must be a nonempty JSON list")
        errors = tuple(_fraction(value) for value in raw_errors)
        floors = tuple(_fraction(value) for value in raw_floors)
        if len(errors) != len(floors):
            raise ValueError("prefix_error_majorants and prefix_floors must have equal length")
        if any(value < 0 for value in errors):
            raise ValueError("prefix_error_majorants must be nonnegative")
        if any(value <= 0 for value in floors):
            raise ValueError("prefix_floors must be strictly positive")
        certificate = cls(errors=errors, floors=floors)
        certificate.require_physical_tolerance()
        return certificate

    @property
    def threshold(self) -> int:
        return len(self.errors) - 1

    @property
    def relative_errors(self) -> tuple[Fraction, ...]:
        return tuple(error / floor for error, floor in zip(self.errors, self.floors, strict=True))

    @property
    def maximum_relative_error(self) -> Fraction:
        return max(self.relative_errors)

    def require_physical_tolerance(self) -> None:
        error = self.maximum_relative_error
        if error > PHYSICAL_ERROR_TOLERANCE:
            raise ValueError(
                f"maximum error/floor ratio {error} exceeds {PHYSICAL_ERROR_TOLERANCE}"
            )


@dataclass(frozen=True)
class RegularizedRankOneScaleCertificate:
    """One exact finite amplitude matrix and its canonical rank-one projection."""

    amplitude: tuple[tuple[Fraction, ...], ...]
    pseudocount: Fraction
    source_shard_size: int = 1

    @classmethod
    def from_json(
        cls, payload: dict[str, Any], *, scale: int
    ) -> "RegularizedRankOneScaleCertificate":
        if not isinstance(payload, dict):
            raise ValueError(f"scale {scale} must be a JSON object")
        raw_amplitude = payload.get("amplitude")
        if not isinstance(raw_amplitude, list) or not raw_amplitude:
            raise ValueError(f"scale {scale} amplitude must be a nonempty JSON matrix")
        rows: list[tuple[Fraction, ...]] = []
        width: int | None = None
        for row_index, raw_row in enumerate(raw_amplitude):
            if not isinstance(raw_row, list) or not raw_row:
                raise ValueError(
                    f"scale {scale} amplitude row {row_index} must be nonempty"
                )
            row = tuple(_fraction(value) for value in raw_row)
            if any(value < 0 for value in row):
                raise ValueError(f"scale {scale} amplitude must be nonnegative")
            if width is None:
                width = len(row)
            elif len(row) != width:
                raise ValueError(f"scale {scale} amplitude must be rectangular")
            if sum(row, Fraction(0)) <= 0:
                raise ValueError(
                    f"scale {scale} amplitude row {row_index} must have positive mass"
                )
            rows.append(row)
        pseudocount = _fraction(payload.get("pseudocount"))
        if pseudocount <= 0:
            raise ValueError(f"scale {scale} pseudocount must be strictly positive")
        source_shard_size = payload.get("source_shard_size", 1)
        if not isinstance(source_shard_size, int) or isinstance(source_shard_size, bool):
            raise ValueError(f"scale {scale} source_shard_size must be an integer")
        if source_shard_size <= 0:
            raise ValueError(f"scale {scale} source_shard_size must be positive")
        return cls(
            amplitude=tuple(rows),
            pseudocount=pseudocount,
            source_shard_size=source_shard_size,
        )

    @property
    def source_count(self) -> int:
        return len(self.amplitude)

    @property
    def target_count(self) -> int:
        return len(self.amplitude[0])

    @property
    def column_masses(self) -> tuple[Fraction, ...]:
        return tuple(
            sum((row[target] for row in self.amplitude), Fraction(0))
            for target in range(self.target_count)
        )

    @property
    def numerators(self) -> tuple[Fraction, ...]:
        return tuple(self.pseudocount + mass for mass in self.column_masses)

    @property
    def denominator(self) -> Fraction:
        return sum(self.numerators, Fraction(0))

    @property
    def profile(self) -> tuple[Fraction, ...]:
        return tuple(numerator / self.denominator for numerator in self.numerators)

    @property
    def row_masses(self) -> tuple[Fraction, ...]:
        return tuple(sum(row, Fraction(0)) for row in self.amplitude)

    @property
    def projected(self) -> tuple[tuple[Fraction, ...], ...]:
        return tuple(
            tuple(row_mass * profile_entry for profile_entry in self.profile)
            for row_mass in self.row_masses
        )

    @property
    def defects(self) -> tuple[tuple[Fraction, ...], ...]:
        return tuple(
            tuple(abs(entry - projected) for entry, projected in zip(row, projection, strict=True))
            for row, projection in zip(self.amplitude, self.projected, strict=True)
        )

    @property
    def maximum_defect(self) -> Fraction:
        return max(defect for row in self.defects for defect in row)

    @property
    def projected_floor(self) -> Fraction:
        return min(entry for row in self.projected for entry in row)

    @property
    def relative_defect(self) -> Fraction:
        return self.maximum_defect / self.projected_floor

    @property
    def pairwise_cross_residuals(
        self,
    ) -> tuple[tuple[tuple[Fraction, ...], ...], ...]:
        """Absolute cleared residuals indexed by source, other, target."""

        return tuple(
            tuple(
                tuple(
                    abs(
                        self.row_masses[other] * self.amplitude[source][target]
                        - self.row_masses[source] * self.amplitude[other][target]
                    )
                    for target in range(self.target_count)
                )
                for other in range(self.source_count)
            )
            for source in range(self.source_count)
        )

    @property
    def maximum_pairwise_cross_residual(self) -> Fraction:
        return max(
            residual
            for source in self.pairwise_cross_residuals
            for other in source
            for residual in other
        )

    @property
    def source_shards(self) -> tuple[tuple[int, ...], ...]:
        """Ordered source partition used by bounded-memory certificates."""

        return tuple(
            tuple(range(start, min(start + self.source_shard_size, self.source_count)))
            for start in range(0, self.source_count, self.source_shard_size)
        )

    @property
    def source_shard_residual_majorants(self) -> tuple[Fraction, ...]:
        """One coordinate-uniform exact residual majorant per source shard."""

        residuals = self.pairwise_cross_residuals
        return tuple(
            max(
                sum(
                    (residuals[source][other][target] for other in shard),
                    Fraction(0),
                )
                for source in range(self.source_count)
                for target in range(self.target_count)
            )
            for shard in self.source_shards
        )

    @property
    def chunked_statistical_budgets(self) -> tuple[tuple[Fraction, ...], ...]:
        """Sum of proved shard majorants plus exact pseudocount bias."""

        shard_sum = sum(self.source_shard_residual_majorants, Fraction(0))
        return tuple(
            tuple(
                (
                    shard_sum
                    + abs(
                        self.pseudocount
                        * (
                            self.target_count * self.amplitude[source][target]
                            - self.row_masses[source]
                        )
                    )
                )
                / self.denominator
                for target in range(self.target_count)
            )
            for source in range(self.source_count)
        )

    @property
    def maximum_chunked_statistical_budget(self) -> Fraction:
        return max(
            budget for row in self.chunked_statistical_budgets for budget in row
        )

    @property
    def chunked_statistical_relative_budget(self) -> Fraction:
        return self.maximum_chunked_statistical_budget / self.projected_floor

    @property
    def exact_statistical_budgets(self) -> tuple[tuple[Fraction, ...], ...]:
        """Exact pairwise-residual sum plus exact pseudocount bias."""

        return tuple(
            tuple(
                (
                    sum(
                        (
                            self.pairwise_cross_residuals[source][other][target]
                            for other in range(self.source_count)
                        ),
                        Fraction(0),
                    )
                    + abs(
                        self.pseudocount
                        * (
                            self.target_count * self.amplitude[source][target]
                            - self.row_masses[source]
                        )
                    )
                )
                / self.denominator
                for target in range(self.target_count)
            )
            for source in range(self.source_count)
        )

    @property
    def maximum_exact_statistical_budget(self) -> Fraction:
        return max(
            budget for row in self.exact_statistical_budgets for budget in row
        )

    @property
    def exact_statistical_relative_budget(self) -> Fraction:
        return self.maximum_exact_statistical_budget / self.projected_floor

    @property
    def hybrid_statistical_budgets(self) -> tuple[tuple[Fraction, ...], ...]:
        """Uniform pairwise bound plus the exact pseudocount bias."""

        pairwise_bound = self.maximum_pairwise_cross_residual
        return tuple(
            tuple(
                (
                    self.source_count * pairwise_bound
                    + abs(
                        self.pseudocount
                        * (
                            self.target_count * self.amplitude[source][target]
                            - self.row_masses[source]
                        )
                    )
                )
                / self.denominator
                for target in range(self.target_count)
            )
            for source in range(self.source_count)
        )

    @property
    def maximum_hybrid_statistical_budget(self) -> Fraction:
        return max(
            budget for row in self.hybrid_statistical_budgets for budget in row
        )

    @property
    def hybrid_statistical_relative_budget(self) -> Fraction:
        return self.maximum_hybrid_statistical_budget / self.projected_floor

    @property
    def statistical_budgets(self) -> tuple[tuple[Fraction, ...], ...]:
        """Cardinality-plus-pseudocount budgets from the Lean theorem."""

        pairwise_bound = self.maximum_pairwise_cross_residual
        return tuple(
            tuple(
                (
                    self.source_count * pairwise_bound
                    + self.pseudocount
                    * (
                        self.target_count * self.amplitude[source][target]
                        + self.row_masses[source]
                    )
                )
                / self.denominator
                for target in range(self.target_count)
            )
            for source in range(self.source_count)
        )

    @property
    def maximum_statistical_budget(self) -> Fraction:
        return max(budget for row in self.statistical_budgets for budget in row)

    @property
    def statistical_relative_budget(self) -> Fraction:
        return self.maximum_statistical_budget / self.projected_floor


@dataclass(frozen=True)
class RegularizedRankOneMatrixPrefixLeanCertificate:
    """A finite prefix of exact canonical rank-one matrix calculations."""

    scales: tuple[RegularizedRankOneScaleCertificate, ...]

    @classmethod
    def from_json(
        cls, payload: dict[str, Any]
    ) -> "RegularizedRankOneMatrixPrefixLeanCertificate":
        if not isinstance(payload, dict):
            raise ValueError("the certificate payload must be a JSON object")
        raw_scales = payload.get("scales")
        if not isinstance(raw_scales, list) or not raw_scales:
            raise ValueError("scales must be a nonempty JSON list")
        certificate = cls(
            scales=tuple(
                RegularizedRankOneScaleCertificate.from_json(item, scale=scale)
                for scale, item in enumerate(raw_scales)
            )
        )
        certificate.to_computed_floor_prefix()
        certificate.to_exact_statistical_computed_floor_prefix()
        certificate.to_chunked_statistical_computed_floor_prefix()
        return certificate

    @property
    def threshold(self) -> int:
        return len(self.scales) - 1

    @property
    def maximum_relative_defect(self) -> Fraction:
        return max(scale.relative_defect for scale in self.scales)

    def to_computed_floor_prefix(self) -> ComputedFloorPrefixLeanCertificate:
        certificate = ComputedFloorPrefixLeanCertificate(
            errors=tuple(scale.maximum_defect for scale in self.scales),
            floors=tuple(scale.projected_floor for scale in self.scales),
        )
        certificate.require_physical_tolerance()
        return certificate


    def to_statistical_computed_floor_prefix(
        self,
    ) -> ComputedFloorPrefixLeanCertificate:
        """Prefix using the proved pairwise-statistical majorant."""

        certificate = ComputedFloorPrefixLeanCertificate(
            errors=tuple(
                scale.maximum_statistical_budget for scale in self.scales
            ),
            floors=tuple(scale.projected_floor for scale in self.scales),
        )
        certificate.require_physical_tolerance()
        return certificate

    def to_exact_statistical_computed_floor_prefix(
        self,
    ) -> ComputedFloorPrefixLeanCertificate:
        """Prefix using the exact residual-and-bias theorem budget."""

        certificate = ComputedFloorPrefixLeanCertificate(
            errors=tuple(
                scale.maximum_exact_statistical_budget for scale in self.scales
            ),
            floors=tuple(scale.projected_floor for scale in self.scales),
        )
        certificate.require_physical_tolerance()
        return certificate

    def to_chunked_statistical_computed_floor_prefix(
        self,
    ) -> ComputedFloorPrefixLeanCertificate:
        """Prefix using independently checkable source-shard majorants."""

        certificate = ComputedFloorPrefixLeanCertificate(
            errors=tuple(
                scale.maximum_chunked_statistical_budget for scale in self.scales
            ),
            floors=tuple(scale.projected_floor for scale in self.scales),
        )
        certificate.require_physical_tolerance()
        return certificate


def _source_shard_coordinate_residual(
    task: tuple[
        int,
        int,
        int,
        int,
        tuple[tuple[Fraction, ...], ...],
        tuple[Fraction, ...],
        tuple[int, ...],
    ]
) -> tuple[int, int, Fraction]:
    """Compute one exact shard/source/target residual in a worker process."""

    scale, shard_index, source, target, amplitude, row_masses, shard = task
    value = sum(
        (
            abs(
                row_masses[other] * amplitude[source][target]
                - row_masses[source] * amplitude[other][target]
            )
            for other in shard
        ),
        Fraction(0),
    )
    return scale, shard_index, value


def validate_regularized_shards_parallel(
    certificate: RegularizedRankOneMatrixPrefixLeanCertificate,
    *,
    jobs: int,
    require_parallel: bool = False,
) -> tuple[tuple[Fraction, ...], ...]:
    """Recompute proposed shard majorants with a deterministic process pool.

    This speeds up certificate production only.  The returned rationals remain
    untrusted until the emitted Lean shard theorems compile.
    """

    if jobs <= 0:
        raise ValueError("jobs must be positive")
    tasks = [
        (
            scale_index,
            shard_index,
            source,
            target,
            scale.amplitude,
            scale.row_masses,
            shard,
        )
        for scale_index, scale in enumerate(certificate.scales)
        for shard_index, shard in enumerate(scale.source_shards)
        for source in range(scale.source_count)
        for target in range(scale.target_count)
    ]
    worker_count = min(jobs, len(tasks))
    if worker_count == 1:
        results = map(_source_shard_coordinate_residual, tasks)
    else:
        try:
            with ProcessPoolExecutor(max_workers=worker_count) as executor:
                results = tuple(
                    executor.map(_source_shard_coordinate_residual, tasks)
                )
        except (NotImplementedError, PermissionError) as error:
            if require_parallel:
                raise RuntimeError(
                    "parallel shard workers are unavailable in this environment"
                ) from error
            results = map(_source_shard_coordinate_residual, tasks)

    observed = [
        [Fraction(0) for _shard in scale.source_shards]
        for scale in certificate.scales
    ]
    for scale_index, shard_index, value in results:
        observed[scale_index][shard_index] = max(
            observed[scale_index][shard_index], value
        )
    packed = tuple(tuple(scale) for scale in observed)
    expected = tuple(
        scale.source_shard_residual_majorants for scale in certificate.scales
    )
    if packed != expected:
        raise RuntimeError("parallel shard recomputation disagrees with serial result")
    return packed


DEMO_PAYLOAD: dict[str, Any] = {
    "kernel": [["21/2", "19/10"], ["57/4", "63/20"]],
    "source_profile": ["2", "3"],
    "target_profile": ["5", "1"],
    "terminal": ["7", "11"],
}

PREFIX_DEMO_PAYLOAD: dict[str, Any] = {
    "prefix_errors": ["1/32", "1/20", "1/16"],
}

COMPUTED_FLOOR_PREFIX_DEMO_PAYLOAD: dict[str, Any] = {
    "prefix_error_majorants": ["1/8192", "3/16384", "1/2048"],
    "prefix_floors": ["1/2", "3/4", "1"],
}

REGULARIZED_RANK_ONE_PREFIX_DEMO_PAYLOAD: dict[str, Any] = {
    "scales": [
        {
            "amplitude": [["4096", "4096"], ["8192", "8192"]],
            "pseudocount": "1",
        },
        {
            "amplitude": [["4097", "4096"]],
            "pseudocount": "1",
        },
        {
            "amplitude": [["8192", "8191"], ["4096", "4095"]],
            "pseudocount": "1",
        },
    ]
}


def _lean_identifier(name: str) -> str:
    if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", name):
        raise ValueError(f"not a safe Lean identifier: {name!r}")
    return name


def _lean_q(value: Fraction) -> str:
    if value <= 0:
        raise ValueError("the current emitter accepts only positive rationals")
    return f"Q'.mkPos {value.numerator} {value.denominator} (by decide)"


def _lean_q_nonnegative(value: Fraction) -> str:
    if value < 0:
        raise ValueError("relative errors must be nonnegative")
    if value == 0:
        return "(0 : Q')"
    return _lean_q(value)


def _lean_fin_function(
    name: str,
    domain_size: int,
    values: tuple[Fraction, ...],
) -> str:
    lines = [f"def {name} (index : Fin {domain_size}) : Q' :=", "  match index.val with"]
    lines.extend(f"  | {index} => {_lean_q(value)}" for index, value in enumerate(values))
    lines.append("  | _ => 0")
    return "\n".join(lines)


def _lean_fin_matrix(
    name: str,
    matrix: tuple[tuple[Fraction, ...], ...],
) -> str:
    height = len(matrix)
    width = len(matrix[0])
    lines = [
        f"def {name} (source : Fin {height}) (target : Fin {width}) : Q' :=",
        "  match source.val, target.val with",
    ]
    for row, values in enumerate(matrix):
        lines.extend(
            f"  | {row}, {column} => {_lean_q(value)}"
            for column, value in enumerate(values)
        )
    lines.append("  | _, _ => 0")
    return "\n".join(lines)


def _lean_fin_nonnegative_matrix(
    name: str,
    matrix: tuple[tuple[Fraction, ...], ...],
) -> str:
    height = len(matrix)
    width = len(matrix[0])
    lines = [
        f"def {name} (source : Fin {height}) (target : Fin {width}) : Q' :=",
        "  match source.val, target.val with",
    ]
    for row, values in enumerate(matrix):
        lines.extend(
            f"  | {row}, {column} => {_lean_q_nonnegative(value)}"
            for column, value in enumerate(values)
        )
    lines.append("  | _, _ => 0")
    return "\n".join(lines)


def emit_lean(
    certificate: RelativeRankOneLeanCertificate,
    *,
    name: str = "boundaryMessagePilot",
    namespace: str = "YMGap.Continuum.GeneratedBoundaryMessageCertificate",
) -> str:
    """Return a self-contained Lean module body for the exact certificate."""

    name = _lean_identifier(name)
    namespace_parts = namespace.split(".")
    if not namespace_parts or any(
        _lean_identifier(part) != part for part in namespace_parts
    ):
        raise ValueError(f"not a safe Lean namespace: {namespace!r}")
    source_count = len(certificate.source_profile)
    target_count = len(certificate.target_profile)
    source_values = ", ".join(str(index) for index in range(source_count))
    target_values = ", ".join(str(index) for index in range(target_count))
    kernel_name = f"{name}Kernel"
    source_name = f"{name}SourceProfile"
    target_name = f"{name}TargetProfile"
    terminal_name = f"{name}Terminal"
    sources_name = f"{name}Sources"
    targets_name = f"{name}Targets"
    witness_name = f"{name}Witness"
    terminal_pos_name = f"{name}Terminal_pos"
    denominator_pos_name = f"{name}Denominator_pos"
    refresh_name = f"{name}Refresh"
    rate_name = f"{name}Refresh_rate_le_quarter"
    maximum = certificate.maximum_relative_error

    sections = [
        "/- Generated certificate data.  The generator is untrusted; Lean checks this file. -/",
        "import YMGap.Continuum.BF4BoundaryMessageRelativeRankOneQuarter",
        "",
        f"namespace {namespace}",
        "",
        "open YMGap.Constructive",
        "open YMGap.Continuum.BF4BoundaryMessageProjectiveRefresh",
        "open YMGap.Continuum.BF4BoundaryMessageRelativeRankOneQuarter",
        "open YMGap.Continuum.BF4ConditionalCarrierLumpabilityFence",
        "open YMGap.Continuum.ConstructiveRefreshContraction",
        "",
        f"-- Generator-side maximum relative error: {maximum}",
        f"def {sources_name} : List (Fin {source_count}) := [{source_values}]",
        f"def {targets_name} : List (Fin {target_count}) := [{target_values}]",
        "",
        _lean_fin_matrix(kernel_name, certificate.kernel),
        "",
        _lean_fin_function(source_name, source_count, certificate.source_profile),
        "",
        _lean_fin_function(target_name, target_count, certificate.target_profile),
        "",
        _lean_fin_function(terminal_name, target_count, certificate.terminal),
        "",
        f"def {witness_name} :",
        "    FiniteRelativeRankOneQuarterWitness",
        f"      {kernel_name} {sources_name} {targets_name} where",
        f"  sourceProfile := {source_name}",
        f"  targetProfile := {target_name}",
        "  sourceProfile_pos := by decide",
        "  targetProfile_pos := by decide",
        "  relative_error := by decide",
        "",
        f"theorem {terminal_pos_name} :",
        f"    ∀ target, target ∈ {targets_name} →",
        f"      (0 : Q') < {terminal_name} target := by",
        "  decide",
        "",
        f"theorem {denominator_pos_name} :",
        "    ∀ source,",
        "      (0 : Q') < terminalWeightedDenominator",
        f"        {targets_name} {kernel_name} {terminal_name} source := by",
        "  decide",
        "",
        f"def {refresh_name} :",
        f"    FiniteRefreshCertificate {sources_name} {targets_name} :=",
        "  terminalProjectiveRefreshCertificate",
        f"    {witness_name}.toCrossRatioCertificate",
        f"    {terminal_name} {terminal_pos_name} {denominator_pos_name}",
        f"    {witness_name}.commonMass_lt_one",
        "    0 (by decide)",
        "",
        f"theorem {rate_name} :",
        f"    {refresh_name}.rate ≤ quarterRate := by",
        "  exact terminalProjectiveRefresh_rate_le_quarter",
        f"    {witness_name}.toCrossRatioCertificate",
        f"    {terminal_name} {terminal_pos_name} {denominator_pos_name}",
        f"    {witness_name}.commonMass_lt_one",
        "    0 (by decide)",
        "    relativeRankOneSpread_square_le_fourThirds",
        "",
        f"end {namespace}",
        "",
        f"#print axioms {namespace}.{rate_name}",
        "",
    ]
    return "\n".join(sections)


def emit_prefix_tail_lean(
    certificate: QuarterErrorPrefixLeanCertificate,
    *,
    name: str = "boundaryMessagePrefix",
    namespace: str = "YMGap.Continuum.GeneratedBoundaryMessagePrefixCertificate",
) -> str:
    """Emit a checked finite-prefix adapter with an explicit analytic tail input."""

    name = _lean_identifier(name)
    namespace_parts = namespace.split(".")
    if not namespace_parts or any(
        _lean_identifier(part) != part for part in namespace_parts
    ):
        raise ValueError(f"not a safe Lean namespace: {namespace!r}")

    threshold = certificate.threshold
    exact_names = [f"{name}Stage{stage}_exact" for stage in range(threshold + 1)]
    parameters = [
        "    (error : Nat -> Q')",
        *(
            f"    ({exact_name} : error {stage} ≈ {_lean_q_nonnegative(value)})"
            for stage, (exact_name, value) in enumerate(
                zip(exact_names, certificate.errors, strict=True)
            )
        ),
        "    (tail_step : forall stage : Nat,",
        f"      {threshold} <= stage -> error (stage + 1) <= error stage)",
    ]

    prefix_proof = ["  prefix_bound := by", "    intro stage hstage"]
    if threshold == 0:
        prefix_proof.append("    omega")
    else:
        cases = " ∨ ".join(f"stage = {stage}" for stage in range(threshold))
        alternatives = " | ".join("rfl" for _ in range(threshold))
        prefix_proof.extend(
            [
                f"    have hcases : {cases} := by omega",
                f"    rcases hcases with {alternatives}",
            ]
        )
        for exact_name in exact_names[:threshold]:
            prefix_proof.extend(
                [
                    "    · exact Q'.le_trans' _ _ _",
                    f"        (Q'.le_of_eqv {exact_name}) (by decide)",
                ]
            )

    call_arguments = " ".join(exact_names + ["tail_step"])
    sections = [
        "/- Generated finite-prefix data.  The generator is untrusted; Lean checks this file. -/",
        "import YMGap.Continuum.BF4BoundaryMessagePrefixTailQuarter",
        "",
        f"namespace {namespace}",
        "",
        "open YMGap.Constructive",
        "open YMGap.Continuum.BF4BoundaryMessageRelativeRankOneQuarter",
        "open YMGap.Continuum.BF4BoundaryMessagePrefixTailQuarter",
        "",
        'local infix:50 " ≈ " => Q\'.eqv',
        "",
        f"-- Generator-side threshold: {threshold}",
        f"-- Generator-side maximum prefix error: {certificate.maximum_error}",
        f"def {name}Budget",
        *parameters,
        f"    : QuarterErrorPrefixTail error where",
        f"  threshold := {threshold}",
        *prefix_proof,
        "  threshold_bound := by",
        "    exact Q'.le_trans' _ _ _",
        f"      (Q'.le_of_eqv {exact_names[-1]}) (by decide)",
        "  tail_step := tail_step",
        "",
        f"theorem {name}AllStages_le",
        *parameters,
        "    : forall stage : Nat,",
        "      error stage <= relativeRankOneTolerance := by",
        "  intro stage",
        f"  exact ({name}Budget error {call_arguments}).bound_all stage",
        "",
        f"end {namespace}",
        "",
        f"#print axioms {namespace}.{name}Budget",
        f"#print axioms {namespace}.{name}AllStages_le",
        "",
    ]
    return "\n".join(sections)


def emit_computed_floor_prefix_lean(
    certificate: ComputedFloorPrefixLeanCertificate,
    *,
    name: str = "boundaryMessageFloorPrefix",
    namespace: str = "YMGap.Continuum.GeneratedBoundaryMessageFloorPrefixCertificate",
) -> str:
    """Emit checked error/floor prefix data plus an explicit cross-tail input."""

    name = _lean_identifier(name)
    namespace_parts = namespace.split(".")
    if not namespace_parts or any(
        _lean_identifier(part) != part for part in namespace_parts
    ):
        raise ValueError(f"not a safe Lean namespace: {namespace!r}")

    threshold = certificate.threshold
    error_exact_names = [f"{name}ErrorStage{stage}_exact" for stage in range(threshold + 1)]
    floor_exact_names = [f"{name}FloorStage{stage}_exact" for stage in range(threshold + 1)]
    exact_parameters: list[str] = []
    call_exact_names: list[str] = []
    for stage, (error, floor, error_name, floor_name) in enumerate(
        zip(
            certificate.errors,
            certificate.floors,
            error_exact_names,
            floor_exact_names,
            strict=True,
        )
    ):
        exact_parameters.extend(
            [
                f"    ({error_name} : error {stage} ≈ {_lean_q_nonnegative(error)})",
                f"    ({floor_name} : floor {stage} ≈ {_lean_q(floor)})",
            ]
        )
        call_exact_names.extend([error_name, floor_name])

    parameters = [
        "    (error floor : Nat -> Q')",
        *exact_parameters,
        "    (floor_pos : forall stage, (0 : Q') < floor stage)",
        "    (tail_cross : forall stage : Nat,",
        f"      {threshold} <= stage ->",
        "        error (stage + 1) * floor stage <=",
        "          error stage * floor (stage + 1))",
    ]

    def bound_proof(stage: int, indent: str) -> list[str]:
        return [
            f"{indent}exact Q'.le_trans' _ _ _",
            f"{indent}  (Q'.le_of_eqv {error_exact_names[stage]})",
            f"{indent}  (Q'.le_trans' _ _ _",
            f"{indent}    (by decide)",
            f"{indent}    (Q'.ge_of_eqv",
            f"{indent}      (Q'.mul_eqv_congr_left",
            f"{indent}        physicalRelativeErrorTolerance _ _",
            f"{indent}        {floor_exact_names[stage]})))",
        ]

    prefix_proof = ["  prefix_bound := by", "    intro stage hstage"]
    if threshold == 0:
        prefix_proof.append("    omega")
    else:
        cases = " ∨ ".join(f"stage = {stage}" for stage in range(threshold))
        alternatives = " | ".join("rfl" for _ in range(threshold))
        prefix_proof.extend(
            [
                f"    have hcases : {cases} := by omega",
                f"    rcases hcases with {alternatives}",
            ]
        )
        for stage in range(threshold):
            prefix_proof.append("    ·")
            prefix_proof.extend(bound_proof(stage, "      "))

    call_arguments = " ".join(call_exact_names + ["floor_pos", "tail_cross"])
    sections = [
        "/- Generated computed-floor prefix data.  The generator is untrusted; Lean checks this file. -/",
        "import YMGap.Continuum.BF4BoundaryMessageComputedFloorCrossTail",
        "",
        f"namespace {namespace}",
        "",
        "open YMGap.Constructive",
        "open YMGap.Continuum.BF4BoundaryMessageComputedFloorCrossTail",
        "open YMGap.Continuum.BF4PhysicalHalfAmplitudeRelativeTerminalPerturbation",
        "",
        'local infix:50 " ≈ " => Q\'.eqv',
        "",
        f"-- Generator-side threshold: {threshold}",
        f"-- Generator-side maximum error/floor ratio: {certificate.maximum_relative_error}",
        f"def {name}Budget",
        *parameters,
        "    : PositiveFloorErrorCrossTail",
        "        error floor physicalRelativeErrorTolerance where",
        f"  threshold := {threshold}",
        "  floor_pos := floor_pos",
        *prefix_proof,
        "  threshold_bound := by",
        *bound_proof(threshold, "    "),
        "  tail_cross := tail_cross",
        "",
        f"theorem {name}AllStages_le",
        *parameters,
        "    : forall stage : Nat,",
        "      error stage <= physicalRelativeErrorTolerance * floor stage := by",
        "  intro stage",
        f"  exact ({name}Budget error floor {call_arguments})",
        "    |>.error_le_tolerance_mul_floor stage",
        "",
        f"end {namespace}",
        "",
        f"#print axioms {namespace}.{name}Budget",
        f"#print axioms {namespace}.{name}AllStages_le",
        "",
    ]
    return "\n".join(sections)


def emit_regularized_rank_one_prefix_lean(
    certificate: RegularizedRankOneMatrixPrefixLeanCertificate,
    *,
    name: str = "boundaryMessageRegularizedPrefix",
    namespace: str = "YMGap.Continuum.GeneratedBoundaryMessageRegularizedPrefixCertificate",
) -> str:
    """Emit literal matrices plus their checked canonical rank-one prefix data."""

    name = _lean_identifier(name)
    namespace_parts = namespace.split(".")
    if not namespace_parts or any(
        _lean_identifier(part) != part for part in namespace_parts
    ):
        raise ValueError(f"not a safe Lean namespace: {namespace!r}")

    floor_certificate = certificate.to_exact_statistical_computed_floor_prefix()
    floor_certificate.require_physical_tolerance()
    adapter = emit_computed_floor_prefix_lean(
        floor_certificate,
        name=name,
        namespace=namespace,
    )
    adapter = adapter.replace(
        "import YMGap.Continuum.BF4BoundaryMessageComputedFloorCrossTail",
        "import YMGap.Continuum.BF4BoundaryMessageComputedFloorCrossTail\n"
        "import YMGap.Continuum.FiniteRegularizedRankOneStatistics",
        1,
    )

    sections = [
        adapter.rstrip(),
        "",
        f"namespace {namespace}",
        "",
        "open YMGap.Constructive",
        "open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget",
        "open YMGap.Continuum.FiniteRegularizedRankOneStatistics",
        "open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm",
        "",
        'local infix:50 " ≈ " => Q\'.eqv',
        "",
        "/- Literal finite amplitude matrices.  Each theorem below is checked",
        "by Lean; the external exact-arithmetic run is not part of the proof. -/",
    ]

    for stage, scale in enumerate(certificate.scales):
        stem = f"{name}Scale{stage}"
        sources = f"{stem}Sources"
        targets = f"{stem}Targets"
        amplitude = f"{stem}Amplitude"
        pseudocount = f"{stem}Pseudocount"
        column_mass = f"{stem}ColumnMass"
        numerator = f"{stem}Numerator"
        denominator = f"{stem}Denominator"
        denominator_pos = f"{stem}Denominator_pos"
        finite_denominator_pos = f"{stem}FiniteDenominator_pos"
        profile = f"{stem}Profile"
        row_mass = f"{stem}RowMass"
        projection = f"{stem}Projection"
        error = f"{stem}Error"
        pairwise_bound = f"{stem}PairwiseBound"
        exact_statistical_budget = f"{stem}ExactStatisticalBudget"
        exact_statistical_error = f"{stem}ExactStatisticalError"
        source_chunks = f"{stem}SourceChunks"
        source_chunks_flatten = f"{stem}SourceChunks_flatten"
        chunk_majorant = f"{stem}ChunkMajorant"
        chunked_statistical_budget = f"{stem}ChunkedStatisticalBudget"
        chunked_statistical_error = f"{stem}ChunkedStatisticalError"
        hybrid_statistical_budget = f"{stem}HybridStatisticalBudget"
        hybrid_statistical_error = f"{stem}HybridStatisticalError"
        statistical_budget = f"{stem}StatisticalBudget"
        statistical_error = f"{stem}StatisticalError"
        floor = f"{stem}Floor"
        source_values = ", ".join(str(index) for index in range(scale.source_count))
        target_values = ", ".join(str(index) for index in range(scale.target_count))
        source_shard_names = [
            f"{stem}SourceShard{shard_index}"
            for shard_index in range(len(scale.source_shards))
        ]
        source_shard_definitions: list[str] = []
        for shard_name, shard in zip(
            source_shard_names, scale.source_shards, strict=True
        ):
            shard_values = ", ".join(str(index) for index in shard)
            source_shard_definitions.append(
                f"def {shard_name} : List (Fin {scale.source_count}) := [{shard_values}]"
            )
        chunk_majorant_lines = [
            f"def {chunk_majorant}",
            f"    (chunk : List (Fin {scale.source_count}))",
            f"    (_source : Fin {scale.source_count}) (_target : Fin {scale.target_count}) : Q' :=",
        ]
        for shard_index, (shard_name, shard_bound) in enumerate(
            zip(
                source_shard_names,
                scale.source_shard_residual_majorants,
                strict=True,
            )
        ):
            keyword = "if" if shard_index == 0 else "else if"
            chunk_majorant_lines.append(
                f"  {keyword} chunk = {shard_name} then {_lean_q_nonnegative(shard_bound)}"
            )
        chunk_majorant_lines.append("  else 0")
        sections.extend(
            [
                "",
                f"def {sources} : List (Fin {scale.source_count}) := [{source_values}]",
                f"def {targets} : List (Fin {scale.target_count}) := [{target_values}]",
                *source_shard_definitions,
                f"def {source_chunks} : List (List (Fin {scale.source_count})) :=",
                f"  [{', '.join(source_shard_names)}]",
                f"theorem {source_chunks_flatten} : {source_chunks}.flatten = {sources} := by",
                "  decide",
                f"def {pseudocount} : Q' := {_lean_q(scale.pseudocount)}",
                "",
                _lean_fin_nonnegative_matrix(amplitude, scale.amplitude),
                "",
                f"def {column_mass} (target : Fin {scale.target_count}) : Q' :=",
                f"  listQSum (fun source => {amplitude} source target) {sources}",
                "",
                f"def {numerator} (target : Fin {scale.target_count}) : Q' :=",
                f"  {pseudocount} + {column_mass} target",
                "",
                f"def {denominator} : Q' :=",
                f"  listQSum {numerator} {targets}",
                "",
                f"theorem {denominator_pos} : (0 : Q') < {denominator} := by",
                "  decide",
                "",
                f"theorem {finite_denominator_pos} :",
                "    (0 : Q') < finiteRegularizedDenominator",
                f"      {sources} {targets} {amplitude} {pseudocount} := by",
                "  decide",
                "",
                f"def {profile} (target : Fin {scale.target_count}) : Q' :=",
                f"  Q'.divPos ({numerator} target) {denominator} {denominator_pos}",
                "",
                f"def {row_mass} (source : Fin {scale.source_count}) : Q' :=",
                f"  listQSum ({amplitude} source) {targets}",
                "",
                f"def {projection}",
                f"    (source : Fin {scale.source_count}) (target : Fin {scale.target_count}) : Q' :=",
                f"  {row_mass} source * {profile} target",
                "",
                f"def {error} : Q' := {_lean_q_nonnegative(scale.maximum_defect)}",
                f"def {pairwise_bound} : Q' := "
                f"{_lean_q_nonnegative(scale.maximum_pairwise_cross_residual)}",
                "",
                f"def {exact_statistical_budget}",
                f"    (source : Fin {scale.source_count}) (target : Fin {scale.target_count}) : Q' :=",
                "  Q'.divPos",
                "    (finitePairwiseRowResidualBudget",
                f"        {sources} {targets} {amplitude} source target +",
                "      finitePseudocountBiasBudget",
                f"        {targets} {amplitude} {pseudocount} source target)",
                f"    (finiteRegularizedDenominator {sources} {targets}",
                f"      {amplitude} {pseudocount})",
                f"    {finite_denominator_pos}",
                "",
                f"def {exact_statistical_error} : Q' := "
                f"{_lean_q_nonnegative(scale.maximum_exact_statistical_budget)}",
                "",
                *chunk_majorant_lines,
                "",
                f"def {chunked_statistical_budget}",
                f"    (source : Fin {scale.source_count}) (target : Fin {scale.target_count}) : Q' :=",
                "  Q'.divPos",
                "    (finiteChunkedPairwiseRowResidualMajorant",
                f"        {source_chunks}",
                f"        (fun chunk => {chunk_majorant} chunk source target) +",
                "      finitePseudocountBiasBudget",
                f"        {targets} {amplitude} {pseudocount} source target)",
                f"    (finiteRegularizedDenominator {sources} {targets}",
                f"      {amplitude} {pseudocount})",
                f"    {finite_denominator_pos}",
                "",
                f"def {chunked_statistical_error} : Q' := "
                f"{_lean_q_nonnegative(scale.maximum_chunked_statistical_budget)}",
                "",
                f"def {hybrid_statistical_budget}",
                f"    (source : Fin {scale.source_count}) (target : Fin {scale.target_count}) : Q' :=",
                "  Q'.divPos",
                f"    (Q'.ofNat {sources}.length * {pairwise_bound} +",
                "      finitePseudocountBiasBudget",
                f"        {targets} {amplitude} {pseudocount} source target)",
                f"    (finiteRegularizedDenominator {sources} {targets}",
                f"      {amplitude} {pseudocount})",
                f"    {finite_denominator_pos}",
                "",
                f"def {hybrid_statistical_error} : Q' := "
                f"{_lean_q_nonnegative(scale.maximum_hybrid_statistical_budget)}",
                "",
                f"def {statistical_budget}",
                f"    (source : Fin {scale.source_count}) (target : Fin {scale.target_count}) : Q' :=",
                "  Q'.divPos",
                f"    (Q'.ofNat {sources}.length * {pairwise_bound} +",
                f"      {pseudocount} *",
                f"        (Q'.ofNat {targets}.length * {amplitude} source target +",
                f"          finiteRowMass {targets} {amplitude} source))",
                f"    (finiteRegularizedDenominator {sources} {targets}",
                f"      {amplitude} {pseudocount})",
                f"    {finite_denominator_pos}",
                "",
                f"def {statistical_error} : Q' := "
                f"{_lean_q_nonnegative(scale.maximum_statistical_budget)}",
                f"def {floor} : Q' := {_lean_q(scale.projected_floor)}",
                "",
                f"theorem {stem}Pairwise_le :",
                f"    ∀ source, source ∈ {sources} →",
                f"      ∀ target, target ∈ {targets} →",
                f"        ∀ other, other ∈ {sources} →",
                "          Q'.abs (finitePairwiseRowCrossTerm",
                f"            {targets} {amplitude} source other target) ≤",
                f"              {pairwise_bound} := by",
                "  decide",
                "",
                f"theorem {stem}StatisticalBudget_le :",
                f"    ∀ source, source ∈ {sources} →",
                f"      ∀ target, target ∈ {targets} →",
                f"        {statistical_budget} source target ≤",
                f"          {statistical_error} := by",
                "  decide",
                "",
                f"theorem {stem}ExactStatisticalBudget_le :",
                f"    ∀ source, source ∈ {sources} →",
                f"      ∀ target, target ∈ {targets} →",
                f"        {exact_statistical_budget} source target ≤",
                f"          {exact_statistical_error} := by",
                "  decide",
                "",
                f"theorem {stem}ChunkBound :",
                f"    ∀ source, source ∈ {sources} →",
                f"      ∀ target, target ∈ {targets} →",
                f"        ∀ chunk, chunk ∈ {source_chunks} →",
                "          finitePairwiseRowResidualBudget",
                f"              chunk {targets} {amplitude} source target ≤",
                f"            {chunk_majorant} chunk source target := by",
                "  decide",
                "",
                f"theorem {stem}ChunkedStatisticalBudget_le :",
                f"    ∀ source, source ∈ {sources} →",
                f"      ∀ target, target ∈ {targets} →",
                f"        {chunked_statistical_budget} source target ≤",
                f"          {chunked_statistical_error} := by",
                "  decide",
                "",
                f"theorem {stem}HybridStatisticalBudget_le :",
                f"    ∀ source, source ∈ {sources} →",
                f"      ∀ target, target ∈ {targets} →",
                f"        {hybrid_statistical_budget} source target ≤",
                f"          {hybrid_statistical_error} := by",
                "  decide",
                "",
                f"theorem {stem}GenericDefect_le_hybridStatisticalError :",
                f"    ∀ source, source ∈ {sources} →",
                f"      ∀ target, target ∈ {targets} →",
                "        finiteRegularizedRankOneDefect",
                f"            {sources} {targets} {amplitude} {pseudocount}",
                f"            {finite_denominator_pos} source target ≤",
                f"          {hybrid_statistical_error} := by",
                "  intro source source_mem target target_mem",
                "  exact Q'.le_trans' _ _ _",
                "    (finiteRegularizedRankOneDefect_le_of_pairwise_exactBias",
                f"      {sources} {targets} {amplitude} {pseudocount}",
                f"      {finite_denominator_pos}",
                f"      {pairwise_bound} (by decide)",
                "      source target",
                "      (by",
                "        intro other other_mem",
                f"        exact {stem}Pairwise_le source source_mem target",
                "          target_mem other other_mem))",
                f"    ({stem}HybridStatisticalBudget_le",
                "      source source_mem target target_mem)",
                "",
                f"theorem {stem}GenericDefect_le_chunkedStatisticalError :",
                f"    ∀ source, source ∈ {sources} →",
                f"      ∀ target, target ∈ {targets} →",
                "        finiteRegularizedRankOneDefect",
                f"            {sources} {targets} {amplitude} {pseudocount}",
                f"            {finite_denominator_pos} source target ≤",
                f"          {chunked_statistical_error} := by",
                "  intro source source_mem target target_mem",
                "  exact Q'.le_trans' _ _ _",
                "    (finiteRegularizedRankOneDefect_le_chunkedMajorant_of_flatten_eq",
                f"      {sources} {source_chunks} {source_chunks_flatten}",
                f"      {targets} {amplitude} {pseudocount}",
                f"      {finite_denominator_pos}",
                f"      (fun chunk => {chunk_majorant} chunk source target)",
                "      source target",
                "      (by",
                "        intro chunk chunk_mem",
                f"        exact {stem}ChunkBound source source_mem target",
                "          target_mem chunk chunk_mem))",
                f"    ({stem}ChunkedStatisticalBudget_le",
                "      source source_mem target target_mem)",
                "",
                f"theorem {stem}GenericDefect_le_exactStatisticalError :",
                f"    ∀ source, source ∈ {sources} →",
                f"      ∀ target, target ∈ {targets} →",
                "        finiteRegularizedRankOneDefect",
                f"            {sources} {targets} {amplitude} {pseudocount}",
                f"            {finite_denominator_pos} source target ≤",
                f"          {exact_statistical_error} := by",
                "  intro source source_mem target target_mem",
                "  exact Q'.le_trans' _ _ _",
                "    (finiteRegularizedRankOneDefect_le_divPos_budget",
                f"      {sources} {targets} {amplitude} {pseudocount}",
                f"      {finite_denominator_pos} source target)",
                f"    ({stem}ExactStatisticalBudget_le",
                "      source source_mem target target_mem)",
                "",
                f"theorem {stem}GenericDefect_le_statisticalError :",
                f"    ∀ source, source ∈ {sources} →",
                f"      ∀ target, target ∈ {targets} →",
                "        finiteRegularizedRankOneDefect",
                f"            {sources} {targets} {amplitude} {pseudocount}",
                f"            {finite_denominator_pos} source target ≤",
                f"          {statistical_error} := by",
                "  intro source source_mem target target_mem",
                "  exact Q'.le_trans' _ _ _",
                "    (finiteRegularizedRankOneDefect_le_of_pairwise",
                f"      {sources} {targets} {amplitude}",
                "      (by decide)",
                f"      {finite_denominator_pos}",
                "      (by intro source' target' target'_mem; decide +revert)",
                f"      {pairwise_bound} (by decide)",
                "      source target target_mem",
                "      (by",
                "        intro other other_mem",
                f"        exact {stem}Pairwise_le source source_mem target",
                "          target_mem other other_mem))",
                f"    ({stem}StatisticalBudget_le source source_mem target target_mem)",
                "",
                f"theorem {stem}Defect_le :",
                f"    ∀ source, source ∈ {sources} →",
                f"      ∀ target, target ∈ {targets} →",
                f"        Q'.abs ({amplitude} source target +",
                f"          -{projection} source target) ≤ {error} := by",
                "  decide",
                "",
                f"theorem {stem}Floor_le :",
                f"    ∀ source, source ∈ {sources} →",
                f"      ∀ target, target ∈ {targets} →",
                f"        {floor} ≤ {projection} source target := by",
                "  decide",
            ]
        )

    sections.extend(
        [
            "",
            f"end {namespace}",
            "",
            *(
                f"#print axioms {namespace}.{name}Scale{stage}Pairwise_le\n"
                f"#print axioms {namespace}.{name}Scale{stage}GenericDefect_le_exactStatisticalError\n"
                f"#print axioms {namespace}.{name}Scale{stage}GenericDefect_le_chunkedStatisticalError\n"
                f"#print axioms {namespace}.{name}Scale{stage}GenericDefect_le_hybridStatisticalError\n"
                f"#print axioms {namespace}.{name}Scale{stage}GenericDefect_le_statisticalError\n"
                f"#print axioms {namespace}.{name}Scale{stage}Defect_le\n"
                f"#print axioms {namespace}.{name}Scale{stage}Floor_le"
                for stage in range(len(certificate.scales))
            ),
            "",
        ]
    )
    return "\n".join(sections)


def _load_payload(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ValueError(f"could not read certificate JSON {path}: {error}") from error
    if not isinstance(payload, dict):
        raise ValueError("the certificate JSON root must be an object")
    return payload


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--demo", action="store_true", help="emit the built-in exact example")
    source.add_argument("--input", type=Path, help="read exact rational certificate JSON")
    source.add_argument(
        "--prefix-demo",
        action="store_true",
        help="emit the built-in finite-prefix/tail adapter",
    )
    source.add_argument(
        "--prefix-input",
        type=Path,
        help="read finite exact prefix-error JSON",
    )
    source.add_argument(
        "--floor-prefix-demo",
        action="store_true",
        help="emit the built-in computed-floor finite-prefix/cross-tail adapter",
    )
    source.add_argument(
        "--floor-prefix-input",
        type=Path,
        help="read finite exact error-majorant and ideal-floor prefix JSON",
    )
    source.add_argument(
        "--regularized-prefix-demo",
        action="store_true",
        help="derive checked prefix data from built-in exact amplitude matrices",
    )
    source.add_argument(
        "--regularized-prefix-input",
        type=Path,
        help="derive checked prefix data from exact amplitude-matrix JSON",
    )
    parser.add_argument("--name", default="boundaryMessagePilot", help="Lean declaration prefix")
    parser.add_argument(
        "--jobs",
        type=int,
        default=max(1, os.cpu_count() or 1),
        help="worker processes for regularized source-shard recomputation",
    )
    parser.add_argument(
        "--require-parallel",
        action="store_true",
        help="fail instead of falling back when process workers are unavailable",
    )
    parser.add_argument(
        "--namespace",
        default="YMGap.Continuum.GeneratedBoundaryMessageCertificate",
        help="Lean namespace for emitted declarations",
    )
    arguments = parser.parse_args()
    if (
        arguments.regularized_prefix_demo
        or arguments.regularized_prefix_input is not None
    ):
        payload = (
            REGULARIZED_RANK_ONE_PREFIX_DEMO_PAYLOAD
            if arguments.regularized_prefix_demo
            else _load_payload(arguments.regularized_prefix_input)
        )
        certificate = RegularizedRankOneMatrixPrefixLeanCertificate.from_json(payload)
        validate_regularized_shards_parallel(
            certificate,
            jobs=arguments.jobs,
            require_parallel=arguments.require_parallel,
        )
        print(
            emit_regularized_rank_one_prefix_lean(
                certificate, name=arguments.name, namespace=arguments.namespace
            ),
            end="",
        )
    elif arguments.floor_prefix_demo or arguments.floor_prefix_input is not None:
        payload = (
            COMPUTED_FLOOR_PREFIX_DEMO_PAYLOAD
            if arguments.floor_prefix_demo
            else _load_payload(arguments.floor_prefix_input)
        )
        certificate = ComputedFloorPrefixLeanCertificate.from_json(payload)
        print(
            emit_computed_floor_prefix_lean(
                certificate, name=arguments.name, namespace=arguments.namespace
            ),
            end="",
        )
    elif arguments.prefix_demo or arguments.prefix_input is not None:
        payload = (
            PREFIX_DEMO_PAYLOAD
            if arguments.prefix_demo
            else _load_payload(arguments.prefix_input)
        )
        certificate = QuarterErrorPrefixLeanCertificate.from_json(payload)
        print(
            emit_prefix_tail_lean(
                certificate, name=arguments.name, namespace=arguments.namespace
            ),
            end="",
        )
    else:
        payload = DEMO_PAYLOAD if arguments.demo else _load_payload(arguments.input)
        certificate = RelativeRankOneLeanCertificate.from_json(payload)
        print(emit_lean(certificate, name=arguments.name, namespace=arguments.namespace), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
