"""Cocircuit-inequality scout for the BF4 binary-multicover route.

Every even binary sheet meets every GF(2) coboundary in an even number of
faces.  Hence a multicover label vector ``x`` must obey

    x[e] <= sum(x[f] for f in cut - {e})

for every face ``e`` in every binary coboundary ``cut``.  Positive local
SU(2) link multiplicity imposes the same inequality only for the elementary
link stars, together with even total spin at each link.

This script samples XORs of actual corrected-slab link stars and asks an
exact-integrality MILP whether the local SU(2) constraints permit a violation
of the resulting global cut inequality.  A candidate is rechecked using the
exact Python integer routines and the complete binary-cycle span at extent
one.  It is a scout, not a proof; any witness used by the formal development
must be transcribed and verified in Lean.
"""

from __future__ import annotations

import random
from dataclasses import dataclass

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp

from computations.bf4_binary_multicover_normality import (
    has_binary_multicover,
    locally_admissible,
    slab_incidence,
)
from computations.dual_half_time_reflection_route import (
    boundary_complete_slab_plaquettes,
)
from computations.dual_positivity_geometry_bridge import Link4, Plaquette4

PINNED_NONZERO_FACES: tuple[Plaquette4, ...] = (
    ((0, 0, 0, 0), (0, 1)),
    ((0, 0, 0, 0), (0, 2)),
    ((0, 0, 0, 0), (1, 3)),
    ((0, 0, 0, 0), (2, 3)),
    ((0, 0, 0, 1), (0, 1)),
    ((0, 0, 0, 1), (0, 2)),
    ((0, 0, 1, 0), (0, 1)),
    ((0, 0, 1, 0), (1, 3)),
    ((0, 0, 1, 1), (0, 1)),
    ((0, 1, 0, 0), (0, 2)),
    ((0, 1, 0, 0), (2, 3)),
    ((0, 1, 0, 1), (0, 2)),
    ((1, 0, 0, 0), (1, 2)),
    ((1, 0, 0, 0), (1, 3)),
    ((1, 0, 0, 0), (2, 3)),
    ((1, 0, 1, 0), (1, 3)),
    ((1, 1, 0, 0), (2, 3)),
)

PINNED_CUT_LINKS: tuple[Link4, ...] = (
    ((0, 1, 0, 0), 2),
    ((0, 1, 0, 1), 2),
    ((1, 1, 0, 0), 2),
    ((1, 1, 0, 1), 2),
)

PINNED_DISTINGUISHED_FACE: Plaquette4 = (
    (1, 0, 0, 0),
    (1, 2),
)


def gf2_rank(rows: tuple[int, ...]) -> int:
    """Rank of bit-packed rows over GF(2)."""

    pivots: dict[int, int] = {}
    for source in rows:
        row = source
        while row:
            pivot = row.bit_length() - 1
            if pivot in pivots:
                row ^= pivots[pivot]
            else:
                pivots[pivot] = row
                break
    return len(pivots)


def gf2_kernel_basis(
    rows: tuple[int, ...], column_count: int
) -> tuple[int, ...]:
    """Bit-packed basis of the nullspace of ``rows`` over GF(2)."""

    pivots: dict[int, int] = {}
    for source in rows:
        row = source
        while row:
            pivot = row.bit_length() - 1
            if pivot in pivots:
                row ^= pivots[pivot]
            else:
                pivots[pivot] = row
                break

    basis: list[int] = []
    for free in range(column_count):
        if free in pivots:
            continue
        vector = 1 << free
        for pivot in sorted(pivots):
            if (pivots[pivot] & vector).bit_count() % 2:
                vector |= 1 << pivot
        if any((row & vector).bit_count() % 2 for row in rows):
            raise AssertionError("GF(2) kernel construction drifted")
        basis.append(vector)
    return tuple(basis)


def all_kernel_masks(
    rows: tuple[int, ...], column_count: int
) -> tuple[int, ...]:
    """All nonzero nullspace vectors, when the nullity is scout-sized."""

    masks = [0]
    for basis_vector in gf2_kernel_basis(rows, column_count):
        masks += [mask ^ basis_vector for mask in masks]
    return tuple(sorted(masks[1:]))


def link_star_masks(
    support: tuple[Plaquette4, ...],
    incidence: dict[Link4, tuple[Plaquette4, ...]],
) -> tuple[int, ...]:
    """Nonzero actual link-star rows on the displayed face support."""

    face_index = {face: index for index, face in enumerate(support)}
    return tuple(
        mask
        for incident in incidence.values()
        if (
            mask := sum(
                1 << face_index[face]
                for face in incident
                if face in face_index
            )
        )
    )


@dataclass(frozen=True)
class CocircuitViolation:
    extent: int
    support: tuple[Plaquette4, ...]
    labels: tuple[int, ...]
    cut_mask: int
    distinguished_face: int
    sheet_masks: tuple[int, ...]

    def cut_defect(self) -> int:
        return self.labels[self.distinguished_face] - sum(
            label
            for index, label in enumerate(self.labels)
            if index != self.distinguished_face
            and self.cut_mask & (1 << index)
        )

    def validates(self) -> bool:
        incidence = slab_incidence(self.extent)
        stars = link_star_masks(self.support, incidence)
        in_row_span = all(
            (sheet & self.cut_mask).bit_count() % 2 == 0
            for sheet in self.sheet_masks
        )
        return (
            self.cut_defect() > 0
            and locally_admissible(
                self.support, self.labels, incidence
            )
            and in_row_span
            and not has_binary_multicover(
                self.labels, self.sheet_masks
            )
            and self.sheet_masks
            == all_kernel_masks(stars, len(self.support))
            and self.cut_mask != 0
            and bool(stars)
        )


def locally_admissible_milp(
    support: tuple[Plaquette4, ...],
    incidence: dict[Link4, tuple[Plaquette4, ...]],
    cutoff: int,
    objective: np.ndarray,
) -> tuple[int, ...] | None:
    """Minimize a face objective under exact local SU(2) constraints."""

    face_index = {face: index for index, face in enumerate(support)}
    incident_indices = tuple(
        tuple(
            face_index[face]
            for face in incident
            if face in face_index
        )
        for incident in incidence.values()
    )
    incident_indices = tuple(row for row in incident_indices if row)
    face_count = len(support)
    link_count = len(incident_indices)
    variable_count = face_count + link_count

    lower_rows: list[float] = []
    upper_rows: list[float] = []
    matrix_rows: list[np.ndarray] = []

    for link_index, incident in enumerate(incident_indices):
        parity = np.zeros(variable_count, dtype=float)
        parity[list(incident)] = 1.0
        parity[face_count + link_index] = -2.0
        matrix_rows.append(parity)
        lower_rows.append(0.0)
        upper_rows.append(0.0)

        for face in incident:
            polygon = np.zeros(variable_count, dtype=float)
            polygon[face] = 1.0
            for other in incident:
                if other != face:
                    polygon[other] -= 1.0
            matrix_rows.append(polygon)
            lower_rows.append(-np.inf)
            upper_rows.append(0.0)

    full_objective = np.zeros(variable_count, dtype=float)
    full_objective[:face_count] = objective
    result = milp(
        c=full_objective,
        integrality=np.ones(variable_count, dtype=int),
        bounds=Bounds(
            np.zeros(variable_count, dtype=float),
            np.concatenate(
                (
                    np.full(face_count, cutoff, dtype=float),
                    np.full(link_count, 3 * cutoff, dtype=float),
                )
            ),
        ),
        constraints=LinearConstraint(
            np.stack(matrix_rows),
            np.array(lower_rows, dtype=float),
            np.array(upper_rows, dtype=float),
        ),
        options={"time_limit": 10.0},
    )
    if not result.success or result.x is None:
        return None
    labels = tuple(int(round(value)) for value in result.x[:face_count])
    if not locally_admissible(support, labels, incidence):
        raise AssertionError("MILP candidate failed exact local validation")
    return labels


def search_cocircuit_violations(
    extent: int = 1,
    cutoff: int = 3,
    samples: int = 500,
    seed: int = 20260728,
) -> CocircuitViolation | None:
    """Sample global coboundaries and optimize their inequality defects."""

    support = tuple(boundary_complete_slab_plaquettes(extent))
    incidence = slab_incidence(extent)
    stars = link_star_masks(support, incidence)
    sheets = all_kernel_masks(stars, len(support))
    nullity = len(support) - gf2_rank(stars)
    if len(sheets) != (1 << nullity) - 1:
        raise ValueError(
            "full cycle enumeration is too large or incomplete; "
            f"got {len(sheets)} sheets at nullity {nullity}"
        )

    generator = random.Random(seed)
    seen: set[int] = set()
    for _ in range(samples):
        cut = 0
        for star in generator.sample(
            stars, generator.randint(2, min(12, len(stars)))
        ):
            cut ^= star
        if cut == 0 or cut in seen:
            continue
        seen.add(cut)
        cut_faces = tuple(
            index
            for index in range(len(support))
            if cut & (1 << index)
        )
        for distinguished in cut_faces:
            objective = np.zeros(len(support), dtype=float)
            objective[list(cut_faces)] = 1.0
            objective[distinguished] = -1.0
            labels = locally_admissible_milp(
                support, incidence, cutoff, objective
            )
            if labels is None:
                continue
            defect = labels[distinguished] - sum(
                labels[index]
                for index in cut_faces
                if index != distinguished
            )
            if defect <= 0:
                continue
            witness = CocircuitViolation(
                extent,
                support,
                labels,
                cut,
                distinguished,
                sheets,
            )
            if not witness.validates():
                raise AssertionError(
                    "cocircuit candidate validation drifted"
                )
            return witness
    return None


def pinned_normality_counterexample() -> CocircuitViolation:
    """Return the deterministic certificate transcribed into Lean.

    The ambient extent-one slab has 72 faces and cycle nullity seven.  The
    labels are two on the displayed seventeen-face support and zero
    elsewhere.  The four-link coboundary has odd intersection with that
    support only at ``PINNED_DISTINGUISHED_FACE``.
    """

    extent = 1
    support = tuple(boundary_complete_slab_plaquettes(extent))
    incidence = slab_incidence(extent)
    face_index = {face: index for index, face in enumerate(support)}
    cut_mask = 0
    for link in PINNED_CUT_LINKS:
        cut_mask ^= sum(
            1 << face_index[face]
            for face in incidence[link]
        )
    stars = link_star_masks(support, incidence)
    labels = tuple(
        2 if face in PINNED_NONZERO_FACES else 0
        for face in support
    )
    witness = CocircuitViolation(
        extent=extent,
        support=support,
        labels=labels,
        cut_mask=cut_mask,
        distinguished_face=face_index[PINNED_DISTINGUISHED_FACE],
        sheet_masks=all_kernel_masks(stars, len(support)),
    )
    if not witness.validates():
        raise AssertionError("pinned cocircuit certificate drifted")
    return witness


if __name__ == "__main__":
    result = pinned_normality_counterexample()
    nonzero = tuple(
        (face, label)
        for face, label in zip(
            result.support, result.labels, strict=True
        )
        if label
    )
    print(
        {
            "extent": result.extent,
            "cutoff": max(result.labels),
            "ambient_faces": len(result.support),
            "closed_binary_sheets": len(result.sheet_masks),
            "distinguished_face": result.support[
                result.distinguished_face
            ],
            "cut_defect": result.cut_defect(),
            "nonzero_labels": nonzero,
        }
    )
