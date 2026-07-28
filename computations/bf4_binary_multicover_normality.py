"""Exact/combinatorial scout for the BF4 binary-multicover theorem.

For a finite support ``S`` of corrected-slab plaquettes, a binary sheet is a
subset of ``S`` incident an even number of times at every slab link.  A
higher-spin state ``x : S -> Nat`` has a binary multicover exactly when it is
an additive sum of such sheet indicators.

The Lean positive-row hypothesis gives local SU(2) invariant multiplicity at
every link.  This scout tests whether those local conditions imply membership
in the global binary-sheet semigroup on small actual BF4 supports.

Numerical MILP is used only to scout candidates.  Any witness selected for the
formal proof must subsequently be checked by exact finite arithmetic in Lean.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations, product

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp

from computations.dual_half_time_reflection_route import (
    boundary_complete_slab_plaquettes,
)
from computations.dual_positivity_geometry_bridge import (
    Link4,
    Plaquette4,
    Vertex4,
    edges_of,
)
from computations.exact_haar_network import invariant_multiplicity
from computations.general_cutoff_coherence_scout import unit_cube_boundary


def slab_incidence(
    extent: int,
) -> dict[Link4, tuple[Plaquette4, ...]]:
    """The actual corrected-slab link-to-face incidence relation."""

    incidence: dict[Link4, list[Plaquette4]] = {}
    for face in boundary_complete_slab_plaquettes(extent):
        for link in edges_of(face):
            incidence.setdefault(link, []).append(face)
    return {link: tuple(faces) for link, faces in incidence.items()}


def even_sheet_masks(
    support: tuple[Plaquette4, ...],
    incidence: dict[Link4, tuple[Plaquette4, ...]],
) -> tuple[int, ...]:
    """Enumerate every nonzero even binary sheet inside a small support."""

    face_index = {face: index for index, face in enumerate(support)}
    link_masks = tuple(
        sum(1 << face_index[face] for face in incident if face in face_index)
        for incident in incidence.values()
    )
    return tuple(
        mask
        for mask in range(1, 1 << len(support))
        if all((mask & link_mask).bit_count() % 2 == 0 for link_mask in link_masks)
    )


def locally_admissible(
    support: tuple[Plaquette4, ...],
    labels: tuple[int, ...],
    incidence: dict[Link4, tuple[Plaquette4, ...]],
) -> bool:
    """Check exact positive SU(2) invariant multiplicity at every slab link."""

    label = dict(zip(support, labels, strict=True))
    return all(
        invariant_multiplicity(
            tuple(label.get(face, 0) for face in incident if label.get(face, 0))
        )
        > 0
        for incident in incidence.values()
    )


def has_binary_multicover(
    labels: tuple[int, ...],
    sheet_masks: tuple[int, ...],
) -> bool:
    """MILP membership test in the additive binary-sheet semigroup."""

    if not sheet_masks:
        return not any(labels)
    columns = np.array(
        [
            [1.0 if mask & (1 << row) else 0.0 for mask in sheet_masks]
            for row in range(len(labels))
        ],
        dtype=float,
    )
    result = milp(
        c=np.ones(len(sheet_masks), dtype=float),
        integrality=np.ones(len(sheet_masks), dtype=int),
        bounds=Bounds(
            np.zeros(len(sheet_masks), dtype=float),
            np.full(len(sheet_masks), np.inf, dtype=float),
        ),
        constraints=LinearConstraint(
            columns,
            np.array(labels, dtype=float),
            np.array(labels, dtype=float),
        ),
        options={"time_limit": 5.0},
    )
    return bool(result.success)


def slab_unit_cubes(extent: int) -> tuple[tuple[Plaquette4, ...], ...]:
    """All coordinate unit-cube boundaries contained in the slab face list."""

    face_space = set(boundary_complete_slab_plaquettes(extent))
    cubes: list[tuple[Plaquette4, ...]] = []
    coordinate_range = range(extent + 1)
    for base in product(coordinate_range, repeat=4):
        vertex: Vertex4 = tuple(base)  # type: ignore[assignment]
        for directions in combinations(range(4), 3):
            boundary = unit_cube_boundary(vertex, directions)
            if set(boundary).issubset(face_space):
                cubes.append(boundary)
    return tuple(cubes)


@dataclass(frozen=True)
class MulticoverCounterexample:
    extent: int
    support: tuple[Plaquette4, ...]
    labels: tuple[int, ...]
    sheet_masks: tuple[int, ...]

    def validates(self) -> bool:
        incidence = slab_incidence(self.extent)
        return (
            locally_admissible(self.support, self.labels, incidence)
            and not has_binary_multicover(self.labels, self.sheet_masks)
            and self.sheet_masks
            == even_sheet_masks(self.support, incidence)
        )


def search_cube_unions(
    extent: int = 1,
    maximum_cubes: int = 4,
    maximum_support: int = 18,
    maximum_label: int = 3,
) -> MulticoverCounterexample | None:
    """Search small cube-union supports and low positive spin labels."""

    incidence = slab_incidence(extent)
    cubes = slab_unit_cubes(extent)
    seen_supports: set[tuple[Plaquette4, ...]] = set()
    for cube_count in range(1, maximum_cubes + 1):
        for chosen in combinations(cubes, cube_count):
            support = tuple(sorted(set().union(*map(set, chosen))))
            if support in seen_supports or len(support) > maximum_support:
                continue
            seen_supports.add(support)
            sheets = even_sheet_masks(support, incidence)
            if not sheets:
                continue

            fixed_candidates = (
                tuple(2 for _ in support),
                tuple(3 for _ in support),
            )
            for labels in fixed_candidates:
                if (
                    locally_admissible(support, labels, incidence)
                    and not has_binary_multicover(labels, sheets)
                ):
                    witness = MulticoverCounterexample(
                        extent, support, labels, sheets
                    )
                    if not witness.validates():
                        raise AssertionError("candidate validation drifted")
                    return witness

            if len(support) <= 12:
                for labels in product(range(1, maximum_label + 1), repeat=len(support)):
                    if (
                        locally_admissible(support, labels, incidence)
                        and not has_binary_multicover(labels, sheets)
                    ):
                        witness = MulticoverCounterexample(
                            extent, support, labels, sheets
                        )
                        if not witness.validates():
                            raise AssertionError("candidate validation drifted")
                        return witness
    return None


if __name__ == "__main__":
    print(search_cube_unions())
