"""Exact survival probes for positivity of SU(2) dual coefficients.

This module evaluates honest Haar networks rather than inserting the
regression values as formulas.  It walks up a short incidence ladder:

* a single closed cube;
* a double cube with a shared face;
* a 2x2x1 slab with an unanchored intertwiner circuit;
* the four-page wheel around an interior link;
* the heat-kernel sum over the wheel's page spins.

The spin labels are doubled spins ``n = 2j``.  All amplitudes are exact
``Fraction`` values, and heat-kernel channel activities are sparse exact
polynomials in ``s = exp(-t/4)``.  The wheel page sum is genuinely finite:
at vertex ``i`` the fusion rules force
``j_i <= m_{i-1} + m_i``.
"""

from __future__ import annotations

import itertools
from collections.abc import Sequence
from fractions import Fraction
from typing import TypeAlias

from computations.exact_haar_network import (
    P_ONE,
    GaugeFixedComplex,
    SPoly,
    brick_complex,
    casimir4,
    chi,
    contract,
    dim,
    heat_activity,
    holonomy,
    scalar,
)

SpinAssignment: TypeAlias = tuple[int, ...]
WheelAssignment: TypeAlias = tuple[tuple[int, ...], tuple[int, ...]]
Face: TypeAlias = list[tuple[int, int]]
OrientedWord: TypeAlias = tuple[tuple[int, int], ...]
WheelWords: TypeAlias = tuple[
    tuple[OrientedWord, OrientedWord, OrientedWord, OrientedWord],
    tuple[OrientedWord, OrientedWord, OrientedWord, OrientedWord],
]


def _require_nonnegative(label: str, value: int) -> None:
    if value < 0:
        raise ValueError(f"{label} must be nonnegative; got {value}")


def _require_four_spins(label: str, spins: Sequence[int]) -> tuple[int, ...]:
    if len(spins) != 4:
        raise ValueError(f"{label} must contain four doubled spins; got {len(spins)}")
    out = tuple(spins)
    if any(n < 0 for n in out):
        raise ValueError(f"{label} spins must be nonnegative; got {out}")
    return out


# ---------------------------------------------------------------------------
# P0/P1: closed brick complexes
# ---------------------------------------------------------------------------


def brick_dual_amplitude(
    nx: int, ny: int, nz: int, spins: Sequence[int]
) -> SPoly:
    """Evaluate one spin assignment on every face of a closed brick.

    The evaluator builds every plaquette character from its actual oriented
    holonomy, fixes a maximal tree by Haar invariance, and contracts all
    remaining SU(2) links exactly.
    """

    for name, size in (("nx", nx), ("ny", ny), ("nz", nz)):
        if size <= 0:
            raise ValueError(f"{name} must be positive; got {size}")
    cx, faces = brick_complex(nx, ny, nz)
    if len(spins) != len(faces):
        raise ValueError(
            f"one spin per face is required: expected {len(faces)}, got {len(spins)}"
        )
    if any(n < 0 for n in spins):
        raise ValueError("doubled spins must be nonnegative")
    factors = [
        chi(n, cx.holonomy_of(face))
        for n, face in zip(spins, faces, strict=True)
        if n > 0
    ]
    return cx.contract_invariant(factors or [dict(P_ONE)])


def single_cube_table(nmax: int) -> dict[SpinAssignment, Fraction]:
    """Return every nonzero 1x1x1 cube amplitude with labels <= ``nmax``."""

    _require_nonnegative("nmax", nmax)
    _, faces = brick_complex(1, 1, 1)
    out: dict[SpinAssignment, Fraction] = {}
    for spins in itertools.product(range(nmax + 1), repeat=len(faces)):
        value = brick_dual_amplitude(1, 1, 1, spins)
        if value:
            if set(value) != {0}:
                raise AssertionError(f"fixed-spin amplitude depends on s: {value}")
            out[spins] = value[0]
    return out


def _double_cube_face_classes() -> tuple[
    GaugeFixedComplex, list[Face], int, list[int], list[int]
]:
    """Classify the shared and exterior faces of the 1x1x2 brick."""

    cx, faces = brick_complex(1, 1, 2)
    coords: dict[int, tuple[int, int, int]] = {}
    vertex = 0
    for x in range(2):
        for y in range(2):
            for z in range(3):
                coords[vertex] = (x, y, z)
                vertex += 1

    interior: int | None = None
    cube_a: list[int] = []
    cube_b: list[int] = []
    for face_index, face in enumerate(faces):
        face_vertices: set[tuple[int, int, int]] = set()
        for edge_index, _orientation in face:
            a, b = cx.edges[edge_index]
            face_vertices.add(coords[a])
            face_vertices.add(coords[b])
        z_values = {v[2] for v in face_vertices}
        if z_values == {1}:
            interior = face_index
        elif max(z_values) <= 1:
            cube_a.append(face_index)
        else:
            cube_b.append(face_index)
    if interior is None or len(cube_a) != 5 or len(cube_b) != 5:
        raise AssertionError("unexpected deterministic 1x1x2 face geometry")
    return cx, faces, interior, cube_a, cube_b


def double_cube_structured_table(
    nmax: int, kmax: int
) -> dict[tuple[int, int, int], Fraction]:
    """Evaluate ``Z(n_A,n_B,k)`` on the actual 1x1x2 complex.

    The five exposed faces of the lower and upper cube carry ``n_A`` and
    ``n_B`` respectively, while their common face carries ``k``.
    """

    _require_nonnegative("nmax", nmax)
    _require_nonnegative("kmax", kmax)
    _cx, faces, interior, cube_a, cube_b = _double_cube_face_classes()
    out: dict[tuple[int, int, int], Fraction] = {}
    for n_a in range(nmax + 1):
        for n_b in range(nmax + 1):
            for shared in range(kmax + 1):
                spins = [0] * len(faces)
                for face_index in cube_a:
                    spins[face_index] = n_a
                for face_index in cube_b:
                    spins[face_index] = n_b
                spins[interior] = shared
                value = brick_dual_amplitude(1, 1, 2, spins)
                if value:
                    if set(value) != {0}:
                        raise AssertionError(
                            f"fixed-spin amplitude depends on s: {value}"
                        )
                    out[(n_a, n_b, shared)] = value[0]
    return out


# ---------------------------------------------------------------------------
# P1b: 2x2x1 slab with an unanchored four-wall circuit
# ---------------------------------------------------------------------------


def _slab_geometry() -> tuple[
    GaugeFixedComplex, list[Face], list[int], list[int]
]:
    cx, faces = brick_complex(2, 2, 1)
    coords: dict[int, tuple[int, int, int]] = {}
    vertex = 0
    for x in range(3):
        for y in range(3):
            for z in range(2):
                coords[vertex] = (x, y, z)
                vertex += 1

    def face_info(
        face: list[tuple[int, int]],
    ) -> tuple[str, int, int, int] | tuple[str, int, int]:
        vertices: set[tuple[int, int, int]] = set()
        for edge_index, _orientation in face:
            a, b = cx.edges[edge_index]
            vertices.add(coords[a])
            vertices.add(coords[b])
        xs = {v[0] for v in vertices}
        ys = {v[1] for v in vertices}
        zs = {v[2] for v in vertices}
        if len(zs) == 1:
            return ("horizontal", min(zs), min(xs), min(ys))
        if len(xs) == 1:
            return ("x-wall", min(xs), min(ys))
        return ("y-wall", min(ys), min(xs))

    info = [face_info(face) for face in faces]
    interior = [
        i
        for i, (kind, *rest) in enumerate(info)
        if (kind == "x-wall" and rest[0] == 1)
        or (kind == "y-wall" and rest[0] == 1)
    ]
    outer = [i for i in range(len(faces)) if i not in interior]
    cyclic_walls = [
        next(i for i in interior if info[i] == wanted)
        for wanted in [
            ("x-wall", 1, 0),
            ("y-wall", 1, 1),
            ("x-wall", 1, 1),
            ("y-wall", 1, 0),
        ]
    ]
    if len(interior) != 4 or len(cyclic_walls) != 4:
        raise AssertionError("unexpected deterministic 2x2x1 slab geometry")
    return cx, faces, outer, cyclic_walls


def slab_value(n_outer: int, walls: Sequence[int]) -> SPoly:
    """Evaluate a uniform exterior shell and four cyclic interior walls."""

    _require_nonnegative("n_outer", n_outer)
    wall_spins = _require_four_spins("walls", walls)
    cx, faces, outer, cyclic_walls = _slab_geometry()
    spins = [0] * len(faces)
    for face_index in outer:
        spins[face_index] = n_outer
    for face_index, spin in zip(cyclic_walls, wall_spins, strict=True):
        spins[face_index] = spin
    factors = [
        chi(spin, cx.holonomy_of(face))
        for spin, face in zip(spins, faces, strict=True)
        if spin > 0
    ]
    return cx.contract_invariant(factors or [dict(P_ONE)])


def slab_sweep(
    nmax_outer: int, kmax: int
) -> dict[tuple[int, int, int, int, int], Fraction]:
    """Return all nonzero slab values in a finite exact falsification grid."""

    _require_nonnegative("nmax_outer", nmax_outer)
    _require_nonnegative("kmax", kmax)
    out: dict[tuple[int, int, int, int, int], Fraction] = {}
    for n_outer in range(nmax_outer + 1):
        for walls in itertools.product(range(kmax + 1), repeat=4):
            value = slab_value(n_outer, walls)
            if value:
                if set(value) != {0}:
                    raise AssertionError(
                        f"fixed-spin amplitude depends on s: {value}"
                    )
                wall_0, wall_1, wall_2, wall_3 = walls
                out[(n_outer, wall_0, wall_1, wall_2, wall_3)] = value[0]
    return out


# ---------------------------------------------------------------------------
# P2: wheel (four pages around an interior link)
#
# Gauge fixing the spine leaves
#
#   integral product_i chi_{j_i}(X_i)
#                    chi_{m_i}(X_i X_{i+1}^{-1}) dX_i.
# ---------------------------------------------------------------------------


def wheel_oriented_words() -> WheelWords:
    """Return the page and cyclic-rim words defining the actual wheel.

    Page ``i`` is ``X_i`` after the spine has been removed by gauge
    invariance.  Rim ``i`` is the oriented word ``X_i X_(i+1)^-1``.
    Keeping this topology as public data gives certificate exporters and the
    evaluator one shared source of truth.
    """

    pages = tuple(((i, 1),) for i in range(4))
    rims = tuple(((i, 1), ((i + 1) % 4, -1)) for i in range(4))
    return (
        (pages[0], pages[1], pages[2], pages[3]),
        (rims[0], rims[1], rims[2], rims[3]),
    )


def wheel_value(page_spins: Sequence[int], rim_spins: Sequence[int]) -> SPoly:
    """Evaluate the actual four-link wheel Haar contraction."""

    pages = _require_four_spins("page_spins", page_spins)
    rim = _require_four_spins("rim_spins", rim_spins)
    page_words, rim_words = wheel_oriented_words()
    factors = []
    for i in range(4):
        if pages[i] > 0:
            factors.append(chi(pages[i], holonomy(page_words[i])))
        if rim[i] > 0:
            factors.append(chi(rim[i], holonomy(rim_words[i])))
    return scalar(contract(factors or [dict(P_ONE)], range(4)))


def wheel_sweep(nmax: int) -> dict[WheelAssignment, Fraction]:
    """Return all nonzero wheel values with page/rim labels <= ``nmax``.

    Parity and triangle conditions only skip networks that the SU(2) fusion
    rules prove zero; every survivor is still evaluated by exact integration.
    """

    _require_nonnegative("nmax", nmax)
    out: dict[WheelAssignment, Fraction] = {}
    for pages in itertools.product(range(nmax + 1), repeat=4):
        for rim in itertools.product(range(nmax + 1), repeat=4):
            if any(
                (pages[i] + rim[(i - 1) % 4] + rim[i]) % 2 for i in range(4)
            ):
                continue
            if any(
                not (
                    abs(rim[(i - 1) % 4] - rim[i])
                    <= pages[i]
                    <= rim[(i - 1) % 4] + rim[i]
                )
                for i in range(4)
            ):
                continue
            value = wheel_value(pages, rim)
            if value:
                if set(value) != {0}:
                    raise AssertionError(
                        f"fixed-spin amplitude depends on s: {value}"
                    )
                out[(pages, rim)] = value[0]
    return out


# ---------------------------------------------------------------------------
# P3: physically summed heat-kernel page channel
# ---------------------------------------------------------------------------


def rim_channel_activity(rim_spins: Sequence[int]) -> SPoly:
    """Sum all fusion-admissible page spins against heat-kernel activities."""

    rim = _require_four_spins("rim_spins", rim_spins)
    nmax = max(rim[(i - 1) % 4] + rim[i] for i in range(4))
    page_words, rim_words = wheel_oriented_words()
    factors = [heat_activity(holonomy(word), nmax) for word in page_words]
    factors.extend(
        chi(rim[i], holonomy(rim_words[i]))
        for i in range(4)
        if rim[i] > 0
    )
    return scalar(contract(factors, range(4)))


def rim_channel_decomposition(
    rim_spins: Sequence[int],
) -> dict[SpinAssignment, SPoly]:
    """Return the exact page-spin ledger that resums to a rim activity."""

    rim = _require_four_spins("rim_spins", rim_spins)
    nmax = max(rim[(i - 1) % 4] + rim[i] for i in range(4))
    terms: dict[SpinAssignment, SPoly] = {}
    for pages in itertools.product(range(nmax + 1), repeat=4):
        value = wheel_value(pages, rim)
        if not value:
            continue
        coefficient = Fraction(1)
        s_power = 0
        for spin in pages:
            coefficient *= dim(spin)
            s_power += casimir4(spin)
        terms[pages] = {s_power: coefficient * value[0]}
    return terms


def negative_wheel_witnesses(nmax: int) -> dict[WheelAssignment, Fraction]:
    """Search an exact wheel grid and retain only negative coefficients.

    This is intentionally a falsification helper: an empty result is finite
    evidence, never a theorem beyond the requested cutoff.
    """

    return {
        assignment: value
        for assignment, value in wheel_sweep(nmax).items()
        if value < 0
    }


def negative_slab_witnesses(
    nmax_outer: int, kmax: int
) -> dict[tuple[int, int, int, int, int], Fraction]:
    """Search an exact unanchored-slab grid for a negative amplitude."""

    return {
        assignment: value
        for assignment, value in slab_sweep(nmax_outer, kmax).items()
        if value < 0
    }
