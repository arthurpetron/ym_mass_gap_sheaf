"""Exact regression and falsification gates for dual positivity survival."""

from fractions import Fraction
from itertools import product
from typing import Any

import pytest
import sympy
from sympy.physics.wigner import clebsch_gordan

from computations.dual_positivity_survival import (
    brick_dual_amplitude,
    double_cube_structured_table,
    negative_slab_witnesses,
    negative_wheel_witnesses,
    rim_channel_activity,
    rim_channel_decomposition,
    single_cube_table,
    slab_value,
    wheel_sweep,
    wheel_value,
)
from computations.exact_haar_network import sign_on_unit_interval


def _rotate(values: tuple[int, ...], amount: int = 1) -> tuple[int, ...]:
    return values[amount:] + values[:amount]


def _magnetic_indices(label: int) -> tuple[int, ...]:
    return tuple(range(-label, label + 1, 2))


def _clebsch_gordan_doubled(
    left_label: int,
    left_magnetic: int,
    right_label: int,
    right_magnetic: int,
    output_label: int,
    output_magnetic: int,
) -> Any:  # noqa: ANN401
    return clebsch_gordan(
        sympy.Rational(left_label, 2),
        sympy.Rational(right_label, 2),
        sympy.Rational(output_label, 2),
        sympy.Rational(left_magnetic, 2),
        sympy.Rational(right_magnetic, 2),
        sympy.Rational(output_magnetic, 2),
    )


def _wheel_clebsch_gordan_squared_norm(
    pages: tuple[int, int, int, int],
    rim: tuple[int, int, int, int],
) -> Any:  # noqa: ANN401
    """Independent exact recoupling formula for the quaternion contraction."""

    squared_norm = sympy.S.Zero
    for page_magnetic in product(*(_magnetic_indices(label) for label in pages)):
        amplitude = sympy.S.Zero
        for rim_magnetic in product(*(_magnetic_indices(label) for label in rim)):
            term = sympy.S.One
            for i in range(4):
                term *= _clebsch_gordan_doubled(
                    pages[i],
                    page_magnetic[i],
                    rim[i],
                    rim_magnetic[i],
                    rim[i - 1],
                    rim_magnetic[i - 1],
                )
            amplitude += term
        squared_norm += sympy.conjugate(amplitude) * amplitude
    return sympy.simplify(
        squared_norm / sympy.prod(label + 1 for label in rim)
    )


# P0: a closed single-cube surface.
def test_single_cube_control() -> None:
    assert single_cube_table(2) == {
        (0, 0, 0, 0, 0, 0): Fraction(1),
        (1, 1, 1, 1, 1, 1): Fraction(1, 16),
        (2, 2, 2, 2, 2, 2): Fraction(1, 81),
    }


# P1: two cubes sharing a face.
def test_double_cube_small_table() -> None:
    table = double_cube_structured_table(1, 2)
    assert table == {
        (0, 0, 0): Fraction(1),
        (0, 1, 1): Fraction(1, 16),
        (1, 0, 1): Fraction(1, 16),
        (1, 1, 0): Fraction(1, 256),
        (1, 1, 2): Fraction(1, 256),
    }
    # Reflection through the shared face exchanges the two cubes.
    assert all(table.get((a, b, k)) == table.get((b, a, k)) for a, b, k in table)


# P1b: the first unanchored four-wall circuit.
def test_slab_spot_values() -> None:
    assert slab_value(1, (0, 0, 0, 0)) == {0: Fraction(1, 16384)}
    assert slab_value(1, (2, 2, 2, 2)) == {0: Fraction(7, 442368)}
    assert slab_value(2, (2, 2, 2, 2)) == {0: Fraction(1, 28697814)}
    assert slab_value(1, (1, 1, 1, 1)) == {}


def test_slab_cyclic_orientation_invariance_nearby() -> None:
    """A nearby unpinned circuit is unchanged by rotating the square slab."""

    walls = (0, 2, 0, 2)
    value = slab_value(1, walls)
    assert slab_value(1, _rotate(walls)) == value
    assert slab_value(1, _rotate(walls, 2)) == value


def test_unanchored_slab_falsification_grid() -> None:
    """Search all 2*3^4 nearby structured slab assignments for a negative."""

    assert negative_slab_witnesses(1, 2) == {}


# P2: the four-page wheel around one interior link.
def test_wheel_hand_verified_values() -> None:
    assert wheel_value((0, 0, 1, 1), (0, 0, 1, 0)) == {0: Fraction(1, 2)}
    assert wheel_value((2, 2, 2, 2), (2, 2, 2, 2)) == {
        0: Fraction(1, 54)
    }
    assert wheel_value((1, 1, 1, 1), (1, 1, 1, 1)) == {}


def test_wheel_dihedral_invariance_nearby() -> None:
    """Simultaneously relabeling wheel sites preserves the exact contraction."""

    pages = (0, 1, 1, 2)
    rim = (0, 1, 2, 0)
    value = wheel_value(pages, rim)
    assert wheel_value(_rotate(pages), _rotate(rim)) == value
    # Under i -> -i, pages relabel by j_i -> j_{-i}, while the oriented rim
    # edge i -> i+1 relabels by m_i -> m_{-i-1}.
    reflected_pages = (pages[0], pages[3], pages[2], pages[1])
    reflected_rim = (rim[3], rim[2], rim[1], rim[0])
    assert wheel_value(reflected_pages, reflected_rim) == value


def test_wheel_sweep_nonnegative_small() -> None:
    values = wheel_sweep(1)
    assert values
    assert all(value >= 0 for value in values.values())


def test_wheel_falsification_sweep_through_spin_two() -> None:
    """Search the strictly larger 3^8 wheel grid for a negative coefficient."""

    assert negative_wheel_witnesses(2) == {}


@pytest.mark.parametrize(
    ("pages", "rim"),
    [
        ((0, 0, 1, 1), (0, 0, 1, 0)),
        ((2, 2, 2, 2), (2, 2, 2, 2)),
        ((1, 1, 1, 1), (1, 1, 1, 1)),
        ((0, 1, 3, 2), (3, 2, 1, 3)),
        ((0, 1, 1, 2), (0, 1, 2, 0)),
    ],
)
def test_wheel_clebsch_gordan_squared_norm_identity(
    pages: tuple[int, int, int, int],
    rim: tuple[int, int, int, int],
) -> None:
    """Cross-check the all-label formula against quaternion Haar moments."""

    haar_value = wheel_value(pages, rim).get(0, Fraction(0))
    expected = sympy.Rational(haar_value.numerator, haar_value.denominator)
    assert sympy.simplify(
        _wheel_clebsch_gordan_squared_norm(pages, rim) - expected
    ) == 0


# P3: physically summed heat-kernel channel.
def test_rim_channel_exact_polynomial() -> None:
    activity = rim_channel_activity((1, 1, 1, 1))
    assert activity == {
        0: Fraction(1, 4),
        16: Fraction(9, 2),
        24: Fraction(6),
        32: Fraction(21, 4),
    }
    assert sign_on_unit_interval(activity) == "positive"


def test_rim_channel_ledger_is_termwise_positive() -> None:
    decomposition = rim_channel_decomposition((1, 1, 1, 1))
    assert all(next(iter(poly.values())) > 0 for poly in decomposition.values())
    grouped: dict[int, list[tuple[tuple[int, ...], Fraction]]] = {}
    total: dict[int, Fraction] = {}
    for pages, poly in decomposition.items():
        for power, coefficient in poly.items():
            grouped.setdefault(power, []).append((pages, coefficient))
            total[power] = total.get(power, Fraction(0)) + coefficient
    assert {power: len(sectors) for power, sectors in grouped.items()} == {
        0: 1,
        16: 6,
        24: 4,
        32: 1,
    }
    assert total == rim_channel_activity((1, 1, 1, 1))


@pytest.mark.parametrize(
    ("pages", "rim"),
    [
        ((0, 0, 0), (0, 0, 0, 0)),
        ((0, 0, 0, 0), (0, 0, 0)),
        ((0, -1, 0, 0), (0, 0, 0, 0)),
    ],
)
def test_wheel_rejects_malformed_spin_assignments(
    pages: tuple[int, ...], rim: tuple[int, ...]
) -> None:
    with pytest.raises(ValueError):
        wheel_value(pages, rim)


def test_brick_rejects_wrong_face_count() -> None:
    with pytest.raises(ValueError, match="one spin per face"):
        brick_dual_amplitude(1, 1, 1, (0,))
