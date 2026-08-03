"""Exact cutoff-one values of the two BF4 five-cycle Haar marginals.

The Lean route reduces the two centered-vacuum moments from 116 link Haar
variables to Haar integration over the based cycles ``[0, 4, 5, 6, 10]``.
At cutoff one, the independently implemented exact whole-slab contraction
has a seven-dimensional binary cycle space, hence only 128 closed surfaces.
This module reads that exact rational certificate and performs the remaining
comparison and centered-normalization algebra as sparse polynomials.

The heat coordinate is called ``w`` in Lean and ``s`` in the Python Haar
integrator.  They are the same variable: ``coeffW(w, 1) = 2 w^3``.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import cache

from computations.exact_haar_network import (
    SPoly,
    sp_add_into,
    sp_clean,
    sp_mul,
    sp_str,
)
from computations.general_reflection_cut_carrier import (
    binary_reflection_cut_carrier,
)
from computations.whole_corrected_slab_kraus import (
    EXPECTED_BINARY_MASS,
    binary_whole_slab_kraus_kernel,
)

BASED_CYCLES = (0, 4, 5, 6, 10)

EXPECTED_VACUUM_ROW_HAAR5: SPoly = {
    0: Fraction(1),
    18: Fraction(4),
}

EXPECTED_HAAR5_DIFFERENCE: SPoly = {
    18: Fraction(28),
    30: Fraction(96),
    36: Fraction(224),
    42: Fraction(192),
    48: Fraction(3),
}

EXPECTED_CENTERED_NUMERATOR: SPoly = {
    18: Fraction(24),
    30: Fraction(96),
    36: Fraction(208),
    42: Fraction(192),
    48: Fraction(3),
}

EXPECTED_CENTERED_DEFECT_NUMERATOR: SPoly = {
    36: Fraction(768),
    48: Fraction(5376),
    54: Fraction(12032),
    60: Fraction(19968),
    66: Fraction(41640),
    72: Fraction(83456),
    78: Fraction(83520),
    84: Fraction(38160),
    90: Fraction(1152),
    96: Fraction(9),
}


def _sp_subtract(left: SPoly, right: SPoly) -> SPoly:
    result = sp_clean(left)
    sp_add_into(result, right, Fraction(-1))
    return sp_clean(result)


def _all_coefficients_positive(polynomial: SPoly) -> bool:
    return bool(polynomial) and all(coefficient > 0 for coefficient in polynomial.values())


def _vacuum_row_haar5() -> tuple[SPoly, int]:
    """Read the vacuum row from the exact zero-signature Kraus block."""
    carrier = binary_reflection_cut_carrier()
    kernel = binary_whole_slab_kraus_kernel()
    for signature, states, block in zip(
        carrier.signatures,
        carrier.states_by_signature,
        kernel.blocks,
        strict=True,
    ):
        if signature.face_mask != 0:
            continue
        vacuum_rows = [
            row
            for row, state in enumerate(states)
            if state.lower_patch_mask == 0
        ]
        if len(vacuum_rows) != 1:
            raise AssertionError("the zero-signature block lost its unique vacuum state")
        row_polynomial: SPoly = {}
        for entry in block.kernel[vacuum_rows[0]]:
            sp_add_into(row_polynomial, entry)
        return sp_clean(row_polynomial), len(block.kernel[vacuum_rows[0]])
    raise AssertionError("the exact cutoff-one kernel lost its zero-signature block")


@dataclass(frozen=True)
class CutoffOneHaarFiveMomentBalance:
    """Exact polynomial certificate for both Haar values and their balance."""

    based_cycles: tuple[int, ...]
    closed_surface_count: int
    vacuum_row_surface_count: int
    vacuum_row: SPoly
    constant_quadratic: SPoly
    comparison_difference: SPoly
    vacuum_row_square: SPoly
    centered_numerator: SPoly
    partition_excess: SPoly
    centered_defect_numerator: SPoly

    @property
    def haar5_values_strictly_ordered_for_positive_w(self) -> bool:
        return _all_coefficients_positive(self.comparison_difference)

    @property
    def centered_sides_strictly_differ_for_positive_w(self) -> bool:
        return _all_coefficients_positive(self.centered_defect_numerator)

    def validates(self) -> bool:
        return (
            self.based_cycles == BASED_CYCLES
            and self.closed_surface_count == 128
            and self.vacuum_row_surface_count == 2
            and self.vacuum_row == EXPECTED_VACUUM_ROW_HAAR5
            and self.constant_quadratic == EXPECTED_BINARY_MASS
            and self.comparison_difference == EXPECTED_HAAR5_DIFFERENCE
            and self.vacuum_row_square == sp_mul(self.vacuum_row, self.vacuum_row)
            and self.centered_numerator == EXPECTED_CENTERED_NUMERATOR
            and self.centered_numerator
            == _sp_subtract(self.constant_quadratic, self.vacuum_row_square)
            and self.partition_excess
            == _sp_subtract(self.constant_quadratic, {0: Fraction(1)})
            and self.centered_defect_numerator
            == EXPECTED_CENTERED_DEFECT_NUMERATOR
            and self.centered_defect_numerator
            == sp_mul(self.partition_excess, self.centered_numerator)
            and self.haar5_values_strictly_ordered_for_positive_w
            and self.centered_sides_strictly_differ_for_positive_w
        )


@cache
def cutoff_one_haar5_moment_balance() -> CutoffOneHaarFiveMomentBalance:
    """Evaluate and compare the two exact Haar-five moments."""
    kernel = binary_whole_slab_kraus_kernel()
    vacuum_row, vacuum_row_surface_count = _vacuum_row_haar5()
    constant_quadratic = sp_clean(kernel.unnormalized_mass)
    vacuum_row_square = sp_mul(vacuum_row, vacuum_row)
    centered_numerator = _sp_subtract(constant_quadratic, vacuum_row_square)
    partition_excess = _sp_subtract(constant_quadratic, {0: Fraction(1)})
    return CutoffOneHaarFiveMomentBalance(
        based_cycles=BASED_CYCLES,
        closed_surface_count=kernel.physical_assignment_count,
        vacuum_row_surface_count=vacuum_row_surface_count,
        vacuum_row=vacuum_row,
        constant_quadratic=constant_quadratic,
        comparison_difference=_sp_subtract(constant_quadratic, vacuum_row),
        vacuum_row_square=vacuum_row_square,
        centered_numerator=centered_numerator,
        partition_excess=partition_excess,
        centered_defect_numerator=sp_mul(partition_excess, centered_numerator),
    )


def polynomial_in_w(polynomial: SPoly) -> str:
    """Format an exact sparse polynomial using the Lean heat variable ``w``."""
    return sp_str(polynomial).replace("s^", "w^")


def render_balance_report(balance: CutoffOneHaarFiveMomentBalance) -> str:
    """Render the exact evaluation and normalized centered comparison."""
    row = polynomial_in_w(balance.vacuum_row)
    constant = polynomial_in_w(balance.constant_quadratic)
    difference = polynomial_in_w(balance.comparison_difference)
    numerator = polynomial_in_w(balance.centered_numerator)
    defect = polynomial_in_w(balance.centered_defect_numerator)
    cycles = ",".join(str(cycle) for cycle in balance.based_cycles)
    return "\n".join(
        (
            "EXACT CUTOFF-ONE HAAR_5 MOMENT BALANCE",
            "=======================================",
            f"based cycles       [{cycles}]",
            f"closed surfaces    {balance.closed_surface_count}",
            f"vacuum-row support {balance.vacuum_row_surface_count}",
            "",
            f"R(w) = Haar_5(row)      = {row}",
            f"C(w) = Haar_5(constant) = {constant}",
            f"C(w) - R(w)             = {difference}",
            "",
            "p_vac(w)                = R(w) / C(w)",
            f"N(w) = C(w) - R(w)^2    = {numerator}",
            "signed centered moment  = N(w) / C(w)",
            "physical centered moment= N(w) / C(w)^2",
            f"same-action defect      = ({defect}) / C(w)^2",
            "",
            "For w > 0: C(w) > R(w), N(w) > 0, and the defect is strictly positive.",
            "The centered same-action balance holds only at the degenerate point w = 0.",
        )
    )
