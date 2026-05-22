"""Tests for ``computations.su2_representations`` (Milestone 1.1).

Coverage:

- Enumeration of irreps and rejection of malformed inputs.
- Dimension d_j = 2j + 1 as sympy expression and float (symbolic check).
- Casimir C_2(j) = j(j + 1) as sympy expression and float (symbolic check).
- The required spec check: C_2(1/2) = 3/4 returned as a sympy witness.
- Character formula chi_j(theta) = sin((2j+1) theta / 2) / sin(theta / 2)
  matches its symbolic form on each irrep, and the numerical evaluator
  agrees with direct evaluation away from removable singularities.
- Numerical character orthogonality (Schur) at machine precision.
- The figure script runs and produces a non-empty SVG.
"""

from __future__ import annotations

from fractions import Fraction
from pathlib import Path

import numpy as np
import pytest
import sympy

from computations.su2_representations import (
    DEFAULT_J_MAX,
    KILLING_FORM_CONVENTION,
    Irrep,
    character_inner_product,
    character_orthogonality_matrix,
    enumerate_irreps,
    plot_casimir_spectrum,
    verify_casimir_one_half,
)

# --------------------------------------------------------------------------
# Convention pin (so future modules can detect a silent change).
# --------------------------------------------------------------------------


def test_killing_form_convention_is_physics_spin() -> None:
    assert KILLING_FORM_CONVENTION == "physics_spin"


# --------------------------------------------------------------------------
# Enumeration.
# --------------------------------------------------------------------------


def test_enumerate_irreps_up_to_two() -> None:
    irreps = enumerate_irreps(Fraction(2))
    expected_js = [
        Fraction(0),
        Fraction(1, 2),
        Fraction(1),
        Fraction(3, 2),
        Fraction(2),
    ]
    assert [r.j for r in irreps] == expected_js


def test_enumerate_irreps_default_j_max() -> None:
    irreps = enumerate_irreps()
    assert irreps[0].j == Fraction(0)
    assert irreps[-1].j == DEFAULT_J_MAX
    # 11 irreps for j in {0, 1/2, 1, ..., 5}.
    assert len(irreps) == 11


def test_enumerate_rejects_non_half_integer_j_max() -> None:
    with pytest.raises(ValueError, match="half-integer"):
        enumerate_irreps(Fraction(1, 3))


def test_enumerate_rejects_negative_j_max() -> None:
    with pytest.raises(ValueError, match="non-negative"):
        enumerate_irreps(Fraction(-1))


def test_irrep_constructor_rejects_negative_spin() -> None:
    with pytest.raises(ValueError, match="non-negative"):
        Irrep.from_spin(Fraction(-1, 2))


def test_irrep_constructor_rejects_non_half_integer_spin() -> None:
    with pytest.raises(ValueError, match="half-integer"):
        Irrep.from_spin(Fraction(1, 3))


# --------------------------------------------------------------------------
# Dimensions.
# --------------------------------------------------------------------------


def test_dimension_symbolic_equals_2j_plus_1() -> None:
    for r in enumerate_irreps(Fraction(3)):
        j_sym = sympy.Rational(r.j.numerator, r.j.denominator)
        expected = 2 * j_sym + 1
        assert sympy.simplify(r.dimension_symbolic - expected) == 0


def test_dimension_float_matches_symbolic() -> None:
    for r in enumerate_irreps(Fraction(3)):
        assert r.dimension_float == 2 * float(r.j) + 1
        assert r.dimension_float == float(r.dimension_symbolic)


# --------------------------------------------------------------------------
# Casimirs.
# --------------------------------------------------------------------------


def test_verify_casimir_one_half_returns_sympy_zero_witness() -> None:
    """Constructive law: the witness is the sympy expression, not a bool."""
    witness = verify_casimir_one_half()
    assert isinstance(witness, sympy.Expr)
    assert witness == 0
    # The witness is *literally* the sympy zero object, not just falsy.
    assert witness == sympy.S.Zero


def test_casimir_one_half_value() -> None:
    """C_2(1/2) = 3/4 directly on the constructed irrep."""
    half = Irrep.from_spin(Fraction(1, 2))
    assert half.casimir_symbolic == sympy.Rational(3, 4)
    assert half.casimir_float == pytest.approx(0.75, abs=1e-15)


def test_casimir_symbolic_each_irrep() -> None:
    for r in enumerate_irreps(Fraction(3)):
        j_sym = sympy.Rational(r.j.numerator, r.j.denominator)
        expected = j_sym * (j_sym + 1)
        assert sympy.simplify(r.casimir_symbolic - expected) == 0


def test_casimir_known_values_from_outline() -> None:
    """Spot-check the values quoted in docs/outline.md §18.1."""
    expected: dict[Fraction, sympy.Expr] = {
        Fraction(0): sympy.Integer(0),
        Fraction(1, 2): sympy.Rational(3, 4),
        Fraction(1): sympy.Integer(2),
        Fraction(3, 2): sympy.Rational(15, 4),
        Fraction(2): sympy.Integer(6),
    }
    for r in enumerate_irreps(Fraction(2)):
        assert sympy.simplify(r.casimir_symbolic - expected[r.j]) == 0


def test_casimir_float_matches_symbolic() -> None:
    for r in enumerate_irreps(Fraction(5)):
        assert r.casimir_float == pytest.approx(float(r.casimir_symbolic), rel=1e-15)


# --------------------------------------------------------------------------
# Character formula.
# --------------------------------------------------------------------------


def test_character_symbolic_trivial_irrep_is_one() -> None:
    theta = sympy.Symbol("theta", real=True, positive=True)
    chi_0 = Irrep.from_spin(Fraction(0)).character_symbolic(theta)
    assert sympy.simplify(chi_0 - 1) == 0


def test_character_symbolic_half_spin_matches_two_cos_half() -> None:
    """chi_{1/2}(theta) = sin(theta) / sin(theta / 2) = 2 cos(theta / 2)."""
    theta = sympy.Symbol("theta", real=True, positive=True)
    chi = Irrep.from_spin(Fraction(1, 2)).character_symbolic(theta)
    expected = 2 * sympy.cos(theta / 2)
    assert sympy.simplify(chi - expected) == 0


def test_character_symbolic_matches_spec_formula() -> None:
    """Direct symbolic equality with sin((2j+1) theta/2) / sin(theta/2)."""
    theta = sympy.Symbol("theta", real=True, positive=True)
    for r in enumerate_irreps(Fraction(3)):
        d_sym = r.dimension_symbolic
        expected = sympy.sin(d_sym * theta / 2) / sympy.sin(theta / 2)
        chi = r.character_symbolic(theta)
        assert sympy.simplify(chi - expected) == 0


def test_character_numeric_at_identity_recovers_dimension() -> None:
    """chi_j(0) = d_j (L'Hopital limit; numerical branch handles theta = 0)."""
    for r in enumerate_irreps(Fraction(3)):
        assert r.character(0.0) == pytest.approx(r.dimension_float, abs=1e-15)


def test_character_numeric_matches_naive_formula_away_from_zero() -> None:
    theta = float(np.pi / 3.0)
    for r in enumerate_irreps(Fraction(3)):
        d = r.dimension_float
        expected = float(np.sin(d * theta / 2.0) / np.sin(theta / 2.0))
        assert r.character(theta) == pytest.approx(expected, abs=1e-12)


# --------------------------------------------------------------------------
# Character orthogonality (numerical Schur).
# --------------------------------------------------------------------------


def test_inner_product_diagonal_is_one() -> None:
    for r in enumerate_irreps(Fraction(3)):
        value, error = character_inner_product(r, r)
        assert value == pytest.approx(1.0, abs=1e-10)
        # The quadrature also returns its own error witness.
        assert error < 1e-9


def test_inner_product_off_diagonal_is_zero() -> None:
    irreps = enumerate_irreps(Fraction(2))
    for i, ri in enumerate(irreps):
        for k, rk in enumerate(irreps):
            if i == k:
                continue
            value, _ = character_inner_product(ri, rk)
            assert value == pytest.approx(0.0, abs=1e-10)


def test_orthogonality_matrix_witness_under_tolerance() -> None:
    """Constructive witness: return the Gram matrix AND its deviation."""
    irreps = enumerate_irreps(Fraction(5))
    matrix, deviation = character_orthogonality_matrix(irreps)
    n = len(irreps)
    assert matrix.shape == (n, n)
    # The deviation is the modulus; the tolerance is the requirement.
    assert deviation < 1e-10
    np.testing.assert_allclose(matrix, np.eye(n), atol=1e-10)


# --------------------------------------------------------------------------
# Figure generation.
# --------------------------------------------------------------------------


def test_plot_casimir_spectrum_writes_svg(tmp_path: Path) -> None:
    out = tmp_path / "casimir-spectrum.svg"
    result = plot_casimir_spectrum(j_max=Fraction(5), output_path=out)
    assert result == out
    assert out.exists()
    assert out.stat().st_size > 0
    text = out.read_text(encoding="utf-8")
    assert text.lstrip().startswith("<?xml")
    assert "</svg>" in text
