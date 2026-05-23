"""Tests for `computations.buffer_shell` (Milestone 1.3).

Coverage:

- ``BufferShellBound`` construction; provenance dict structure.
- Bound is monotone in δ_k (work_plan 1.3 test).
- Bound formula vanishes as g_k → 0 (formula property).
- The (C, κ, β) constants match the documented provenance:
    * κ = 3/4 in canonical convention; κ = 3 in Wilson.
    * β = 3 (dim SU(2)).
- Manton rejected (same as 1.2 ``kappa_from_casimir``).
- Numerical reference: direct heat-kernel quadrature is well-defined,
  monotone in δ, and the bound tracks its shape at moderate g.
- Order-of-magnitude consistency at moderate g (g ≥ 1), per
  work_plan 1.3 "consistent with direct numerical integration of the
  heat kernel."  The bound is NOT a uniform upper bound at small g
  because the canonical-convention probability has a Haar-floor that
  the ``exp(-κ/g²)·g^β`` shape vanishes below — see
  ``notes/single-plaquette-derivation.md`` §4 for the discussion.
- Input validation (positive δ, g; Manton rejection).
- Figure generation smoke test (writes a non-empty SVG).
"""

from __future__ import annotations

from pathlib import Path

import pytest

from computations.buffer_shell import (
    BUFFER_BOUND_PREFACTOR,
    BufferShellBound,
    buffer_measure_exact_numerical,
    plot_buffer_bound_vs_g,
    shell_weyl_volume,
    single_plaquette_buffer_measure,
)
from computations.heat_kernel import HeatKernelConvention

CANONICAL = HeatKernelConvention.CANONICAL
WILSON = HeatKernelConvention.WILSON
MANTON = HeatKernelConvention.MANTON


# --------------------------------------------------------------------------
# Shell Weyl-volume
# --------------------------------------------------------------------------


def test_shell_weyl_volume_positive() -> None:
    """For δ > 0, the Weyl volume of the annulus is positive."""
    for delta in (0.05, 0.1, 0.5, 1.0):
        assert shell_weyl_volume(delta) > 0


def test_shell_weyl_volume_monotone() -> None:
    """Shell Weyl volume is monotone increasing in δ."""
    deltas = [0.05, 0.1, 0.2, 0.4, 0.8]
    vols = [shell_weyl_volume(d) for d in deltas]
    for i in range(len(vols) - 1):
        assert vols[i] < vols[i + 1]


def test_shell_weyl_volume_small_delta_cubic() -> None:
    """For small δ, the Weyl volume scales like δ³ (3D shell)."""
    # Compare to leading-order expansion: (4 δ³ / 3 - δ³ / 48) / (2 π).
    import math

    for delta in (0.01, 0.02, 0.05):
        observed = shell_weyl_volume(delta)
        expected_leading = (4 / 3 - 1 / 48) * delta**3 / (2 * math.pi)
        # Should agree to within 10% for δ ≤ 0.05.
        assert observed == pytest.approx(expected_leading, rel=0.10)


def test_shell_weyl_volume_rejects_nonpositive() -> None:
    with pytest.raises(ValueError):
        shell_weyl_volume(0.0)
    with pytest.raises(ValueError):
        shell_weyl_volume(-0.1)


# --------------------------------------------------------------------------
# BufferShellBound construction + the (C, κ, β) triple
# --------------------------------------------------------------------------


def test_bound_is_BufferShellBound_with_provenance() -> None:
    b = single_plaquette_buffer_measure(0.2, 1.0, CANONICAL)
    assert isinstance(b, BufferShellBound)
    assert b.delta_k == 0.2
    assert b.g_k == 1.0
    assert b.convention is CANONICAL
    # Provenance dict has the four documented keys.
    for key in ("kappa", "beta", "C_weyl_volume", "C_safety_prefactor"):
        assert key in b.provenance


def test_bound_kappa_canonical_is_three_quarters() -> None:
    """SU(2) κ in the canonical convention is 3/4 = C_2(1/2)."""
    b = single_plaquette_buffer_measure(0.2, 1.0, CANONICAL)
    assert b.kappa == pytest.approx(0.75)


def test_bound_kappa_wilson_is_three() -> None:
    """SU(2) κ in Wilson is 2N · C_2(1/2) = 4 · 3/4 = 3."""
    b = single_plaquette_buffer_measure(0.2, 1.0, WILSON)
    assert b.kappa == pytest.approx(3.0)


def test_bound_beta_is_group_dimension() -> None:
    """β = dim SU(2) = 3 in every convention."""
    for conv in (CANONICAL, WILSON):
        b = single_plaquette_buffer_measure(0.2, 1.0, conv)
        assert b.beta == 3


def test_bound_C_includes_safety_prefactor() -> None:
    """C(δ) = BUFFER_BOUND_PREFACTOR · shell_weyl_volume(δ)."""
    delta = 0.2
    b = single_plaquette_buffer_measure(delta, 1.0, CANONICAL)
    assert b.C == pytest.approx(BUFFER_BOUND_PREFACTOR * shell_weyl_volume(delta))


# --------------------------------------------------------------------------
# work_plan 1.3 sanity checks
# --------------------------------------------------------------------------


def test_bound_monotone_in_delta_k() -> None:
    """work_plan 1.3 test: bound increases monotonically in δ_k."""
    deltas = [0.05, 0.1, 0.2, 0.4, 0.8]
    values = [
        single_plaquette_buffer_measure(d, 1.0, CANONICAL).value() for d in deltas
    ]
    for i in range(len(values) - 1):
        assert values[i] < values[i + 1]


def test_bound_formula_vanishes_as_g_to_zero() -> None:
    """work_plan 1.3 test: bound formula → 0 as g_k → 0.

    The formula ``C · exp(-κ/g²) · g^β`` with κ > 0 and β ≥ 0 vanishes
    as g → 0 because exp(-κ/g²) dominates.  This is a property of the
    formula (which is what we deliver); the actual canonical-convention
    buffer probability has a Haar-floor — see the notes.
    """
    for delta in (0.05, 0.1, 0.5):
        # Strictly decreasing toward zero.
        v_1 = single_plaquette_buffer_measure(delta, 1.0, CANONICAL).value()
        v_p5 = single_plaquette_buffer_measure(delta, 0.5, CANONICAL).value()
        v_p3 = single_plaquette_buffer_measure(delta, 0.3, CANONICAL).value()
        v_p1 = single_plaquette_buffer_measure(delta, 0.1, CANONICAL).value()
        assert v_1 > v_p5 > v_p3 > v_p1
        # And the smallest is exponentially tiny.
        assert v_p1 < 1e-20


def test_bound_consistent_with_numerical_at_moderate_g() -> None:
    """work_plan 1.3 test: at moderate g (g ≈ 1.5), bound and direct
    numerical heat-kernel integration agree in shape and order of
    magnitude.  The agreement is best when the irrep-tail captures the
    leading behavior, i.e. at moderate-to-large g; at small g the
    bound underestimates (see notes §4)."""
    for delta in (0.05, 0.1, 0.2):
        bound = single_plaquette_buffer_measure(delta, 1.5, CANONICAL).value()
        numerical = buffer_measure_exact_numerical(delta, 1.5, CANONICAL)
        # Same order of magnitude: 0.5 ≤ bound / numerical ≤ 5.
        ratio = bound / numerical
        assert 0.5 <= ratio <= 5.0, (
            f"δ={delta}, g=1.5: bound/numerical = {ratio:.3f}, expected [0.5, 5.0]"
        )


# --------------------------------------------------------------------------
# Direct numerical reference
# --------------------------------------------------------------------------


def test_numerical_buffer_measure_positive() -> None:
    for delta in (0.05, 0.1, 0.5):
        for g in (0.5, 1.0, 1.5):
            assert buffer_measure_exact_numerical(delta, g, CANONICAL) > 0


def test_numerical_buffer_measure_monotone_in_delta() -> None:
    """The DIRECT numerical buffer probability is also monotone in δ."""
    deltas = [0.05, 0.1, 0.2, 0.4]
    g = 1.0
    values = [buffer_measure_exact_numerical(d, g, CANONICAL) for d in deltas]
    for i in range(len(values) - 1):
        assert values[i] < values[i + 1]


# --------------------------------------------------------------------------
# Convention handling
# --------------------------------------------------------------------------


def test_manton_rejected() -> None:
    with pytest.raises(ValueError, match="Manton"):
        single_plaquette_buffer_measure(0.2, 1.0, MANTON)
    with pytest.raises(ValueError, match="Manton"):
        buffer_measure_exact_numerical(0.2, 1.0, MANTON)


def test_input_validation() -> None:
    with pytest.raises(ValueError):
        single_plaquette_buffer_measure(0.0, 1.0, CANONICAL)
    with pytest.raises(ValueError):
        single_plaquette_buffer_measure(-0.1, 1.0, CANONICAL)
    with pytest.raises(ValueError):
        single_plaquette_buffer_measure(0.2, 0.0, CANONICAL)
    with pytest.raises(ValueError):
        single_plaquette_buffer_measure(0.2, -1.0, CANONICAL)


# --------------------------------------------------------------------------
# Wilson convention spot check
# --------------------------------------------------------------------------


def test_wilson_bound_smaller_than_canonical() -> None:
    """At the same (δ, g), Wilson's larger κ = 3 (vs canonical 3/4)
    produces a SMALLER bound (the exp factor decays faster).  Confirms
    the convention switch propagates correctly."""
    delta, g = 0.2, 1.0
    b_canonical = single_plaquette_buffer_measure(delta, g, CANONICAL).value()
    b_wilson = single_plaquette_buffer_measure(delta, g, WILSON).value()
    assert b_wilson < b_canonical


# --------------------------------------------------------------------------
# Figure smoke test
# --------------------------------------------------------------------------


def test_plot_buffer_bound_vs_g_writes_svg(tmp_path: Path) -> None:
    """Smoke test: the plot writes a non-empty SVG."""
    out = tmp_path / "test_bound.svg"
    result = plot_buffer_bound_vs_g(
        delta_values=(0.1, 0.2),
        g_range=(0.6, 1.2),
        n_points=10,
        output_path=str(out),
    )
    assert Path(result) == out
    assert out.exists()
    assert out.stat().st_size > 0
    text = out.read_text(encoding="utf-8")
    assert text.lstrip().startswith("<?xml")
    assert "</svg>" in text
