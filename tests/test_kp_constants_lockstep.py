"""Lockstep guard for the canonical KP certificate constants (ρ_sf, ρ_lf, K_sf, K_lf).

Background (the bug this prevents)
----------------------------------
The canonical small-field KP rate ``ρ_sf`` was duplicated in two Lean modules:

  * ``lean/YMGap/Sheaf/SU2KP.lean``           — ``rho_sf_canonical = 25/3``  (CORRECT)
  * ``lean/YMGap/Sheaf/PolymerDomination.lean`` — ``rho_sf_can = 50/9``       (STALE)

``50/9`` is the value obtained with the *old* Bałaban coefficient ``c_λ = 1/2``;
the coefficient was later updated to ``c_λ = 3/4`` (giving ``25/3``), but the
PolymerDomination copy was never updated.  Worse, ``50/9 ≈ 5.556 < 6.947 ≈ ρ_lf``
satisfies ``ρ_sf ≤ ρ_lf`` while the CORRECT ``25/3 ≈ 8.333 > ρ_lf`` does NOT — so
the stale value silently propped up an "activity-exponent dominance" grid that is
false at the true rate.

These tests PARSE the actual Lean sources (not hard-coded mirrors) and pin them to
the Python ground truth ``computations.small_field_kp.compute_small_field_kp``, so
any future drift — in either file, or in ``c_λ`` — fails here.
"""

from __future__ import annotations

import math
import re
from fractions import Fraction
from pathlib import Path

import pytest

from computations.large_field_kp import (
    MU_PLAQUETTE_4D,
    MU_PLAQUETTE_4D_RATIONAL,
    compute_large_field_kp,
    heat_kernel_character_tail_Z,
)
from computations.small_field_kp import (
    BAŁABAN_SPECTRAL_GAP_COEFF,
    HeatKernelConvention,
    MU_CONNECTIVITY_4D,
    compute_small_field_kp,
)

REPO_ROOT = Path(__file__).resolve().parents[1]
SHEAF = REPO_ROOT / "lean" / "YMGap" / "Sheaf"
SU2KP_SRC = (SHEAF / "SU2KP.lean").read_text(encoding="utf-8")
POLYMER_SRC = (SHEAF / "PolymerDomination.lean").read_text(encoding="utf-8")

# The canonical pilot operating point (see small_field_kp.py / mass_gap_bound.py).
CANONICAL_G = Fraction(3, 10)  # g_0 = 0.30, exact


def _lean_mkpos(src: str, name: str) -> Fraction:
    """Extract ``def <name> : Q' := Q'.mkPos <num> <den> ...`` as an exact Fraction."""
    m = re.search(rf"def\s+{re.escape(name)}\s*:\s*Q'\s*:=\s*Q'\.mkPos\s+(\d+)\s+(\d+)", src)
    if m is None:
        raise AssertionError(f"could not find `def {name} : Q' := Q'.mkPos <n> <d>` in source")
    return Fraction(int(m.group(1)), int(m.group(2)))


# --------------------------------------------------------------------------
# Ground truth: the canonical small-field rate is exactly 25/3
# --------------------------------------------------------------------------


def test_balaban_coeff_is_three_quarters() -> None:
    """The drift's root cause: ρ_sf = c_λ · conv / g².  c_λ MUST be 3/4 (not the
    old 1/2); ``50/9`` is the c_λ=1/2 artifact."""
    assert Fraction(BAŁABAN_SPECTRAL_GAP_COEFF) == Fraction(3, 4)


def test_ground_truth_rho_sf_canonical_is_25_over_3() -> None:
    """Exact: ρ_sf = (3/4) · 1 / (3/10)² = 25/3 at the canonical pilot."""
    exact = Fraction(BAŁABAN_SPECTRAL_GAP_COEFF) * Fraction(1) / (CANONICAL_G ** 2)
    assert exact == Fraction(25, 3)
    # and the (float) compute path agrees
    kp = compute_small_field_kp(g_k=float(CANONICAL_G), t_choice=HeatKernelConvention.CANONICAL)
    assert math.isclose(kp.rho_sf, 25 / 3, rel_tol=1e-12)
    # the stale value must NOT reappear
    assert not math.isclose(kp.rho_sf, 50 / 9, rel_tol=1e-9)


# --------------------------------------------------------------------------
# Lean SU2KP is the single source of truth and matches the ground truth
# --------------------------------------------------------------------------


def test_lean_su2kp_rho_sf_matches_ground_truth() -> None:
    """SU2KP.rho_sf_canonical (the source of truth) == 25/3 == Python ground truth."""
    assert _lean_mkpos(SU2KP_SRC, "rho_sf_canonical") == Fraction(25, 3)


def test_lean_su2kp_records_true_rate_ordering() -> None:
    """SU2KP records the TRUE relationship ρ_lf ≤ ρ_sf (small field decays faster).
    This is the relationship PolymerDomination historically inverted."""
    assert "rho_lf_le_rho_sf_canonical" in SU2KP_SRC
    rho_sf = _lean_mkpos(SU2KP_SRC, "rho_sf_canonical")
    rho_lf = _lean_mkpos(SU2KP_SRC, "rho_lf_canonical")
    assert rho_lf <= rho_sf  # 6947/1000 ≤ 25/3


def test_lean_su2kp_K_sf_is_conservative_upper_bound() -> None:
    """K_sf_canonical must be a conservative (≥) upper bound on the true K_sf."""
    kp = compute_small_field_kp(g_k=float(CANONICAL_G), t_choice=HeatKernelConvention.CANONICAL)
    k_sf_lean = _lean_mkpos(SU2KP_SRC, "K_sf_canonical")
    assert float(k_sf_lean) >= kp.K_sf  # 1099/1000 = 1.099 ≥ ~1.005


# --------------------------------------------------------------------------
# PolymerDomination no longer carries the stale / conflicting value
# --------------------------------------------------------------------------


def test_polymer_domination_stale_rho_sf_purged() -> None:
    """The stale ρ_sf = 50/9 must be gone from PolymerDomination."""
    assert "Q'.mkPos 50 9" not in POLYMER_SRC


def test_polymer_domination_no_false_canonical_claim() -> None:
    """PolymerDomination must NOT claim its demo rate "matches" the canonical KP
    rate (the old false comment).  Its ρ_sf grid is now explicitly abstract."""
    assert "matches `Sheaf.SU2KP.rho_sf_canonical`" not in POLYMER_SRC
    # the abstract relabel is present
    assert "abstract illustrative" in POLYMER_SRC.lower() or "ABSTRACT" in POLYMER_SRC


def test_no_lean_module_redefines_canonical_rho_sf_off_truth() -> None:
    """Exhaustive guard: no Sheaf module may define a ``rho_sf*`` Q'-constant whose
    value claims to be the canonical KP rate yet differs from 25/3.  (Abstract demo
    rates like ``:= 1`` are fine; only ``Q'.mkPos`` constants are pinned.)"""
    for src_path in SHEAF.glob("*.lean"):
        src = src_path.read_text(encoding="utf-8")
        for m in re.finditer(r"def\s+(rho_sf\w*)\s*:\s*Q'\s*:=\s*Q'\.mkPos\s+(\d+)\s+(\d+)", src):
            name, num, den = m.group(1), int(m.group(2)), int(m.group(3))
            assert Fraction(num, den) == Fraction(25, 3), (
                f"{src_path.name}:{name} = {num}/{den} is a Q'.mkPos canonical-rate "
                f"constant that differs from the ground truth 25/3 (stale drift?)"
            )

# --------------------------------------------------------------------------
# Large-field lockstep (added 2026-07-25 with the SL.1 μ_plaq upgrade)
#
# The μ_plaq flip (16 → 1359141/25000 ≥ 20e) changed K_lf and q at the
# canonical/Wilson pilots.  The Lean constants in SU2KP.lean were re-pinned
# (K_lf_canonical 16/1000 → 56/1000, q_canonical_upper 154/10000 →
# 523/10000, K_lf_wilson 1/1000 → 2/1000, q_wilson_upper 4/10000 →
# 14/10000).  These tests parse the Lean sources and pin them against the
# Python ground truth so any future drift — in μ_plaq, Z_t, or either Lean
# file — fails here (the same guard the small-field side already had).
# --------------------------------------------------------------------------


def test_mu_plaquette_ground_truth_rational() -> None:
    """The exact-rational μ_plaq ground truth: 1359141/25000 = 20 × 2718282/10⁶,
    the 20e majorant (≥ proof in large_field_kp.MU_PLAQUETTE_4D_RATIONAL and
    tests/test_large_field_kp.py::TestMuPlaquetteGe20eGuard)."""
    assert MU_PLAQUETTE_4D_RATIONAL == Fraction(1359141, 25000)
    assert MU_PLAQUETTE_4D_RATIONAL == Fraction(20) * Fraction(2718282, 10**6)
    # the float consumed downstream faithfully represents it
    assert math.isclose(MU_PLAQUETTE_4D, float(MU_PLAQUETTE_4D_RATIONAL), rel_tol=1e-15)


def test_lean_su2kp_K_lf_canonical_is_conservative_upper_bound() -> None:
    """K_lf_canonical (Lean, 56/1000) must be a conservative (≥) upper bound
    on the true K_lf at the canonical pilot under the DEFAULT μ_plaq.
    (Pre-2026-07-25 the Lean value was 16/1000, sound only under the
    unsupported legacy μ_plaq = 16.)"""
    kp = compute_large_field_kp(float(CANONICAL_G), t_choice=HeatKernelConvention.CANONICAL)
    k_lf_lean = _lean_mkpos(SU2KP_SRC, "K_lf_canonical")
    assert float(k_lf_lean) >= kp.K_lf  # 56/1000 = 0.056 ≥ ~0.05515
    # and it is not grossly loose (within 2% of the Python value)
    assert float(k_lf_lean) <= kp.K_lf * 1.02


def test_lean_su2kp_q_canonical_upper_bounds_python_q() -> None:
    """q_canonical_upper (Lean, 523/10000) ≥ μ_plaq · Z_t^upper (Python)."""
    Z = heat_kernel_character_tail_Z(float(CANONICAL_G), HeatKernelConvention.CANONICAL)
    q_python = MU_PLAQUETTE_4D * Z.upper_bound
    q_lean = _lean_mkpos(SU2KP_SRC, "q_canonical_upper")
    assert float(q_lean) >= q_python  # 0.0523 ≥ ~0.052271
    assert float(q_lean) <= q_python * 1.01


def test_lean_su2kp_K_lf_wilson_is_conservative_upper_bound() -> None:
    """K_lf_wilson (Lean, 2/1000) ≥ true K_lf at the Wilson pilot g = 0.50."""
    kp = compute_large_field_kp(0.50, t_choice=HeatKernelConvention.WILSON)
    k_lf_lean = _lean_mkpos(SU2KP_SRC, "K_lf_wilson")
    assert float(k_lf_lean) >= kp.K_lf  # 2/1000 ≥ ~0.0013379
    q_lean = _lean_mkpos(SU2KP_SRC, "q_wilson_upper")
    Z = heat_kernel_character_tail_Z(0.50, HeatKernelConvention.WILSON)
    assert float(q_lean) >= MU_PLAQUETTE_4D * Z.upper_bound


def test_lean_bf_derivation_arithmetic_canonical() -> None:
    """Re-verify (in exact rationals) the Brydges–Federbush decide-arithmetic
    the Lean kernel checks: q ≤ K_lf · (1 - q) at the re-pinned constants."""
    q = _lean_mkpos(SU2KP_SRC, "q_canonical_upper")
    K = _lean_mkpos(SU2KP_SRC, "K_lf_canonical")
    assert q <= K * (1 - q)
    assert q < 1
    qw = _lean_mkpos(SU2KP_SRC, "q_wilson_upper")
    Kw = _lean_mkpos(SU2KP_SRC, "K_lf_wilson")
    assert qw <= Kw * (1 - qw)
    assert qw < 1


def test_lean_polymer_domination_K_lf_pilot_not_stale() -> None:
    """PolymerDomination.K_lf_pilot must also cover the true K_lf at the
    wire-in (it was 2/125 = 0.016 — sound pre-upgrade, UNSOUND after the
    μ_plaq flip; re-pinned to 7/125 = 0.056)."""
    kp = compute_large_field_kp(float(CANONICAL_G), t_choice=HeatKernelConvention.CANONICAL)
    k_lf_pilot = _lean_mkpos(POLYMER_SRC, "K_lf_pilot")
    assert float(k_lf_pilot) >= kp.K_lf
