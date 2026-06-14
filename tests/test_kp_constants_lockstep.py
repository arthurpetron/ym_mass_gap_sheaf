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
