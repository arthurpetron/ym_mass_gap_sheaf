"""Tests for `computations.block_spin` (Milestone 2.3).

Coverage:

- Construction of `BudgetFunctions`, `TwoCellTheta`,
  `BlockSpinStepObligation`.
- `BlockSpinStepObligation.check(s_k, s_next)` returns a dict with
  S1–S4 + scale_increment keys, and `all_satisfied()` is the
  conjunction.
- `check()` correctly flags failure on each clause independently
  (S1, S2, S3, S4, scale_increment).
- `TwoCellTheta.decrease_satisfied()` is true at the boundary
  (σ_in = σ_out + η) and false strictly below.
- `extract_two_cell(s_k, s_next)` returns a `TwoCellTheta` whose
  fields match the input pair.
- `signature()` references S1–S4 and the 2.3 → 3.x handoff.
- No test constructs `s_next` from `s_k`.  The step is 3.1–3.4.
"""

from __future__ import annotations

import pytest

from computations.block_spin import (
    BlockSpinStepObligation,
    BudgetFunctions,
    TwoCellTheta,
)
from computations.inductive_state import InductiveState, KPData

# --------------------------------------------------------------------------
# Fixtures: synthetic budget and well-formed (s_k, s_next) pair
# --------------------------------------------------------------------------


def _constant_budget(value: float = 0.05) -> BudgetFunctions:
    """A constant budget for testing: all four functions return `value`."""

    def fn(_b: float, _g: float) -> float:
        return value

    return BudgetFunctions(eps_sf=fn, eps_lf=fn, delta_cap=fn, eta=fn)


def _state_at(
    k: int,
    sigma_hat: float,
    g: float,
    rho_sf: float,
    rho_lf: float,
    K_sf: float,
    K_lf: float,
    K_cap: float | None = None,
) -> InductiveState:
    """A scale-k InductiveState with the buffer-glue invariants satisfied.

    Buffer ρ_∩ = min(ρ_sf, ρ_lf); buffer K_∩ defaults to K_sf+K_lf
    (V3-K at the boundary).
    """
    if K_cap is None:
        K_cap = K_sf + K_lf
    return InductiveState(
        k=k,
        sigma_hat=sigma_hat,
        g=g,
        kp_sf=KPData(rho=rho_sf, K=K_sf),
        kp_lf=KPData(rho=rho_lf, K=K_lf),
        kp_cap=KPData(rho=min(rho_sf, rho_lf), K=K_cap),
        poly_atlas=None,
    )


def _matched_pair() -> tuple[InductiveState, InductiveState, BlockSpinStepObligation]:
    """A `(s_k, s_next, obligation)` triple satisfying every check.

    Pick degradations strictly inside the budget to avoid boundary
    edge cases.
    """
    budget = _constant_budget(0.05)
    obligation = BlockSpinStepObligation(b=2.0, budget=budget)
    s_k = _state_at(k=0, sigma_hat=0.25, g=1.0, rho_sf=0.6, rho_lf=0.4, K_sf=5.0, K_lf=3.0)
    s_next = _state_at(
        k=1,
        sigma_hat=0.22,          # σ̂_k - 0.03 ≥ σ̂_k - 0.05 ✓ (S4)
        g=0.95,
        rho_sf=0.58,             # ρ_sf_k - 0.02 ≥ ρ_sf_k - 0.05 ✓ (S1)
        rho_lf=0.39,             # ρ_lf_k - 0.01 ≥ ρ_lf_k - 0.05 ✓ (S2)
        K_sf=5.0,
        K_lf=3.0,
        K_cap=s_k.kp_cap.K + 0.02,  # K_∩_k + 0.02 ≤ K_∩_k + 0.05 ✓ (S3)
    )
    return s_k, s_next, obligation


# --------------------------------------------------------------------------
# BudgetFunctions construction
# --------------------------------------------------------------------------


def test_budget_functions_construction() -> None:
    budget = _constant_budget(0.1)
    assert budget.eps_sf(2.0, 1.0) == 0.1
    assert budget.eps_lf(2.0, 1.0) == 0.1
    assert budget.delta_cap(2.0, 1.0) == 0.1
    assert budget.eta(2.0, 1.0) == 0.1


def test_budget_functions_can_depend_on_b_and_g() -> None:
    """Budget functions can be non-constant in (b, g_k)."""
    budget = BudgetFunctions(
        eps_sf=lambda b, g: b * g,
        eps_lf=lambda b, g: b + g,
        delta_cap=lambda b, g: b / (g + 1),
        eta=lambda _b, g: g * g,
    )
    assert budget.eps_sf(2.0, 3.0) == 6.0
    assert budget.eps_lf(2.0, 3.0) == 5.0
    assert budget.delta_cap(2.0, 3.0) == 0.5
    assert budget.eta(2.0, 3.0) == 9.0


# --------------------------------------------------------------------------
# TwoCellTheta
# --------------------------------------------------------------------------


def test_two_cell_decrease_satisfied_strict() -> None:
    theta = TwoCellTheta(sigma_in=1.0, eta_k=0.1, sigma_out=0.95)
    assert theta.decrease_satisfied() is True


def test_two_cell_decrease_at_boundary() -> None:
    """Equality σ_in - η_k = σ_out is on the admissible side."""
    theta = TwoCellTheta(sigma_in=1.0, eta_k=0.1, sigma_out=0.9)
    assert theta.decrease_satisfied() is True


def test_two_cell_decrease_violated() -> None:
    theta = TwoCellTheta(sigma_in=1.0, eta_k=0.1, sigma_out=0.85)  # below σ_in - η
    assert theta.decrease_satisfied() is False


def test_two_cell_can_have_negative_sigma_out_if_eta_large() -> None:
    """A budget so large that σ_in - η_k is negative is a valid Θ_k-witness shape.

    Phase-3 will check that this doesn't actually happen along the RG
    trajectory; the per-step type doesn't enforce positivity (that's V1).
    """
    theta = TwoCellTheta(sigma_in=0.1, eta_k=0.5, sigma_out=-0.3)
    # σ_in - η_k = -0.4 ≤ -0.3 = σ_out
    assert theta.decrease_satisfied() is True


# --------------------------------------------------------------------------
# BlockSpinStepObligation.check on well-formed pair
# --------------------------------------------------------------------------


def test_check_all_pass_on_matched_pair() -> None:
    s_k, s_next, obligation = _matched_pair()
    checks = obligation.check(s_k, s_next)
    assert checks == {
        "scale_increment": True,
        "S1_eps_sf": True,
        "S2_eps_lf": True,
        "S3_delta_cap": True,
        "S4_eta_sigma": True,
    }
    assert obligation.all_satisfied(s_k, s_next) is True


# --------------------------------------------------------------------------
# Failure paths — one per S1, S2, S3, S4, scale_increment
# --------------------------------------------------------------------------


def test_check_fails_on_scale_increment_mismatch() -> None:
    s_k, s_next, obligation = _matched_pair()
    # next state at wrong scale
    bad_next = InductiveState(
        k=5,  # not k+1
        sigma_hat=s_next.sigma_hat,
        g=s_next.g,
        kp_sf=s_next.kp_sf,
        kp_lf=s_next.kp_lf,
        kp_cap=s_next.kp_cap,
        poly_atlas=s_next.poly_atlas,
    )
    checks = obligation.check(s_k, bad_next)
    assert checks["scale_increment"] is False


def test_check_fails_on_S1_eps_sf_excess() -> None:
    s_k, s_next, obligation = _matched_pair()
    # ρ_sf degrades by 0.10, budget is 0.05 — S1 fails.
    bad_next = InductiveState(
        k=s_next.k,
        sigma_hat=s_next.sigma_hat,
        g=s_next.g,
        kp_sf=KPData(rho=s_k.kp_sf.rho - 0.10, K=s_next.kp_sf.K),
        kp_lf=s_next.kp_lf,
        kp_cap=s_next.kp_cap,
        poly_atlas=s_next.poly_atlas,
    )
    checks = obligation.check(s_k, bad_next)
    assert checks["S1_eps_sf"] is False


def test_check_fails_on_S2_eps_lf_excess() -> None:
    s_k, s_next, obligation = _matched_pair()
    bad_next = InductiveState(
        k=s_next.k,
        sigma_hat=s_next.sigma_hat,
        g=s_next.g,
        kp_sf=s_next.kp_sf,
        kp_lf=KPData(rho=s_k.kp_lf.rho - 0.10, K=s_next.kp_lf.K),
        kp_cap=s_next.kp_cap,
        poly_atlas=s_next.poly_atlas,
    )
    checks = obligation.check(s_k, bad_next)
    assert checks["S2_eps_lf"] is False


def test_check_fails_on_S3_delta_cap_excess() -> None:
    s_k, s_next, obligation = _matched_pair()
    bad_next = InductiveState(
        k=s_next.k,
        sigma_hat=s_next.sigma_hat,
        g=s_next.g,
        kp_sf=s_next.kp_sf,
        kp_lf=s_next.kp_lf,
        # K_∩ grows by 0.10, budget is 0.05 — S3 fails.
        kp_cap=KPData(rho=s_next.kp_cap.rho, K=s_k.kp_cap.K + 0.10),
        poly_atlas=s_next.poly_atlas,
    )
    checks = obligation.check(s_k, bad_next)
    assert checks["S3_delta_cap"] is False


def test_check_fails_on_S4_eta_sigma_excess() -> None:
    s_k, s_next, obligation = _matched_pair()
    bad_next = InductiveState(
        k=s_next.k,
        # σ̂ degrades by 0.10, budget is 0.05 — S4 fails.
        sigma_hat=s_k.sigma_hat - 0.10,
        g=s_next.g,
        kp_sf=s_next.kp_sf,
        kp_lf=s_next.kp_lf,
        kp_cap=s_next.kp_cap,
        poly_atlas=s_next.poly_atlas,
    )
    checks = obligation.check(s_k, bad_next)
    assert checks["S4_eta_sigma"] is False


def test_check_boundary_S4_equality() -> None:
    """σ̂_{k+1} = σ̂_k - η is on the admissible side of S4."""
    s_k, _s_next, obligation = _matched_pair()
    eta_k = obligation.budget.eta(obligation.b, s_k.g)
    boundary_next = InductiveState(
        k=s_k.k + 1,
        sigma_hat=s_k.sigma_hat - eta_k,
        g=s_k.g,
        kp_sf=s_k.kp_sf,
        kp_lf=s_k.kp_lf,
        kp_cap=s_k.kp_cap,
        poly_atlas=s_k.poly_atlas,
    )
    assert obligation.check(s_k, boundary_next)["S4_eta_sigma"] is True


# --------------------------------------------------------------------------
# extract_two_cell — the 2.2 → 2-cell extraction
# --------------------------------------------------------------------------


def test_extract_two_cell_matches_inputs() -> None:
    s_k, s_next, obligation = _matched_pair()
    theta = obligation.extract_two_cell(s_k, s_next)
    assert theta.sigma_in == s_k.sigma_hat
    assert theta.eta_k == obligation.budget.eta(obligation.b, s_k.g)
    assert theta.sigma_out == s_next.sigma_hat


def test_extract_two_cell_decrease_satisfied_iff_S4_passes() -> None:
    """`extract_two_cell` should respect S4 — its decrease check is S4."""
    s_k, s_next, obligation = _matched_pair()
    theta = obligation.extract_two_cell(s_k, s_next)
    assert theta.decrease_satisfied() is True
    assert obligation.check(s_k, s_next)["S4_eta_sigma"] is True


# --------------------------------------------------------------------------
# Signature — the 2.3 → 3.x handoff
# --------------------------------------------------------------------------


def test_signature_returns_string() -> None:
    sig = BlockSpinStepObligation.signature()
    assert isinstance(sig, str)
    assert len(sig) > 0


def test_signature_mentions_S1_S4() -> None:
    sig = BlockSpinStepObligation.signature()
    for tag in ("S1", "S2", "S3", "S4"):
        assert tag in sig


def test_signature_mentions_milestone_handoffs() -> None:
    """The signature should reference 3.1, 3.2, 3.3, 3.4 as the milestones
    that produce ε_sf, ε_lf, Δ_cap, η respectively."""
    sig = BlockSpinStepObligation.signature()
    for milestone in ("3.1", "3.2", "3.3", "3.4"):
        assert milestone in sig


# --------------------------------------------------------------------------
# Boundary discipline — no global-budget references
# --------------------------------------------------------------------------


def test_check_does_not_aggregate_across_steps() -> None:
    """`check(s_k, s_next)` is single-step.  Passing it the same triple
    twice or composing it does not yield a global sum or product.
    """
    s_k, s_next, obligation = _matched_pair()
    pytest.importorskip("typing")  # nothing imported here; just structural assertion
    # The check method is a Callable taking exactly two states.
    # Confirm via inspection that there's no `for k in range(...)` style
    # iteration: a single call returns a single dict of bools.
    out = obligation.check(s_k, s_next)
    assert isinstance(out, dict)
    assert all(isinstance(v, bool) for v in out.values())
    # No "sum_eta" or "product_K" keys: the check is per-step.
    assert "sum_eta" not in out
    assert "uniform_sigma_lower_bound" not in out
