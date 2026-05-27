"""Explicit constructive lower bound `m_0` on the SU(2) mass gap.

Milestone 9.1 of `work_plan.md`.  Computes the explicit Q'-rational
lower bound on the SU(2) mass gap m from the Phase-3 pilot numerics,
via the composition:

  σ̂_∞ ≥ ε > 0       (Phase 7.1 framework theorem)
  ⇒ OS4 cluster with rate ε    (Phase 8.1)
  ⇒ spectral gap of H_op ≥ ε    (Phase 8.2 cluster-to-gap bridge)
  ⇒ m := inf σ_+(H_op) ≥ √ε    (dimensional rate → mass identification)

The output is a `MassGapBound` carrying the explicit Q'-rational
`m_0_numerator / m_0_denominator` ≤ m, together with all the
intermediate quantities for audit + Lean wire-in.

# The bound at the project's default operating points

  * **Canonical** (g_0 = 0.30, K = 3, denominator 10000):
      σ̂_∞ ≥ 9967 / 10000  ≈ 0.9967
      m ≥ √(9967/10000) ≈ 0.998348
      m_0_canonical := 998 / 1000   (with m_0² = 0.996004 ≤ 0.9967 ✓)
  * **Wilson** (g_0 = 0.50, K = 3, denominator 10000):
      σ̂_∞ ≥ 9988 / 10000  ≈ 0.9988
      m ≥ √(9988/10000) ≈ 0.999399
      m_0_wilson := 999 / 1000      (with m_0² = 0.998001 ≤ 0.9988 ✓)

Both bounds match the Phase-3 SigmaHatPilot Lean module's pilot
rational constants (`eta_max_pilot`, `eta_total_pilot`, etc.) by
construction; a regression test
(`tests/test_mass_gap_bound.py::test_pilot_data_matches_lean_module`)
enforces lockstep.

# References

- `formal/mass-gap-theorem.tex` (Milestone 9.1, primary deliverable).
- `notes/mass-gap-theorem.md` (Milestone 9.1 prose).
- `computations/q_lift.py::pilot_eta_rational_bound` (Phase-3
  pilot data).
- `lean/YMGap/Continuum/SigmaHatLimit.lean` (Phase 7.1 framework
  theorem).
"""

from __future__ import annotations

import math
from dataclasses import dataclass

from computations.heat_kernel import HeatKernelConvention
from computations.q_lift import pilot_eta_rational_bound


# --------------------------------------------------------------------------
# Result dataclass
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class MassGapBound:
    """The explicit constructive lower bound `m_0 ≤ m` on the SU(2) mass gap.

    Fields:
      * `m_0_numerator`, `m_0_denominator`: the Q'-rational lower bound.
        `m_0 := m_0_numerator / m_0_denominator > 0` in dimensionless
        units where `σ_0^{1/2} = 1` at lattice scale 0.
      * `sigma_hat_inf_lower_num`, `sigma_hat_inf_lower_den`: the
        explicit `σ̂_∞ ≥ ε := σ̂_0 - eta_total` lower bound (Q'-rational).
      * `m_0_squared_num`, `m_0_squared_den`: (m_0)² as a Q'-rational
        (for the decidable check `m_0² ≤ σ̂_∞`).
      * `bound_check_passes`: True iff `m_0² ≤ σ̂_∞` (the witness condition).
      * `eta_total_numerator`, `eta_total_denominator`: the upstream
        Phase-3 pilot's total η consumed across K transitions.
      * `convention`: heat-kernel convention (canonical or Wilson).
      * `g_0`, `K`: the pilot operating point.
      * `m_0_float`: float approximation of m_0 (for display/plotting only;
        the rigorous Q'-rational fields are the witness).
    """

    m_0_numerator: int
    m_0_denominator: int
    sigma_hat_inf_lower_num: int
    sigma_hat_inf_lower_den: int
    m_0_squared_num: int
    m_0_squared_den: int
    bound_check_passes: bool
    eta_total_numerator: int
    eta_total_denominator: int
    convention: HeatKernelConvention
    g_0: float
    K: int
    m_0_float: float


# --------------------------------------------------------------------------
# Helpers
# --------------------------------------------------------------------------


def _cross_product_le(a_num: int, a_den: int, b_num: int, b_den: int) -> bool:
    """Decidable Q'-rational `(a_num/a_den) ≤ (b_num/b_den)` via cross-product.

    Requires both denominators positive.  Returns
    `a_num · b_den ≤ b_num · a_den`.
    """
    if a_den <= 0 or b_den <= 0:
        raise ValueError(
            f"denominators must be positive; got a_den={a_den}, b_den={b_den}"
        )
    return a_num * b_den <= b_num * a_den


# --------------------------------------------------------------------------
# Bound derivation
# --------------------------------------------------------------------------


def derive_mass_gap_bound(
    g_0: float = 0.30,
    K: int = 3,
    convention: HeatKernelConvention = HeatKernelConvention.CANONICAL,
    denominator: int = 10000,
    sigma_hat_initial: float = 1.0,
    m_0_denominator: int = 1000,
    use_chaining: bool = False,
    chain_n_share: int | None = None,
    chain_zeta: float | None = None,
) -> MassGapBound:
    """Derive the explicit Q'-rational mass-gap lower bound from pilot numerics.

    Pipeline:
      1. Run `pilot_eta_rational_bound(g_0, K, convention, denominator)`
         to get `eta_total_numerator / denominator ≤ Σ η_k`.
      2. Compute `σ̂_∞ ≥ ε := σ̂_0 - eta_total`, expressed as
         `(σ̂_0_num · denominator - eta_total_num) / denominator`
         (with σ̂_0 = sigma_hat_initial = 1 → numerator = denominator).
      3. Find the largest `m_0_numerator` such that
         `(m_0_numerator / m_0_denominator)² ≤ ε`.  The cross-product
         decidable check is `m_0_num² · σ̂_∞_den ≤ σ̂_∞_num · m_0_den²`.

    The `m_0_denominator = 1000` default gives a 3-significant-digit
    rational lower bound suitable for the explicit constructive form
    of the SU(2) mass-gap theorem statement.

    For sensitivity sweeps, override `m_0_denominator` (larger →
    finer-grained m_0 search).
    """
    if g_0 <= 0:
        raise ValueError(f"g_0 must be positive; got {g_0}")
    if K < 1:
        raise ValueError(f"K must be ≥ 1; got {K}")
    if denominator < 1:
        raise ValueError(f"denominator must be ≥ 1; got {denominator}")
    if m_0_denominator < 1:
        raise ValueError(f"m_0_denominator must be ≥ 1; got {m_0_denominator}")
    if sigma_hat_initial <= 0:
        raise ValueError(
            f"sigma_hat_initial must be positive; got {sigma_hat_initial}"
        )

    # Step 1: pilot data.
    pilot = pilot_eta_rational_bound(
        g_0=g_0, K=K, convention=convention,
        denominator=denominator,
        sigma_hat_initial=sigma_hat_initial,
        use_chaining=use_chaining,
        chain_n_share=chain_n_share,
        chain_zeta=chain_zeta,
    )

    # Step 2: σ̂_∞ ≥ ε.  With σ̂_0 = 1 = denominator/denominator,
    # ε = (denominator - eta_total_num) / denominator.
    sigma_hat_initial_num = int(round(sigma_hat_initial * denominator))
    epsilon_num = sigma_hat_initial_num - pilot.eta_total_numerator
    epsilon_den = denominator
    if epsilon_num <= 0:
        raise RuntimeError(
            f"σ̂_∞ lower bound is non-positive at the requested operating "
            f"point (g_0={g_0}, K={K}, convention={convention.value}): "
            f"σ̂_0={sigma_hat_initial}, eta_total={pilot.eta_total_numerator}/"
            f"{denominator}, ε={epsilon_num}/{epsilon_den}. Phase 9.1 "
            f"mass-gap bound requires a STRICT budget closure σ̂_0 > Σ η."
        )

    # Step 3: find largest m_0_num with (m_0_num/m_0_den)² ≤ ε.
    # Search bound: m_0_num ≤ m_0_denominator (since m_0 ≤ 1 in natural units).
    m_0_num = 0
    for candidate_num in range(m_0_denominator + 1):
        m_0_sq_num = candidate_num * candidate_num
        m_0_sq_den = m_0_denominator * m_0_denominator
        if _cross_product_le(m_0_sq_num, m_0_sq_den, epsilon_num, epsilon_den):
            m_0_num = candidate_num
        else:
            break
    if m_0_num == 0:
        raise RuntimeError(
            f"No positive m_0 satisfies (m_0)² ≤ ε at m_0_denominator="
            f"{m_0_denominator}. ε = {epsilon_num}/{epsilon_den} may be "
            f"too small for this denominator; try larger m_0_denominator."
        )

    m_0_sq_num = m_0_num * m_0_num
    m_0_sq_den = m_0_denominator * m_0_denominator
    bound_check = _cross_product_le(
        m_0_sq_num, m_0_sq_den, epsilon_num, epsilon_den
    )

    return MassGapBound(
        m_0_numerator=m_0_num,
        m_0_denominator=m_0_denominator,
        sigma_hat_inf_lower_num=epsilon_num,
        sigma_hat_inf_lower_den=epsilon_den,
        m_0_squared_num=m_0_sq_num,
        m_0_squared_den=m_0_sq_den,
        bound_check_passes=bound_check,
        eta_total_numerator=pilot.eta_total_numerator,
        eta_total_denominator=denominator,
        convention=convention,
        g_0=g_0,
        K=K,
        m_0_float=m_0_num / m_0_denominator,
    )


# --------------------------------------------------------------------------
# Default-operating-point convenience wrappers
# --------------------------------------------------------------------------


def canonical_mass_gap_bound() -> MassGapBound:
    """The canonical-pilot mass-gap bound: m_0 = 998/1000 from g_0=0.30, K=3.

    Default Phase-9.1 operating point.  Matches the bound recorded in
    `formal/mass-gap-theorem.tex` Proposition 3.1.
    """
    return derive_mass_gap_bound(
        g_0=0.30, K=3,
        convention=HeatKernelConvention.CANONICAL,
        denominator=10000,
        m_0_denominator=1000,
    )


def wilson_mass_gap_bound() -> MassGapBound:
    """The Wilson-pilot mass-gap bound: m_0 = 999/1000 from g_0=0.50, K=3.

    Default Phase-9.1 Wilson operating point.  Matches the bound recorded
    in `formal/mass-gap-theorem.tex` Proposition 3.2.
    """
    return derive_mass_gap_bound(
        g_0=0.50, K=3,
        convention=HeatKernelConvention.WILSON,
        denominator=10000,
        m_0_denominator=1000,
    )


# --------------------------------------------------------------------------
# Display
# --------------------------------------------------------------------------


def format_mass_gap_bound(bound: MassGapBound) -> str:
    """Multi-line summary of a `MassGapBound` suitable for stdout."""
    lines = [
        f"  convention:                {bound.convention.value}",
        f"  pilot operating point:     g_0 = {bound.g_0}, K = {bound.K}",
        f"  Σ η_k consumed:            {bound.eta_total_numerator}/"
        f"{bound.eta_total_denominator}",
        f"  σ̂_∞ lower bound (ε):       "
        f"{bound.sigma_hat_inf_lower_num}/{bound.sigma_hat_inf_lower_den}"
        f"  ≈ {bound.sigma_hat_inf_lower_num / bound.sigma_hat_inf_lower_den}",
        f"  m_0 (Q'-rational):         "
        f"{bound.m_0_numerator}/{bound.m_0_denominator}"
        f"  ≈ {bound.m_0_float}",
        f"  m_0² (Q'-rational):        "
        f"{bound.m_0_squared_num}/{bound.m_0_squared_den}"
        f"  ≈ {bound.m_0_squared_num / bound.m_0_squared_den}",
        f"  bound check (m_0² ≤ ε):    {bound.bound_check_passes}",
    ]
    return "\n".join(lines)


if __name__ == "__main__":
    print("SU(2) mass-gap explicit constructive lower bound m_0 ≤ m")
    print("=" * 60)
    print()
    print("Canonical convention:")
    print(format_mass_gap_bound(canonical_mass_gap_bound()))
    print()
    print("Wilson convention:")
    print(format_mass_gap_bound(wilson_mass_gap_bound()))
    print()
    print("Sensitivity: m_0_denominator sweep (canonical):")
    print(f"{'denom':>8} {'m_0_num':>10} {'m_0 float':>12}")
    for d in [100, 1000, 10_000, 100_000]:
        b = derive_mass_gap_bound(
            g_0=0.30, K=3,
            convention=HeatKernelConvention.CANONICAL,
            denominator=10000,
            m_0_denominator=d,
        )
        print(f"{d:>8} {b.m_0_numerator:>10} {b.m_0_float:>12.6f}")
