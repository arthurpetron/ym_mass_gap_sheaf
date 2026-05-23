"""Large-field Kotecký–Preiss constants for SU(2).

Milestone 3.2 of `work_plan.md`.  Computes the large-field KP
certificate `(ρ_lf, K_lf)` for SU(2) at scale `k` from the
heat-kernel character expansion.

The large-field activity satisfies (per `docs/context.md` §3.1)

    |a_k^lf(X)|  ≤  exp(-ρ_lf · |X|_plaq),

where `|X|_plaq` is the plaquette count of `X` (lattice-combinatorial,
NOT the physical extent of the small-field bound).  The rate `ρ_lf`
is set by the Casimir gap `C_2(λ_1) - C_2(λ_0) = C_2(1/2) = 3/4` for
SU(2) (P1.1), times the convention factor from 1.2.

## Status: framework + placeholder

work_plan 3.2's open question:

> "Whether the character-expansion convergence radius is large enough
>  at realistic g_k, or whether resummation is needed."

This module delivers the FRAMEWORK with a placeholder rate
`ρ_lf = C_2(1/2)/g_k² = (3/4)/g_k²` in the canonical convention.  The
specific convergence-radius analysis (whether ρ_lf stays positive
across the RG trajectory, and whether the truncated character sum
suffices for the K_lf bound) is the deferred analytic content.

Mirror of `small_field_kp.py` (3.1) in shape: replacement happens
at `compute_large_field_kp` when the explicit derivation lands;
downstream consumers (3.3, 3.4, Lean `Obligation_lf` hook) do not
change.

## Structural independence from small-field

Per the [P2.3-addendum] encoded-but-unverified prediction (`Obligation_lf`
takes no `sf_part` input), the large-field derivation is structurally
independent of the small-field one.  Confirmed if the Bałaban-style
character-expansion analysis closes against the framework here
without needing 3.1's outputs.  If it doesn't, the [P2.3-addendum]
sf⊥lf prediction needs revisiting.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Final

from computations.heat_kernel import (
    C_2_SU2_FUNDAMENTAL,
    HeatKernelConvention,
    kappa_from_casimir,
)

# --------------------------------------------------------------------------
# Placeholder constants
# --------------------------------------------------------------------------

PLACEHOLDER_K_LF_BASE: Final[float] = 1.0
"""Placeholder amplitude K_lf at scale 0.

Bałaban-style polymer expansion gives K_lf as a cluster-expansion
combinatorial constant of order unity, depending on lattice
dimension and the polymer-counting function.  Placeholder = 1.0.
"""


# --------------------------------------------------------------------------
# Result dataclass
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class LargeFieldKP:
    """The large-field KP certificate (ρ_lf, K_lf) at one RG scale.

    Fields mirror SmallFieldKP, with `rho_lf` derived from the
    Casimir gap via the heat-kernel convention.
    """

    rho_lf: float
    K_lf: float
    g_k: float
    scale_k: int
    convention: HeatKernelConvention
    provenance: dict[str, str]


# --------------------------------------------------------------------------
# Compute the certificate
# --------------------------------------------------------------------------


def compute_large_field_kp(
    g_k: float,
    scale_k: int = 0,
    t_choice: HeatKernelConvention = HeatKernelConvention.CANONICAL,
    k_base: float | None = None,
) -> LargeFieldKP:
    """Compute `(ρ_lf, K_lf)` from the SU(2) character expansion.

    The rate `ρ_lf` uses the smallest nonzero Casimir
    `C_2(λ_1) = 3/4` (P1.1) lifted to the convention's `κ(G)/g_k²`:

      * Canonical: `ρ_lf = 3/4 / g_k²` (matches outline §18.5's κ_{SU(2)}).
      * Wilson:    `ρ_lf = 3   / g_k²` (Wilson's 2N · C_2 = 3).

    The amplitude `K_lf` is a placeholder (default 1.0).  Provenance
    records what is derived from 1.1/1.2 and what is placeholder.
    """
    if g_k <= 0:
        raise ValueError(f"g_k must be positive; got {g_k}")
    if scale_k < 0:
        raise ValueError(f"scale_k must be non-negative; got {scale_k}")
    if t_choice is HeatKernelConvention.MANTON:
        raise ValueError(
            "Manton's exp(-c g²) shape mismatches the large-field bound "
            "shape exp(-ρ/g²).  Use CANONICAL or WILSON."
        )

    # ρ_lf from the smallest nonzero Casimir via 1.2's machinery.
    kappa = kappa_from_casimir(
        C_2_min=float(C_2_SU2_FUNDAMENTAL), N=2, t_choice=t_choice
    )
    rho_lf = kappa / (g_k * g_k)

    k_base_eff = k_base if k_base is not None else PLACEHOLDER_K_LF_BASE

    provenance = {
        "rho_lf": (
            f"DERIVED FROM 1.1/1.2: κ({t_choice.value}) / g_k² "
            f"= {kappa:.4f} / {g_k:.4f}² = {rho_lf:.6e}. "
            f"κ from smallest nonzero Casimir C_2(1/2) = 3/4 via "
            f"heat_kernel.kappa_from_casimir under {t_choice.value}."
        ),
        "K_lf": (
            f"PLACEHOLDER: k_base = {k_base_eff:.4f}. "
            f"Character-expansion-residual amplitude — heuristic until "
            f"the explicit derivation lands."
        ),
        "convention": t_choice.value,
        "scale_k": str(scale_k),
        "status": "framework REAL; rho_lf derived from 1.1/1.2; K_lf placeholder",
    }

    return LargeFieldKP(
        rho_lf=rho_lf,
        K_lf=k_base_eff,
        g_k=g_k,
        scale_k=scale_k,
        convention=t_choice,
        provenance=provenance,
    )


# --------------------------------------------------------------------------
# Per-step degradation budget ε_lf
# --------------------------------------------------------------------------


def eps_lf(g_k: float, g_k_next: float, t_choice: HeatKernelConvention) -> float:
    """The per-step ε_lf budget: ρ_lf(k+1) ≥ ρ_lf(k) - ε_lf(b, g_k).

    Same shape as `small_field_kp.eps_sf`; sf and lf budgets are
    structurally independent per the [P2.3-addendum] prediction.
    """
    kp_k = compute_large_field_kp(g_k, t_choice=t_choice)
    kp_next = compute_large_field_kp(g_k_next, t_choice=t_choice)
    return max(0.0, kp_k.rho_lf - kp_next.rho_lf)


# --------------------------------------------------------------------------
# Trajectory
# --------------------------------------------------------------------------


def first_few_rg_steps(
    g_trajectory: list[float],
    t_choice: HeatKernelConvention = HeatKernelConvention.CANONICAL,
) -> list[LargeFieldKP]:
    """Compute the large-field KP certificate at each scale."""
    return [
        compute_large_field_kp(g, scale_k=k, t_choice=t_choice)
        for k, g in enumerate(g_trajectory)
    ]


if __name__ == "__main__":
    from computations.overlap_measure import standard_su2_trajectory

    traj = standard_su2_trajectory(k_max=5)
    g_traj: list[float] = traj[0]
    print("Large-field KP certificates for the standard SU(2) trajectory:")
    print(f"{'k':>3} {'g_k':>8} {'rho_lf':>12} {'K_lf':>8}")
    for kp in first_few_rg_steps(g_traj):
        print(f"{kp.scale_k:>3} {kp.g_k:>8.4f} {kp.rho_lf:>12.6f} {kp.K_lf:>8.4f}")
    print("\nProvenance (k=0):")
    sample = compute_large_field_kp(g_traj[0])
    for key, val in sample.provenance.items():
        print(f"  {key}: {val}")
