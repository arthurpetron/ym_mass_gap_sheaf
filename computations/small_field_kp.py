"""Small-field Kotecký–Preiss constants for SU(2).

Milestone 3.1 of `work_plan.md`.  Computes the small-field KP
certificate `(ρ_sf, K_sf)` for SU(2) at scale `k`, as a function of
`g_k` and a polymer-atlas parameter.

The small-field activity satisfies (per `docs/context.md` §3.1)

    |a_k^sf(X)|  ≤  exp(-ρ_sf · |X|_phys / a_k)

where `|X|_phys / a_k` is the polymer's physical extent in lattice
units.  The KP summability over polymers containing a fixed plaquette
yields the certificate `(ρ_sf, K_sf)`.

## Status (work_plan 3.1 open question)

work_plan.md 3.1's open question:

> "This milestone requires either implementing the relevant pieces
>  of Bałaban's machinery for SU(2) or finding a sufficient citable
>  input. The choice affects the rest of Phase 3 substantially."

**This module delivers the FRAMEWORK and PLACEHOLDER constants**,
not a from-first-principles Bałaban derivation.  The shape of the
certificate, the typed integration with the `BlockSpinStepObligation`
of 2.3, and the cross-references to 1.2 (heat-kernel) and 1.4 (the
union-bound regime) are real and reusable.  The specific numerical
values of `(ρ_sf, K_sf)` are placeholders derived from the available
SU(2) constants (Casimirs, β-function coefficient `b_0 = 22/3`) plus
educated heuristics — clearly tagged in the returned object's
`provenance` field as ``placeholder``.

When the explicit Bałaban derivation is supplied (a future
follow-up, possibly an independent milestone), the function
``compute_small_field_kp`` is the single point of replacement; the
downstream integration (3.3, 3.4, 3.5, and the Lean
`Obligation_sf` hook) does not change.

## What downstream consumers can rely on

- The signature `compute_small_field_kp(g_k, scale_k, ...) → SmallFieldKP`.
- `SmallFieldKP.rho_sf > 0` always.
- `SmallFieldKP.K_sf ≥ 0` always.
- `SmallFieldKP.eps_sf(b, g_k_next, g_k_prev)` returning the per-step
  ε_sf degradation budget compatible with 2.3's S1 condition.
- The certificate at consecutive RG steps satisfies S1:
  ``ρ_sf(k+1) ≥ ρ_sf(k) - ε_sf(b, g_k)``.

## What downstream consumers must NOT rely on

- The specific NUMERICAL values of `ρ_sf` and `K_sf`.  These are
  placeholders; consuming code that depends on specific magnitudes
  is consuming the placeholder.  Provenance fields document this.

## Lean-side closure (deferred)

This module does not close the Lean `[P2.3-sf]` sorry.  Doing so
requires:
  1. The placeholder constants to be replaced by the actual Bałaban
     values (or at least a verifiable rational upper bound on them).
  2. A `Q'`-typed lift via `computations.heat_kernel.kappa_from_casimir_exact`.
  3. A Lean term inhabiting `Obligation_sf` constructed against the
     `Q'` values.
Item 1 is the analytic blocker; items 2 and 3 are mechanical once
item 1 lands.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Final

from computations.heat_kernel import (
    HeatKernelConvention,
)

# --------------------------------------------------------------------------
# Heuristic / placeholder constants
# --------------------------------------------------------------------------

PLACEHOLDER_RHO_SF_BASE: Final[Fraction] = Fraction(1, 2)
"""Placeholder base rate for ρ_sf at scale 0.

Heuristic: ρ_sf is bounded below by a fraction of the
spectral-gap scale for the small-field Laplacian Δ_k.  For SU(2),
the natural choice is some fraction of the Casimir C_2(1/2) = 3/4.
Without the actual Bałaban derivation, we conservatively set this
to 1/2 (slightly below 3/4) at g_k = 1 and scale it by 1/g_k² in
the canonical convention.

Replaceable: the entire numerical content is here.
"""

PLACEHOLDER_K_SF_BASE: Final[float] = 1.0
"""Placeholder base value for K_sf at scale 0.

In Bałaban's polymer expansion, K_sf is bounded by a constant
depending on the lattice dimension and the cluster-expansion
combinatorics, typically of order unity for short-range
small-field activities.  Placeholder = 1.0.
"""


# --------------------------------------------------------------------------
# Result dataclass
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class SmallFieldKP:
    """The small-field KP certificate (ρ_sf, K_sf) at one RG scale.

    Fields:
      * `rho_sf` — the small-field exponential-decay rate (positive).
      * `K_sf` — the polymer-summability amplitude (non-negative).
      * `g_k` — the gauge coupling at which the certificate is evaluated.
      * `scale_k` — the RG step index (0 = initial).
      * `convention` — the heat-kernel convention used to derive ρ_sf.
      * `provenance` — dict mapping each constant to its origin
        (formula, heuristic, placeholder status, etc.).

    The certificate satisfies the polymer KP inequality

        Σ_{X ∋ x} |a_k^sf(X)|(u) · exp(ρ_sf · |X|_phys / a_k)  ≤  K_sf

    in the small-field polymer expansion.  Specific verification
    against polymer activities is deferred (see module docstring).
    """

    rho_sf: float
    K_sf: float
    g_k: float
    scale_k: int
    convention: HeatKernelConvention
    provenance: dict[str, str]


# --------------------------------------------------------------------------
# Compute the certificate
# --------------------------------------------------------------------------


def compute_small_field_kp(
    g_k: float,
    scale_k: int = 0,
    t_choice: HeatKernelConvention = HeatKernelConvention.CANONICAL,
    rho_base: float | None = None,
    k_base: float | None = None,
) -> SmallFieldKP:
    """Compute `(ρ_sf, K_sf)` at the given coupling and RG scale.

    PLACEHOLDER: the numerical content of this function is heuristic.
    See module docstring for the status.

    Default heuristic:
      ρ_sf(g_k) = `rho_base` / g_k²   in canonical convention,
                  scaled by the (2N) factor for Wilson.
      K_sf      = `k_base`            (g_k-independent in the placeholder).

    `rho_base` defaults to `PLACEHOLDER_RHO_SF_BASE`;
    `k_base` defaults to `PLACEHOLDER_K_SF_BASE`.
    """
    if g_k <= 0:
        raise ValueError(f"g_k must be positive; got {g_k}")
    if scale_k < 0:
        raise ValueError(f"scale_k must be non-negative; got {scale_k}")
    if t_choice is HeatKernelConvention.MANTON:
        raise ValueError(
            "Manton convention's bound shape is exp(-c g²); the small-field "
            "framework here is exp(-ρ/g²) shape.  Use CANONICAL or WILSON."
        )

    rho_base_eff = rho_base if rho_base is not None else float(PLACEHOLDER_RHO_SF_BASE)
    k_base_eff = k_base if k_base is not None else PLACEHOLDER_K_SF_BASE

    # Canonical: ρ_sf = rho_base / g_k² (the natural shape for the
    # small-field activity exp(-ρ_sf / g_k²)).
    # Wilson: scaled by 2N = 4 for SU(2).
    if t_choice is HeatKernelConvention.WILSON:
        rho_factor = 4.0
    elif t_choice is HeatKernelConvention.CANONICAL:
        rho_factor = 1.0
    else:
        raise ValueError(f"unknown convention: {t_choice!r}")

    rho_sf = rho_factor * rho_base_eff / (g_k * g_k)
    K_sf = k_base_eff

    provenance = {
        "rho_sf": (
            f"PLACEHOLDER: rho_base · ({rho_factor}) / g_k² "
            f"= {rho_base_eff:.4f} · {rho_factor} / {g_k:.4f}² = {rho_sf:.6e}. "
            f"Heuristic; replaced when Bałaban small-field derivation lands."
        ),
        "K_sf": (
            f"PLACEHOLDER: k_base = {k_base_eff:.4f}. "
            f"Heuristic; will be replaced with the actual cluster-expansion bound."
        ),
        "convention": f"{t_choice.value}; rho_factor = {rho_factor}",
        "scale_k": str(scale_k),
        "status": "placeholder — see computations/small_field_kp.py module docstring",
    }

    return SmallFieldKP(
        rho_sf=rho_sf,
        K_sf=K_sf,
        g_k=g_k,
        scale_k=scale_k,
        convention=t_choice,
        provenance=provenance,
    )


# --------------------------------------------------------------------------
# Per-step degradation budget ε_sf (the 2.3 S1 ingredient)
# --------------------------------------------------------------------------


def eps_sf(g_k: float, g_k_next: float, t_choice: HeatKernelConvention) -> float:
    """The per-step ε_sf budget: ρ_sf(k) - ρ_sf(k+1) ≤ ε_sf(b, g_k).

    PLACEHOLDER.  Computed as the difference of the placeholder rates
    at consecutive scales:

        ε_sf(g_k, g_{k+1}) = max(0, ρ_sf(g_k) - ρ_sf(g_{k+1})).

    For the canonical placeholder ``ρ_sf = ρ_base / g_k²`` and
    ``g_{k+1} > g_k`` (confinement direction), ε_sf > 0.

    Used by 2.3's `Obligation_sf` and 3.4's η-budget aggregation.
    """
    kp_k = compute_small_field_kp(g_k, t_choice=t_choice)
    kp_next = compute_small_field_kp(g_k_next, t_choice=t_choice)
    return max(0.0, kp_k.rho_sf - kp_next.rho_sf)


# --------------------------------------------------------------------------
# Numerical values for the first few RG steps (work_plan 3.1 deliverable)
# --------------------------------------------------------------------------


def first_few_rg_steps(
    g_trajectory: list[float],
    t_choice: HeatKernelConvention = HeatKernelConvention.CANONICAL,
) -> list[SmallFieldKP]:
    """Compute the small-field KP certificate at each scale in the trajectory."""
    return [
        compute_small_field_kp(g, scale_k=k, t_choice=t_choice)
        for k, g in enumerate(g_trajectory)
    ]


if __name__ == "__main__":
    from computations.overlap_measure import standard_su2_trajectory

    traj = standard_su2_trajectory(k_max=5)
    g_traj: list[float] = traj[0]
    print("Small-field KP certificates for the standard SU(2) trajectory:")
    print(f"{'k':>3} {'g_k':>8} {'rho_sf':>12} {'K_sf':>8}")
    for kp in first_few_rg_steps(g_traj):
        print(f"{kp.scale_k:>3} {kp.g_k:>8.4f} {kp.rho_sf:>12.6f} {kp.K_sf:>8.4f}")
    print("\nProvenance (k=0):")
    sample = compute_small_field_kp(g_traj[0])
    for key, val in sample.provenance.items():
        print(f"  {key}: {val}")
