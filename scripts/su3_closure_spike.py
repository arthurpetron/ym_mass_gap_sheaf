"""SU(3) inductive-step closure spike — non-invasive go/no-go.

Feeds SU(3) group constants into the EXISTING generic KP/RG machinery to test
whether the σ̂-budget Σ_k η_k < σ̂_0 closes for SU(3), WITHOUT modifying any
SU(2) production module.  The pipeline already threads the small-field
spectral-gap coefficient (c_λ) and the plaquette connectivity (μ_plaq) as
overrides; the ONLY SU(2)-hardcoded piece is the large-field heat-kernel
character sum Z_t (a sum over half-integer spins).  We monkeypatch that single
function with the SU(3) character sum over (p, q) irreps and drive the existing
`sigma_hat_trajectory`.

SU(3) constants (standard quadratic-Casimir normalization, matching the SU(2)
code where C_2(fund) = j(j+1) = 3/4):
  * C_2(fundamental (1,0)) = 4/3   -> small-field spectral_gap_coeff (c_λ)
  * C_2(adjoint    (1,1))  = 3     -> one-loop b_0 = (11/3)·C_2(adj) = 11
  * dim(p,q)  = (p+1)(q+1)(p+q+2)/2
  * C_2(p,q)  = (p² + q² + p q + 3p + 3q) / 3
  * μ_plaq    = 16  (4D plaquette connectivity; group-independent)

The large-field weight mirrors the SU(2) convention exactly: Z_t = Σ_R dim(R)²
exp(-t · C_2(R)) over nontrivial irreps R.

This is a SPIKE: the SU(3) Z_t is a high-order truncation (no rigorous
geometric tail bound yet) — adequate for go/no-go, not for the eventual Lean
wire-in.
"""

from __future__ import annotations

import math

from computations import large_field_kp as lf
from computations.heat_kernel import HeatKernelConvention
from computations.overlap_kp import compute_overlap_kp
from computations.sigma_hat_trajectory import sigma_hat_trajectory
from computations.small_field_kp import (
    MU_CONNECTIVITY_4D,
    compute_small_field_kp,
)

CANON = HeatKernelConvention.CANONICAL

C2_FUND_SU3 = 4.0 / 3.0
C2_ADJ_SU3 = 3.0
N_SU3 = 3
MU_PLAQ = lf.MU_PLAQUETTE_4D  # 16, dimensional


def su3_dim(p: int, q: int) -> int:
    return (p + 1) * (q + 1) * (p + q + 2) // 2


def su3_casimir(p: int, q: int) -> float:
    return (p * p + q * q + p * q + 3 * p + 3 * q) / 3.0


def su3_character_tail_Z(
    g_k: float,
    t_choice: HeatKernelConvention,
    j_max_int: int = 40,
) -> lf.CharacterTailSum:
    """SU(3) analogue of `heat_kernel_character_tail_Z`.

    Z_t = Σ_{(p,q)≠(0,0)} dim(p,q)² · exp(-t · C_2(p,q)), truncated at
    p,q ≤ j_max_int (the tail is negligible here, < 1e-12, for the t of
    interest — a rigorous geometric bound is deferred to the real port).
    """
    if t_choice is CANON:
        t = 1.0 / (g_k * g_k)
    elif t_choice is HeatKernelConvention.WILSON:
        t = 2.0 * N_SU3 / (g_k * g_k)  # 2N = 6
    else:
        raise ValueError("Manton not supported")
    partial = 0.0
    p_max = j_max_int
    for p in range(p_max + 1):
        for q in range(p_max + 1):
            if p == 0 and q == 0:
                continue
            d = su3_dim(p, q)
            partial += (d * d) * math.exp(-t * su3_casimir(p, q))
    return lf.CharacterTailSum(
        partial_sum=partial,
        tail_bound=0.0,
        upper_bound=partial,
        tail_ratio=0.0,
        tail_finite=True,
        j_max_int=p_max,
        t=t,
    )


def su3_trajectory(k_max: int, g_0: float, b: float = 2.0) -> list[float]:
    """SU(3) one-loop RG flow: b_0 = (11/3)·C_2(adj) = 11 (vs 22/3 for SU(2))."""
    b_0 = (11.0 / 3.0) * C2_ADJ_SU3
    log_b = math.log(b)
    inv_g_sq_0 = 1.0 / (g_0 * g_0)
    g_traj: list[float] = []
    for k in range(k_max + 1):
        inv = inv_g_sq_0 - (b_0 / (16.0 * math.pi * math.pi)) * k * log_b
        if inv <= 0.0:
            break
        g_traj.append(1.0 / math.sqrt(inv))
    return g_traj


def threshold_g_lf_su3() -> float:
    """Largest g with q = μ_plaq·Z_t < 1 (large-field convergence), bisection."""
    lo, hi = 1e-3, 2.0
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        ok = compute_overlap_kp(
            mid, t_choice=CANON, spectral_gap_coeff=C2_FUND_SU3, mu_plaq=MU_PLAQ
        )
        if math.isfinite(ok.lf_part.K_lf):
            lo = mid
        else:
            hi = mid
    return lo


def threshold_g_sf_su3() -> float:
    """g where ρ_sf = c_λ/g² = μ_connectivity: √(c_λ / log(8e))."""
    return math.sqrt(C2_FUND_SU3 / MU_CONNECTIVITY_4D)


def run(g_0: float, k: int = 3) -> dict[str, float | bool | int]:
    g_traj = su3_trajectory(k, g_0)
    traj = sigma_hat_trajectory(
        g_traj,
        sigma_hat_initial=1.0,
        t_choice=CANON,
        spectral_gap_coeff=C2_FUND_SU3,
        mu_plaq=MU_PLAQ,
    )
    sf_ok = all(
        compute_small_field_kp(g, t_choice=CANON, spectral_gap_coeff=C2_FUND_SU3).convergent
        for g in g_traj
    )
    lf_ok = all(
        compute_overlap_kp(g, t_choice=CANON, spectral_gap_coeff=C2_FUND_SU3, mu_plaq=MU_PLAQ).lf_part.convergent
        for g in g_traj
    )
    sigma_K = traj.steps[-1].sigma_hat
    return {
        "g_0": g_0,
        "len": len(g_traj),
        "sf_conv": sf_ok,
        "lf_conv": lf_ok,
        "total_eta": traj.total_eta,
        "sigma_K": sigma_K,
        "closes": traj.budget_closure,
        "m_0_bound": math.sqrt(sigma_K) if sigma_K > 0 else float("nan"),
    }


if __name__ == "__main__":
    # Install the SU(3) character sum into the otherwise-generic pipeline.
    lf.heat_kernel_character_tail_Z = su3_character_tail_Z  # type: ignore[assignment]

    print("=" * 72)
    print("SU(3) inductive-step closure spike (canonical convention, K=3)")
    print("=" * 72)
    print(f"  C_2(fund) = {C2_FUND_SU3:.4f}   C_2(adj) = {C2_ADJ_SU3}   b_0 = 11")
    print(f"  small-field convergence threshold g_max_sf = {threshold_g_sf_su3():.4f}")
    print(f"  large-field convergence threshold g_max_lf = {threshold_g_lf_su3():.4f}")
    print()
    print(f"  {'g_0':>5} {'#g':>3} {'sf':>5} {'lf':>5} {'Σ η':>12} "
          f"{'σ̂_K':>10} {'m_0≳√σ̂_K':>10} {'closes':>7}")
    for g_0 in (0.20, 0.25, 0.30, 0.35, 0.40, 0.45, 0.50):
        r = run(g_0)
        print(f"  {r['g_0']:>5.2f} {r['len']:>3d} {str(r['sf_conv']):>5} "
              f"{str(r['lf_conv']):>5} {r['total_eta']:>12.4e} "
              f"{r['sigma_K']:>10.5f} {r['m_0_bound']:>10.5f} {str(r['closes']):>7}")
    print()
    print("  (m_0 is the implied lattice mass-gap lower bound √σ̂_K in units of √σ_0;")
    print("   the SU(2) canonical pilot at g_0=0.30 gives Σ η≈7.95e-4, m_0≈0.9996.)")
