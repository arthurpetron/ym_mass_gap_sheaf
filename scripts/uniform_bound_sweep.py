"""U.4 — uniform parametric bound monotonicity sweep.

Tests the central strategy of `docs/uniform-parametric-bound-plan.md`: that
**SU(2) is the worst case** for the σ̂-budget, so the uniform bound over all
compact simple gauge groups reduces to monotonicity + the proven SU(2) closure.

For every simple type (A,B,C,D + G₂,F₄,E₆,E₇,E₈) at representative ranks, we
compute `Σ η(G)` by driving the *existing* generic KP/RG pipeline with that
group's invariants — `C₂(fund)` (small-field spectral gap), `h∨ = C₂(adj)`
(one-loop running `b₀ = (11/3)·h∨`), and the heat-kernel character sum
`Z_t = Σ dim(R)²e^{-t·C₂(R)}` (large-field), all from the validated
`computations.lie_algebras` engine — and check `Σ η(G) ≤ Σ η(SU(2))`.

Emits a table sorted by the spectral gap `Δ` and a chart `Σ η` vs `Δ`.
"""

from __future__ import annotations

import math

from computations import large_field_kp as lf
from computations.heat_kernel import HeatKernelConvention
from computations.lie_algebras import SimpleLie, character_Z, smallest_casimir, standard_zoo
from computations.sigma_hat_trajectory import sigma_hat_trajectory
from computations.small_field_kp import compute_small_field_kp
from computations.overlap_kp import compute_overlap_kp

CANON = HeatKernelConvention.CANONICAL
MU_PLAQ = lf.MU_PLAQUETTE_4D  # 16


def _make_Z(lie: SimpleLie):
    """A drop-in replacement for `heat_kernel_character_tail_Z` for this group."""
    def Z(g_k: float, t_choice, j_max_int: int = 0):
        t = 1.0 / (g_k * g_k)  # canonical
        z = character_Z(lie, t)
        return lf.CharacterTailSum(
            partial_sum=z, tail_bound=0.0, upper_bound=z,
            tail_ratio=0.0, tail_finite=True, j_max_int=0, t=t,
        )
    return Z


def _trajectory(k_max: int, g_0: float, h_vee: int, b: float = 2.0) -> list[float]:
    b_0 = (11.0 / 3.0) * h_vee
    log_b = math.log(b)
    inv0 = 1.0 / (g_0 * g_0)
    out: list[float] = []
    for k in range(k_max + 1):
        inv = inv0 - (b_0 / (16.0 * math.pi * math.pi)) * k * log_b
        if inv <= 0.0:
            break
        out.append(1.0 / math.sqrt(inv))
    return out


def run_group(lie: SimpleLie, g_0: float = 0.30, k: int = 3) -> dict:
    delta, _ = smallest_casimir(lie)
    c2_fund = delta  # smallest nonzero Casimir = the defining-rep gap
    lf.heat_kernel_character_tail_Z = _make_Z(lie)  # type: ignore[assignment]
    g_traj = _trajectory(k, g_0, lie.h_vee)
    traj = sigma_hat_trajectory(
        g_traj, sigma_hat_initial=1.0, t_choice=CANON,
        spectral_gap_coeff=c2_fund, mu_plaq=MU_PLAQ,
    )
    sf_ok = all(
        compute_small_field_kp(g, t_choice=CANON, spectral_gap_coeff=c2_fund).convergent
        for g in g_traj
    )
    lf_ok = all(
        compute_overlap_kp(g, t_choice=CANON, spectral_gap_coeff=c2_fund,
                           mu_plaq=MU_PLAQ).lf_part.convergent
        for g in g_traj
    )
    return {
        "name": lie.name, "rank": lie.rank, "delta": delta,
        "c2_fund": c2_fund, "h_vee": lie.h_vee,
        "total_eta": traj.total_eta, "sigma_K": traj.steps[-1].sigma_hat,
        "closes": traj.budget_closure, "sf": sf_ok, "lf": lf_ok,
    }


def main() -> None:
    zoo = standard_zoo()
    rows = [run_group(lie) for lie in zoo]
    su2 = next(r for r in rows if r["name"].startswith("A1"))
    eta_su2 = su2["total_eta"]

    rows.sort(key=lambda r: r["delta"])
    print("=" * 92)
    print("U.4 — uniform σ̂-budget sweep over all simple types (g_0=0.30, K=3, canonical)")
    print("=" * 92)
    print(f"  SU(2) reference:  Σ η = {eta_su2:.4e}   (worst case iff every row ≤ this)")
    print()
    print(f"  {'group':>12} {'Δ':>8} {'C2_adj=h∨':>9} {'Σ η':>12} "
          f"{'Ση/Ση(su2)':>11} {'≤su2?':>6} {'closes':>7}")
    worst = 0.0
    all_le = True
    for r in rows:
        ratio = r["total_eta"] / eta_su2
        le = r["total_eta"] <= eta_su2 * (1 + 1e-9)
        all_le = all_le and le
        worst = max(worst, r["total_eta"])
        print(f"  {r['name']:>12} {r['delta']:>8.4f} {r['h_vee']:>9} "
              f"{r['total_eta']:>12.4e} {ratio:>11.4f} {str(le):>6} {str(r['closes']):>7}")
    print()
    print(f"  VERDICT: every group's Σ η ≤ SU(2)'s : {all_le}")
    print(f"           worst-case Σ η over all groups = {worst:.4e}  (SU(2) = {eta_su2:.4e})")
    print(f"           SU(2) is the maximizer        : {abs(worst - eta_su2) < 1e-12}")

    # Robustness: SU(2) must remain the maximizer across the g_0 window
    # (guards the risk-register "non-monotone pocket near the convergence edge").
    print()
    print("  g_0 robustness — is SU(2) still the worst case across the window?")
    print(f"  {'g_0':>5} {'Ση(su2)':>12} {'max over others':>16} {'su2 worst?':>11}")
    robust = True
    for g0 in (0.20, 0.25, 0.30, 0.35, 0.40, 0.45):
        e2 = run_group(zoo[0], g_0=g0)["total_eta"]
        others = [run_group(l, g_0=g0)["total_eta"] for l in zoo[1:]]
        mx = max(others)
        ok = e2 >= mx * (1 - 1e-9)
        robust = robust and ok
        print(f"  {g0:>5.2f} {e2:>12.4e} {mx:>16.4e} {str(ok):>11}")
    print(f"\n  SU(2) is the worst case across the full g_0 window: {robust}")

    # data dump (provenance for the SVG)
    import json
    import os
    os.makedirs("visualizations/pilot/general", exist_ok=True)
    with open("visualizations/pilot/general/uniform-bound-sweep.json", "w") as f:
        json.dump({
            "operating_point": {"g_0": 0.30, "K": 3, "convention": "canonical",
                                "mu_plaq": MU_PLAQ},
            "su2_total_eta": eta_su2,
            "su2_is_worst_case": all_le,
            "rows": [{k: r[k] for k in ("name", "rank", "delta", "c2_fund",
                      "h_vee", "total_eta", "sigma_K", "closes", "sf", "lf")}
                     for r in rows],
        }, f, indent=2)
    print("  data:  visualizations/pilot/general/uniform-bound-sweep.json")

    # chart Σ η vs Δ
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt

        rs = sorted(rows, key=lambda r: r["delta"])
        xs = [r["delta"] for r in rs]
        ys = [r["total_eta"] for r in rs]
        fig, ax = plt.subplots(figsize=(8, 5))
        ax.scatter(xs, ys, c="tab:blue", zorder=3)
        for r in rs:
            ax.annotate(r["name"].split("=")[0], (r["delta"], r["total_eta"]),
                        fontsize=7, xytext=(3, 3), textcoords="offset points")
        ax.axhline(eta_su2, color="tab:red", ls="--", lw=1,
                   label=f"SU(2) worst case = {eta_su2:.2e}")
        ax.set_xlabel(r"spectral gap  $\Delta = C_2^{\min}$")
        ax.set_ylabel(r"$\Sigma_k\,\eta_k$  (budget consumed, $g_0=0.30$, K=3)")
        ax.set_yscale("log")
        ax.set_title("U.4: σ̂-budget vs spectral gap — SU(2) is the worst case")
        ax.legend()
        ax.grid(True, which="both", alpha=0.3)
        out = "visualizations/pilot/general/uniform-bound-sweep.svg"
        import os
        os.makedirs(os.path.dirname(out), exist_ok=True)
        fig.tight_layout()
        fig.savefig(out)
        print(f"\n  chart: {out}")
    except Exception as e:  # pragma: no cover
        print(f"\n  (chart skipped: {e})")


if __name__ == "__main__":
    main()
