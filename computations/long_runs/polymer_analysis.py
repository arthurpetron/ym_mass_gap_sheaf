"""Analyze the 4D plaquette polymer enumeration from the Rust `polymer_sum`.

Reads the JSON (per-size connected-animal counts N(n)) and:
  1. extrapolates the growth constant mu_inf = lim ln(N(n)/N(n-1)) via a
     1/n fit, and compares to the cluster-expansion bound
     mu_conn = log(2d e) = log(8e) ~ 3.0794 used in small-field-kp.tex;
  2. translates the result into the impact on the small-field convergent
     threshold g_max^sf = sqrt(c_lambda * kappa / mu) (canonical c_lambda=3/4,
     kappa=1); and
  3. plots mu_emp(n) with the bound and the extrapolated limit.

The headline question: does the empirical plaquette-polymer growth constant
respect the manuscript's mu_conn, and if not, by how much (and what does that
do to the convergent regime / the mass gap)?

Usage:
    python -m computations.long_runs.polymer_analysis visualizations/pilot/su2/polymer-sum-max8.json
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import numpy as np

MU_CONN = math.log(8 * math.e)  # log(2d e), d=4  ~ 3.0794
C_LAMBDA = 0.75                 # canonical Casimir gap
KAPPA = 1.0                     # canonical convention factor


def g_max_sf(mu: float) -> float:
    return math.sqrt(C_LAMBDA * KAPPA / mu)


def main() -> None:
    p = argparse.ArgumentParser(description="4D plaquette polymer-growth analysis.")
    p.add_argument("json")
    p.add_argument("--plot", default=None)
    args = p.parse_args()

    d = json.loads(Path(args.json).read_text())
    counts = np.asarray(d["counts"], dtype=float)  # N(1..max)
    ns = np.arange(1, len(counts) + 1)
    ratios = counts[1:] / counts[:-1]              # N(n)/N(n-1), n=2..max
    mu = np.log(ratios)                            # mu_emp(n), n=2..max
    nr = ns[1:]                                    # n values for ratios

    # Extrapolate mu_emp(n) = mu_inf - a/n  (linear in 1/n) over the larger n.
    use = nr >= max(3, nr.max() - 4)
    A = np.vstack([np.ones(use.sum()), 1.0 / nr[use]]).T
    coef, *_ = np.linalg.lstsq(A, mu[use], rcond=None)
    mu_inf, a = float(coef[0]), float(coef[1])

    print(f"=== 4D plaquette polymer growth (max size {len(counts)}) ===")
    print("   n   N(n)            N(n)/N(n-1)   mu_emp")
    print(f"   1   {int(counts[0]):<14}  --            --")
    for i, n in enumerate(nr):
        print(f"  {int(n):>2}   {int(counts[i+1]):<14}  {ratios[i]:>8.4f}      {mu[i]:.4f}")
    print(f"\n  extrapolated growth: mu_inf = {mu_inf:.4f} (lambda = {math.exp(mu_inf):.2f})")
    print(f"  manuscript bound:    mu_conn = log(8e) = {MU_CONN:.4f} (8e = {8*math.e:.2f})")
    if mu_inf > MU_CONN:
        print(f"  => FINDING: empirical growth EXCEEDS mu_conn by {mu_inf - MU_CONN:.4f}")
        print(f"     (share-a-link plaquette graph, coordination 20, vs the 2d=8 in mu_conn).")
        print(f"  Impact on the convergent threshold g_max^sf = sqrt(c_lambda*kappa/mu):")
        print(f"     with mu_conn:  g_max^sf = {g_max_sf(MU_CONN):.4f}")
        print(f"     with mu_inf:   g_max^sf = {g_max_sf(mu_inf):.4f}   (shrinks by {g_max_sf(MU_CONN)-g_max_sf(mu_inf):.4f})")
        print(f"  Mass gap: SAFE. Canonical g_0=0.30 << g_max^sf~{g_max_sf(mu_inf):.2f};")
        print(f"      rho_sf = c_lambda*kappa/g_0^2 = {C_LAMBDA*KAPPA/0.09:.2f} >> mu_inf, so the")
        print(f"     KP expansion still converges with large margin -- only the *stated*")
        print(f"     convergent-regime constant needs the larger mu.")
    else:
        print(f"  => bound HOLDS: mu_inf <= mu_conn (margin {MU_CONN - mu_inf:.4f}).")

    print(f"\n  conjecture 7.4 union looseness (polymer level): {d.get('union_looseness', float('nan')):.4f}")
    print(f"     (K-level empirical reference: 1.014 at g_0=0.30, <= 1.176 across the regime)")

    # Plot
    out = args.plot or str(Path(args.json).with_suffix(".svg"))
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig, ax = plt.subplots(figsize=(8.0, 5.0))
    ax.plot(nr, mu, "o-", color="tab:blue", label=r"$\mu_{\mathrm{emp}}(n)=\ln[N(n)/N(n-1)]$")
    xx = np.linspace(nr.min(), nr.max() + 3, 100)
    ax.plot(xx, mu_inf - a / xx, "--", color="tab:blue", alpha=0.6,
            label=fr"fit $\mu_\infty - a/n$, $\mu_\infty={mu_inf:.3f}$")
    ax.axhline(mu_inf, color="tab:blue", linestyle=":", alpha=0.5)
    ax.axhline(MU_CONN, color="tab:red", linestyle="-", linewidth=1.5,
               label=fr"$\mu_{{\mathrm{{conn}}}}=\log(8e)={MU_CONN:.3f}$ (manuscript)")
    ax.set_xlabel(r"polymer size $n$")
    ax.set_ylabel(r"growth rate $\mu_{\mathrm{emp}}(n)$")
    ax.set_title("4D plaquette-polymer growth vs the KP connectivity bound")
    ax.grid(True, alpha=0.3)
    ax.legend(fontsize=9)
    fig.tight_layout()
    Path(out).parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out, format="svg")
    plt.close(fig)
    print(f"  SVG: {out}")


if __name__ == "__main__":
    main()
