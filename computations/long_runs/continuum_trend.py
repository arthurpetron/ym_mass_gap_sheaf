"""Continuum trend of the 0++ glueball / string-tension ratio.

Given several (glueball, string-tension) measurement pairs at different beta
(hence different lattice spacing a), this computes the dimensionless ratio
m(0++)/sqrt(sigma) = (m_0 a)/sqrt(sigma a^2) at each beta and extrapolates it
linearly in sigma*a^2 (the natural O(a^2) scaling variable) to the continuum
sigma*a^2 -> 0.  The point is to show the finite-spacing ratio rising toward
the established SU(2) value ~3.74 (Teper) as a shrinks.

Each measurement pair must be at matched physical volume (L * sqrt(sigma) a ~
const) so that finite-volume effects are roughly constant across the trend and
do not confound the a -> 0 extrapolation.

Inputs come from a small manifest JSON:
    {"teper": 3.74,
     "points": [
        {"beta": 2.3, "glue": "g_b2.3.json", "sigma": "s_b2.3.json", "rmin": 2},
        {"beta": 2.4, "glue": "g_b2.4.json", "sigma": "s_b2.4.json", "rmin": 3},
        ...]}

Usage:
    python -m computations.long_runs.continuum_trend manifest.json --plot trend.svg
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import numpy as np

from computations.long_runs import glueball_analysis as gb
from computations.long_runs import string_tension_analysis as st


def measure_point(pt: dict, tau0: int, rel_thresh: float) -> dict:
    """Return one trend point: beta, sigma a^2 (+err), m_0 a (+err), ratio (+err)."""
    gd = gb.load(pt["glue"])
    gres = gb.analyze(gd, tau0, pt.get("plateau_lo", 1), pt.get("plateau_hi"), rel_thresh)
    m0, m0e = gres["m0_lattice"], gres["m0_lattice_err"]

    sd = st.load(pt["sigma"])
    rmin = pt.get("rmin", 2)
    v0, sig, c, sige = st.fit_cornell(st.static_potential(sd["w"]), rmin)
    # Prefer a genuine configuration jackknife on sigma a^2 when the JSON carries
    # per-bin sums (string_tension --bins); it is the honest statistical error
    # (typically several times the Cornell-fit covariance).  Central value stays
    # the full-sample fit.
    sig_err_kind = "fit"
    if "bin_w_sum" in sd:
        _, jk = st.jackknife_sigma(sd, rmin)
        if np.isfinite(jk) and jk > 0:
            sige, sig_err_kind = jk, "jackknife"
    # If neither is available (singular Cornell covariance, no bins), fall back to
    # the scatter of the large-r Creutz ratios, which independently estimate sigma.
    if not (np.isfinite(sige) and sige > 0):
        cr = st.creutz_ratios(sd["w"])
        tail = [cr[r] for r in sorted(cr)[-3:]]
        sige = float(np.std(tail, ddof=1)) if len(tail) >= 2 else 0.1 * sig
        sig_err_kind = "creutz"
    rs = math.sqrt(sig)
    rse = 0.5 * sige / sig * rs  # error on sqrt(sigma a^2)

    ratio = m0 / rs
    ratio_e = ratio * math.sqrt((m0e / m0) ** 2 + (rse / rs) ** 2)
    return {
        "beta": pt["beta"],
        "L": gd["l"],
        "n_glue": gd["n_collected"],
        "sigma_a2": sig,
        "sigma_a2_err": sige,
        "sigma_err_kind": sig_err_kind,
        "sqrt_sigma_a": rs,
        "m0_a": m0,
        "m0_a_err": m0e,
        "plateau": gres["plateau_window"],
        "ratio": ratio,
        "ratio_err": ratio_e,
    }


def weighted_line(x: np.ndarray, y: np.ndarray, ye: np.ndarray) -> dict:
    """Weighted least-squares y = a + b x.  Returns intercept a (the continuum
    value at x=0) and slope b with errors, plus chi2/dof."""
    w = 1.0 / ye**2
    S, Sx, Sy = w.sum(), (w * x).sum(), (w * y).sum()
    Sxx, Sxy = (w * x * x).sum(), (w * x * y).sum()
    delta = S * Sxx - Sx * Sx
    a = (Sxx * Sy - Sx * Sxy) / delta
    b = (S * Sxy - Sx * Sy) / delta
    var_a, var_b = Sxx / delta, S / delta
    resid = y - (a + b * x)
    dof = max(1, len(x) - 2)
    chi2 = float((w * resid**2).sum())
    return {
        "intercept": a,
        "intercept_err": math.sqrt(var_a),
        "slope": b,
        "slope_err": math.sqrt(var_b),
        "chi2_dof": chi2 / dof,
    }


def main() -> None:
    p = argparse.ArgumentParser(description="0++ glueball / sqrt(sigma) continuum trend.")
    p.add_argument("manifest", help="JSON manifest of (beta, glue, sigma) points")
    p.add_argument("--tau0", type=int, default=1)
    p.add_argument("--rel-thresh", type=float, default=0.5)
    p.add_argument("--plot", default=None)
    args = p.parse_args()

    man = json.loads(Path(args.manifest).read_text())
    teper = man.get("teper", 3.74)
    pts = [measure_point(pt, args.tau0, args.rel_thresh) for pt in man["points"]]
    pts.sort(key=lambda d: d["sigma_a2"])  # ascending a^2 (continuum on the left)

    print("=== 0++ glueball / sqrt(sigma) continuum trend ===")
    print(f"  {'beta':>5} {'L':>3} {'configs':>8}  {'sigma a^2':>12} {'serr':>4}  {'sqrt(s)a':>9}  "
          f"{'m0 a':>14}  {'plateau':>9}  {'m0/sqrt(s)':>16}")
    for d in pts:
        lo, hi = d["plateau"]
        tag = {"jackknife": "jk", "fit": "fit", "creutz": "cr"}.get(d["sigma_err_kind"], "?")
        print(f"  {d['beta']:>5.3f} {d['L']:>3d} {d['n_glue']:>8d}  "
              f"{d['sigma_a2']:>8.5f}±{d['sigma_a2_err']:.5f} {tag:>4}  {d['sqrt_sigma_a']:>9.4f}  "
              f"{d['m0_a']:>7.4f}±{d['m0_a_err']:.4f}  [{lo},{hi}]      "
              f"{d['ratio']:>7.3f}±{d['ratio_err']:.3f}")

    # Only finite (ratio, ratio_err) points enter the fit and plot.
    good = [d for d in pts if np.isfinite(d["ratio"]) and np.isfinite(d["ratio_err"]) and d["ratio_err"] > 0]
    dropped = [d for d in pts if d not in good]
    if dropped:
        print(f"\n  WARNING: dropping {len(dropped)} non-finite point(s) "
              f"(beta={[d['beta'] for d in dropped]}) -- too few configs / Cornell points?")

    fit = None
    if len(good) >= 2:
        x = np.array([d["sigma_a2"] for d in good])
        y = np.array([d["ratio"] for d in good])
        ye = np.array([d["ratio_err"] for d in good])
        fit = weighted_line(x, y, ye)
        r0, r0e = fit["intercept"], fit["intercept_err"]
        print(f"\n  linear-in-(sigma a^2) extrapolation to the continuum (a -> 0):")
        print(f"    m(0++)/sqrt(sigma)|_cont = {r0:.3f} +/- {r0e:.3f}   "
              f"(slope {fit['slope']:+.2f}, chi2/dof = {fit['chi2_dof']:.2f})")
        print(f"    Teper continuum reference = {teper}   "
              f"=> {r0 / teper * 100:.0f}% of Teper, {(teper - r0) / r0e:+.1f} sigma")
    elif len(good) == 1:
        print(f"\n  (only one finite point at sigma a^2={good[0]['sigma_a2']:.4f}; "
              f"need >=2 for an extrapolation)")

    out = args.plot or str(Path(args.manifest).with_suffix(".svg"))
    if good:
        _plot(good, fit, teper, out)
        print(f"  SVG: {out}")
    else:
        print("  (no finite points to plot)")


def _plot(pts: list[dict], fit: dict | None, teper: float, out: str) -> None:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    x = np.array([d["sigma_a2"] for d in pts])
    y = np.array([d["ratio"] for d in pts])
    ye = np.array([d["ratio_err"] for d in pts])

    fig, ax = plt.subplots(figsize=(8.2, 5.2))
    ax.errorbar(x, y, yerr=ye, fmt="o", color="tab:blue", capsize=4, markersize=7,
                label=r"lattice $m(0^{++})/\sqrt{\sigma}$")
    for d in pts:
        ax.annotate(fr"$\beta={d['beta']}$" + f"\n$L={d['L']}$",
                    (d["sigma_a2"], d["ratio"]), textcoords="offset points",
                    xytext=(6, 6), fontsize=8)
    if fit is not None:
        r0, r0e = fit["intercept"], fit["intercept_err"]
        xx = np.linspace(0, x.max() * 1.05, 100)
        ax.plot(xx, r0 + fit["slope"] * xx, "--", color="tab:blue", alpha=0.7,
                label=fr"fit $\to {r0:.2f}\pm{r0e:.2f}$ as $\sigma a^2\to0$")
        ax.errorbar([0], [r0], yerr=[r0e], fmt="s", color="tab:green", capsize=5,
                    markersize=9, label="continuum extrapolation")
    ax.axhline(teper, color="tab:red", linewidth=1.5,
               label=fr"Teper continuum $= {teper}$")
    ax.set_xlabel(r"$\sigma a^2$  (lattice spacing$^2$; $\to 0$ is the continuum)")
    ax.set_ylabel(r"$m(0^{++})/\sqrt{\sigma}$")
    ax.set_title(r"SU(2) 0$^{++}$ glueball / string-tension ratio: approach to the continuum")
    ax.set_xlim(left=-0.005)
    ax.grid(True, alpha=0.3)
    ax.legend(fontsize=9, loc="lower right")
    fig.tight_layout()
    Path(out).parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out, format="svg")
    plt.close(fig)


if __name__ == "__main__":
    main()
