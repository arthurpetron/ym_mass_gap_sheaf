"""Balaban / Koch–Wittwer SCOUT — block-spin defect SCALING + scheme ranking.

Extends `block_spin_defect_measure.py` (which measures per-beta δ_k, ε_k for a
family of factor-2 transverse-bond-moving schemes indexed by the weight λ) with
the TWO numbers the Lean campaign actually needs but the per-beta table does not
expose:

  (A) THE DECISIVE EXPONENT p in  ε_k ∝ (1 − w_k)^p  and  δ_k ∝ (1 − w_k)^p.
      The whole `EpsilonSummability` dichotomy is: LINEAR (p≈1) ⟹ Σε = ∞ (budget
      NEVER closes); QUADRATIC (p≈2) ⟹ Σε < ∞ (budget CAN close). At the accessible
      crossover betas the two are numerically degenerate (Lean's own caveat), so we
      fit log ε vs log(1−w) over the trajectory and report the slope WITH the honest
      lever range and R². This is a MEASUREMENT of which branch the real 4D flow
      shows at accessible sizes — NOT a proof.

  (B) THE CHARACTER-CHANNEL TRUNCATION ORDER for item 12's Lean interval arithmetic.
      One MK block step raises the single-plaquette class function to the power
      p_fuse = b^{d−1} (= 8 for b=2, d=4) POINTWISE = a p_fuse-fold Clebsch–Gordan
      fusion of the SU(2) heat-kernel coefficients. The certified contraction must
      retain finitely many channels j ≤ J; we compute J (and the truncated tail) at
      the MEASURED effective coupling β_eff so the Lean knows how many characters to
      certify and how big the discarded tail is.

Honesty: MEASURED = the small-L local Creutz/plaquette numbers here. EXTRAPOLATED =
what the fit's exponent WOULD become at β ≥ 2.6 deep in the scaling window, which the
small blocked lattice (L/2)^4 cannot resolve cleanly — that is exactly the cloud job.

Consumes the same `bdef-*.json` the Rust `block_defect` binary emits; reuses the
loader + jackknife + calibration from `block_spin_defect_measure.py`.
"""

from __future__ import annotations

import argparse
import glob
import json
import math
import os

import numpy as np

import block_spin_defect_measure as bsd


# --------------------------------------------------------------------------
# (A) defect-vs-margin scaling: fit ε_k, δ_k ∝ (1 − w_k)^p
# --------------------------------------------------------------------------


def loglog_slope(x: np.ndarray, y: np.ndarray, yerr: np.ndarray | None = None):
    """Weighted linear fit log y = p log x + c. Returns (p, p_err, c, R2, n)."""
    m = np.isfinite(x) & np.isfinite(y) & (x > 0) & (y > 0)
    lx, ly = np.log(x[m]), np.log(y[m])
    n = len(lx)
    if n < 2:
        return (float("nan"), float("nan"), float("nan"), float("nan"), n)
    if yerr is not None:
        ye = yerr[m]
        # propagate to log space: σ(log y) = σ_y / y ; guard zeros.
        w = np.where((ye > 0) & np.isfinite(ye), (y[m] / np.maximum(ye, 1e-12)), 1.0)
    else:
        w = np.ones(n)
    W = np.diag(w ** 2)
    A = np.vstack([lx, np.ones(n)]).T
    # weighted least squares
    AtW = A.T @ W
    cov = np.linalg.inv(AtW @ A)
    coef = cov @ AtW @ ly
    p, c = coef
    resid = ly - A @ coef
    ss_res = float(np.sum((w * resid) ** 2))
    ss_tot = float(np.sum((w * (ly - np.average(ly, weights=w ** 2))) ** 2))
    r2 = 1.0 - ss_res / ss_tot if ss_tot > 0 else float("nan")
    # crude parameter error from the weighted covariance * reduced chi2
    dof = max(n - 2, 1)
    red_chi2 = ss_res / dof
    p_err = float(math.sqrt(cov[0, 0] * max(red_chi2, 1.0)))
    return (float(p), p_err, float(c), r2, n)


def scaling_analysis(res: dict, min_w_margin: float = 0.0) -> dict:
    """For each scheme λ, gather (1−w_k, δ_k, ε_k) across betas and fit the exponent.

    w_k is the FINE plaquette ⟨P⟩ at step k (the physical margin 1−w ∼ g²). Points
    with off_scale=True (blocked coupling below the calibrated window) are FLAGGED but
    still reported; the fit is done both on ALL finite points and on the on-scale-only
    subset, so the reader can see the lever."""
    out = {}
    # fine ⟨P⟩(beta) from calibration table
    cal_beta = np.array(res["calibration"]["beta"], dtype=float)
    cal_plaq = np.array(res["calibration"]["plaq"], dtype=float)
    for lam in res["lambdas"]:
        pts = res["results"][f"{lam}"]
        rows = []
        for p in pts:
            w = float(np.interp(p["beta"], cal_beta[np.argsort(cal_beta)],
                                cal_plaq[np.argsort(cal_beta)]))
            margin = 1.0 - w
            rows.append({
                "beta": p["beta"], "w": w, "margin": margin,
                "delta": p["delta"][0], "delta_err": p["delta"][1],
                "eps": p["eps"][0], "eps_err": p["eps"][1],
                "off_scale": p["off_scale"],
            })
        marg = np.array([r["margin"] for r in rows])
        eps = np.array([r["eps"] for r in rows])
        eps_e = np.array([r["eps_err"] for r in rows])
        dlt = np.array([abs(r["delta"]) for r in rows])  # |δ|: sign is contamination noise
        dlt_e = np.array([r["delta_err"] for r in rows])
        onscale = np.array([not r["off_scale"] for r in rows])

        def fit(mask):
            return {
                "eps": dict(zip(("p", "p_err", "c", "R2", "n"),
                                loglog_slope(marg[mask], eps[mask], eps_e[mask]))),
                "delta": dict(zip(("p", "p_err", "c", "R2", "n"),
                                  loglog_slope(marg[mask], dlt[mask], dlt_e[mask]))),
            }

        all_mask = np.ones(len(rows), dtype=bool)
        out[f"{lam}"] = {
            "rows": rows,
            "margin_range": [float(np.nanmin(marg)), float(np.nanmax(marg))],
            "fit_all": fit(all_mask),
            "fit_onscale": fit(onscale) if onscale.sum() >= 2 else None,
        }
    return out


# --------------------------------------------------------------------------
# (B) character-channel truncation order for item 12 (SU(2) heat-kernel)
# --------------------------------------------------------------------------


def su2_wilson_char_coeffs(beta: float, jmax_2: int = 60) -> np.ndarray:
    """SU(2) fundamental-Wilson single-plaquette class-function coefficients.

    e^{β cosθ} expanded in characters χ_j(θ)=sin(nθ)/sinθ, n=2j+1. Standard result:
    the coefficient of χ_j is  a_n = (2/β)·n·I_n(β)  up to overall normalisation, i.e.
    a_n ∝ n·I_n(β) with I the modified Bessel. Returns the NORMALISED (a_1 = 1)
    coefficient array indexed by n = 1..jmax_2 (n=2j+1, so j = (n−1)/2)."""
    from scipy.special import ive  # exponentially scaled I_n; ratio is exact
    n = np.arange(1, jmax_2 + 1)
    a = n * ive(n, beta)
    return a / a[0]


def truncation_order(beta_eff: float, p_fuse: int = 8,
                     tols=(1e-3, 1e-6, 1e-9)) -> dict:
    """Channel truncation order J(tol) for the single-plaquette weight AND for the
    p_fuse-fold Clebsch–Gordan fusion (the MK bond-move) at coupling β_eff.

    Single plaquette: relative L1 tail  T(J) = Σ_{n>J}|a_n| / Σ_n |a_n|.
    Fusion: a p_fuse-fold pointwise power broadens the character support. In the
    character (Fourier-on-conjugacy) basis the pointwise product is convolution, so
    the fused coefficient support extends to n_max ≈ p_fuse·(n_single − 1) + 1. We
    compute the fused coefficient tail exactly by iterated SU(2) fusion of the
    single-plaquette coefficient sequence and report J_fuse(tol)."""
    a = su2_wilson_char_coeffs(beta_eff, jmax_2=80)
    absa = np.abs(a)
    csum = np.cumsum(absa)
    tot = csum[-1]
    tail = 1.0 - csum / tot  # tail[J-1] = Σ_{n>J}

    def first_below(t):
        idx = np.where(tail < t)[0]
        return int(idx[0] + 1) if len(idx) else len(a)  # J in n-units

    single = {f"{t:.0e}": first_below(t) for t in tols}

    # p_fuse-fold SU(2) fusion of the coefficient sequence (as heat-kernel coeffs
    # under pointwise product => CG convolution). We work with the reduced coeffs
    # b_n = a_n (already the χ_j coefficients). SU(2) fusion of χ_j ⊗ χ_j' =
    # ⊕_{|j−j'|}^{j+j'} χ_J ; in n=2j+1 index the product of two class functions
    # f=Σ b_n χ_{(n-1)/2}, g=Σ c_m χ_{(m-1)/2} has (f·g) coeff at level = the CG
    # decomposition. We convolve in the χ basis using the SU(2) fusion rule.
    def fuse(bn, cn):
        # bn indexed by n=1.., cn likewise. Result indexed by level L=1..
        NB, NC = len(bn), len(cn)
        out = np.zeros(NB + NC, dtype=float)
        for i in range(NB):
            ji2 = i  # j = i/2 (n=i+1)
            if bn[i] == 0:
                continue
            for k in range(NC):
                jk2 = k
                if cn[k] == 0:
                    continue
                # J runs |ji−jk|..ji+jk in integer steps of j => n steps of 2
                lo = abs(ji2 - jk2)
                hi = ji2 + jk2
                for L in range(lo, hi + 1, 2):
                    out[L] += bn[i] * cn[k]
        return out

    fused = absa.copy()
    for _ in range(p_fuse - 1):
        fused = fuse(fused, absa)
        # keep it bounded
        if len(fused) > 400:
            fused = fused[:400]
    fcs = np.cumsum(fused)
    ftail = 1.0 - fcs / fcs[-1]

    def ffirst(t):
        idx = np.where(ftail < t)[0]
        return int(idx[0] + 1) if len(idx) else len(fused)

    fusion = {f"{t:.0e}": ffirst(t) for t in tols}

    return {
        "beta_eff": beta_eff,
        "p_fuse": p_fuse,
        "single_plaquette_J": single,
        "fused_J": fusion,
        "single_tail_at_J": {f"{t:.0e}": float(tail[min(first_below(t) - 1, len(tail) - 1)])
                             for t in tols},
        "n_single_support_99pct": int(np.searchsorted(csum / tot, 0.99) + 1),
    }


# --------------------------------------------------------------------------
# driver + plot
# --------------------------------------------------------------------------


def run(paths, out_json, out_svg, min_beta_eff_scan=None):
    res = bsd.analyze(paths)
    scal = scaling_analysis(res)

    # β_eff per scheme = mean measured blocked-matched coupling β_P over on-scale betas.
    trunc = {}
    for lam in res["lambdas"]:
        bps = [p["beta_P"] for p in res["results"][f"{lam}"]
               if not p["off_scale"] and np.isfinite(p["beta_P"])]
        beta_eff = float(np.mean(bps)) if bps else float(
            np.mean([p["beta_P"] for p in res["results"][f"{lam}"] if np.isfinite(p["beta_P"])]))
        trunc[f"{lam}"] = truncation_order(max(beta_eff, 0.3))

    combined = {"l": res["l"], "betas": res["betas"], "lambdas": res["lambdas"],
                "m0": res["m0"], "scaling": scal, "truncation": trunc,
                "budgets": {k: {kk: v[kk] for kk in
                                ("sum_delta", "sum_eps", "margin", "margin_err",
                                 "closes", "n_steps_pass", "n_steps")}
                            for k, v in res["budgets"].items()}}
    if out_json:
        json.dump(combined, open(out_json, "w"), indent=2)
        print("JSON:", out_json)
    print_report(combined)
    if out_svg:
        make_plot(combined, out_svg)
        print("SVG:", out_svg)
    return combined


def print_report(c):
    print(f"\n=== Balaban defect-scaling SCOUT (L={c['l']}) ===")
    print(f"betas={c['betas']}  m0={c['m0']:.4f}")
    print("\n-- (A) exponent p in  ε_k ∝ (1−w)^p  [p≈1 LINEAR/non-summable, "
          "p≈2 QUADRATIC/summable] --")
    print(f"  {'λ':>5} {'margin range':>16} {'p_eps(all)':>14} {'p_eps(onsc)':>14} "
          f"{'p_delta(all)':>14} {'Σε':>7} {'margin':>9}")
    for lam in c["lambdas"]:
        s = c["scaling"][f"{lam}"]
        b = c["budgets"][f"{lam}"]
        mr = s["margin_range"]
        fe = s["fit_all"]["eps"]
        feo = s["fit_onscale"]["eps"] if s["fit_onscale"] else {"p": float("nan"), "p_err": float("nan"), "R2": float("nan")}
        fd = s["fit_all"]["delta"]
        print(f"  {lam:>5} [{mr[0]:.3f},{mr[1]:.3f}]   "
              f"{fe['p']:6.2f}±{fe['p_err']:.2f}  {feo['p']:6.2f}±{feo['p_err']:.2f}  "
              f"{fd['p']:6.2f}±{fd['p_err']:.2f}  {b['sum_eps']:6.3f}  {b['margin']:+.3f}")
    print("\n-- (B) character-channel truncation order for item 12 (Lean interval "
          "arithmetic) --")
    for lam in c["lambdas"]:
        t = c["truncation"][f"{lam}"]
        print(f"  λ={lam}: β_eff={t['beta_eff']:.2f}  single-plaq J(1e-6)={t['single_plaquette_J']['1e-06']} "
              f"channels  |  {t['p_fuse']}-fold fused J(1e-6)={t['fused_J']['1e-06']} channels "
              f"(tail<1e-6)")


def make_plot(c, out):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    lambdas = c["lambdas"]
    cmap = plt.cm.viridis(np.linspace(0.15, 0.85, len(lambdas)))
    colors = {lam: cmap[i] for i, lam in enumerate(lambdas)}
    fig, axes = plt.subplots(1, 3, figsize=(16, 4.8))

    # panel 1: ε_k vs margin (1−w), log-log, with fitted slopes + p=1,2 guides
    ax = axes[0]
    for lam in lambdas:
        rows = c["scaling"][f"{lam}"]["rows"]
        marg = np.array([r["margin"] for r in rows])
        eps = np.array([r["eps"] for r in rows])
        epse = np.array([r["eps_err"] for r in rows])
        onsc = np.array([not r["off_scale"] for r in rows])
        ax.errorbar(marg[onsc], eps[onsc], yerr=epse[onsc], fmt="o", ms=6, capsize=2,
                    color=colors[lam], label=f"λ={lam}")
        ax.errorbar(marg[~onsc], eps[~onsc], yerr=epse[~onsc], fmt="x", ms=6,
                    color=colors[lam], alpha=0.4)
    # guides p=1, p=2 anchored at a representative point
    xg = np.array([0.28, 0.55])
    ax.plot(xg, 0.35 * (xg / xg[0]) ** 1, "k--", lw=1, label="p=1 (linear)")
    ax.plot(xg, 0.35 * (xg / xg[0]) ** 2, "k:", lw=1.4, label="p=2 (quad)")
    ax.set_xscale("log"); ax.set_yscale("log")
    ax.set_xlabel(r"margin $1-w=1-\langle P\rangle$")
    ax.set_ylabel(r"$\epsilon_k=|\sqrt{\chi_{blk}}-\sqrt{\chi_{fine}}|$")
    ax.set_title("Leakage scaling (slope = exponent p)")
    ax.legend(fontsize=7, ncol=2); ax.grid(alpha=0.3, which="both")

    # panel 2: fitted exponent p_eps per scheme, with p=1/p=2 bands
    ax = axes[1]
    xs = np.arange(len(lambdas))
    pe = [c["scaling"][f"{lam}"]["fit_all"]["eps"]["p"] for lam in lambdas]
    pee = [c["scaling"][f"{lam}"]["fit_all"]["eps"]["p_err"] for lam in lambdas]
    ax.axhspan(0.8, 1.2, color="tab:red", alpha=0.12)
    ax.axhspan(1.8, 2.2, color="tab:green", alpha=0.12)
    ax.axhline(1, color="tab:red", ls="--", lw=1); ax.axhline(2, color="tab:green", ls=":", lw=1.4)
    ax.errorbar(xs, pe, yerr=pee, fmt="s", ms=9, capsize=4, color="tab:blue")
    ax.set_xticks(xs); ax.set_xticklabels([f"{lam}" for lam in lambdas])
    ax.set_xlabel(r"scheme $\lambda$"); ax.set_ylabel(r"fitted exponent $p$ in $\epsilon\propto(1-w)^p$")
    ax.set_title("LINEAR (red, non-summable) vs QUAD (green, summable)")
    ax.text(0.02, 0.93, "red band = non-summable\ngreen band = summable",
            transform=ax.transAxes, fontsize=7, va="top")
    ax.grid(alpha=0.3, axis="y")

    # panel 3: truncation order per scheme (single + fused, tol 1e-6)
    ax = axes[2]
    js = [c["truncation"][f"{lam}"]["single_plaquette_J"]["1e-06"] for lam in lambdas]
    jf = [c["truncation"][f"{lam}"]["fused_J"]["1e-06"] for lam in lambdas]
    ax.bar(xs - 0.2, js, 0.4, label="single plaquette", color="tab:cyan")
    ax.bar(xs + 0.2, jf, 0.4, label=f"{c['truncation'][str(lambdas[0])]['p_fuse']}-fold fused (MK step)",
           color="tab:purple")
    ax.set_xticks(xs); ax.set_xticklabels([f"{lam}" for lam in lambdas])
    ax.set_xlabel(r"scheme $\lambda$"); ax.set_ylabel("channels J (tail < 1e-6)")
    ax.set_title("Item-12 truncation order for Lean interval arith.")
    ax.legend(fontsize=8); ax.grid(alpha=0.3, axis="y")

    fig.suptitle(f"SU(2) block-spin defect SCALING scout (L={c['l']})", y=1.02, fontsize=13)
    fig.tight_layout()
    fig.savefig(out, format="svg", bbox_inches="tight")
    plt.close(fig)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("glob")
    ap.add_argument("--out-json", default=None)
    ap.add_argument("--plot", default=None)
    args = ap.parse_args()
    paths = sorted(glob.glob(args.glob))
    if not paths:
        raise SystemExit(f"no files match {args.glob}")
    print("loading:", *[os.path.basename(p) for p in paths])
    run(paths, args.out_json, args.plot)


if __name__ == "__main__":
    main()
