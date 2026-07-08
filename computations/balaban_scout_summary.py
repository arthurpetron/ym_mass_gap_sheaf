"""Combined L12-vs-L16 summary figure + JSON for the Balaban defect scout.

Overlays the two accessible lattice sizes so the reader sees (i) the L-robustness
of the leakage ε(1−w) for the transverse schemes, (ii) the WINDOW-INSTABILITY of the
fitted exponent p (the honest caveat), and (iii) the decisive gap between decimation
(λ=0, ε rising = non-summable) and transverse bond-moving (λ≥0.5, ε decaying, p≥2).
"""
from __future__ import annotations
import glob, json, os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

import balaban_defect_scaling as bal
import block_spin_defect_measure as bsd

OUTBASE = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                       "block_spin_defect_data")
DATA = OUTBASE  # committed fine-lambda raw runs live alongside the outputs


def load(Lname):
    # fine-lambda raw runs are stored as bdef-{L}-b*-fl.json
    paths = sorted(glob.glob(f"{DATA}/bdef-{Lname}-b*-fl.json"))
    res = bsd.analyze(paths)
    return res, bal.scaling_analysis(res)


def main():
    (r12, s12) = load("L12")
    (r16, s16) = load("L16")
    lambdas = r12["lambdas"]
    cmap = plt.cm.viridis(np.linspace(0.12, 0.88, len(lambdas)))
    col = {lam: cmap[i] for i, lam in enumerate(lambdas)}

    fig, axes = plt.subplots(1, 3, figsize=(16.5, 5.0))

    # panel 1: eps(1-w) overlay, both L, log-log, p=1/p=2 guides
    ax = axes[0]
    for res, s, mk, lab in ((r12, s12, "o", "L12"), (r16, s16, "^", "L16")):
        for lam in lambdas:
            rows = s[f"{lam}"]["rows"]
            m = np.array([x["margin"] for x in rows])
            e = np.array([x["eps"] for x in rows])
            ee = np.array([x["eps_err"] for x in rows])
            good = np.isfinite(e) & (e > 0)
            ax.errorbar(m[good], e[good], yerr=ee[good], fmt=mk, ms=5, capsize=2,
                        color=col[lam], alpha=0.9,
                        label=(f"λ={lam} ({lab})" if lam in (0.0, 0.5) else None))
    xg = np.array([0.27, 0.50])
    ax.plot(xg, 0.32 * (xg / xg[0]) ** 1, "k--", lw=1.1, label="p=1 (linear, NON-summable)")
    ax.plot(xg, 0.32 * (xg / xg[0]) ** 2, "k:", lw=1.5, label="p=2 (quad, summable)")
    ax.set_xscale("log"); ax.set_yscale("log")
    ax.set_xlabel(r"margin $1-w=1-\langle P\rangle$  (larger = stronger coupling)")
    ax.set_ylabel(r"$\epsilon_k=|\sqrt{\chi_{blk}}-\sqrt{\chi_{fine}}(\beta_p)|$")
    ax.set_title("Leakage scaling: λ=0 rises (non-summable),\nλ≥0.5 decays steeper than p=2")
    ax.legend(fontsize=6.5, ncol=1, loc="lower right"); ax.grid(alpha=0.3, which="both")

    # panel 2: fitted exponent p per scheme, both L, with instability shown
    ax = axes[1]
    xs = np.arange(len(lambdas))
    for s, off, mk, lab, c in ((s12, -0.13, "o", "L12 (1-w∈[.28,.50])", "tab:blue"),
                               (s16, +0.13, "^", "L16 (1-w∈[.28,.37])", "tab:orange")):
        pe = [s[f"{lam}"]["fit_all"]["eps"]["p"] for lam in lambdas]
        pee = [s[f"{lam}"]["fit_all"]["eps"]["p_err"] for lam in lambdas]
        ax.errorbar(xs + off, pe, yerr=pee, fmt=mk, ms=9, capsize=4, color=c, label=lab)
    ax.axhspan(0.7, 1.3, color="tab:red", alpha=0.12)
    ax.axhspan(1.8, 5.2, color="tab:green", alpha=0.10)
    ax.axhline(1, color="tab:red", ls="--", lw=1); ax.axhline(2, color="tab:green", ls=":", lw=1.4)
    ax.set_ylim(-1, 6)
    ax.set_xticks(xs); ax.set_xticklabels([f"{lam}" for lam in lambdas])
    ax.set_xlabel(r"scheme $\lambda$ (transverse bond-move weight)")
    ax.set_ylabel(r"fitted exponent $p$ in $\epsilon\propto(1-w)^p$")
    ax.set_title("Exponent: λ=0 in RED (linear/non-summable),\nλ≥0.5 in GREEN (p≥2) but window-unstable")
    ax.legend(fontsize=7, loc="upper left"); ax.grid(alpha=0.3, axis="y")

    # panel 3: Sigma-eps budget per scheme, both L (closes iff < m0)
    ax = axes[2]
    for res, off, mk, lab, c in ((r12, -0.15, "o", "L12 (β 2.0–3.0)", "tab:blue"),
                                 (r16, +0.15, "^", "L16 (β 2.4–3.0)", "tab:orange")):
        se = [res["budgets"][f"{lam}"]["sum_eps"] for lam in lambdas]
        ax.plot(xs + off, se, mk + "-", ms=9, color=c, label=f"Σε {lab}")
        ax.axhline(res["m0"], color=c, ls=":", lw=1.2, alpha=0.8)
    ax.set_xticks(xs); ax.set_xticklabels([f"{lam}" for lam in lambdas])
    ax.set_xlabel(r"scheme $\lambda$"); ax.set_ylabel(r"$\Sigma_k\,\epsilon_k$ (dotted = anchor $m_0$)")
    ax.set_title("Budget threat: Σε below its m₀ dotted line = closes.\nλ=0 far above; λ≥0.25 near/below")
    ax.legend(fontsize=7); ax.grid(alpha=0.3, axis="y")

    fig.suptitle("SU(2) block-spin defect SCALING scout — scheme ranking & ε-summability "
                 "(MEASURED, small-L; decisive test needs cloud)", y=1.02, fontsize=12)
    fig.tight_layout()
    out_svg = f"{OUTBASE}/balaban-scaling-combined.svg"
    fig.savefig(out_svg, format="svg", bbox_inches="tight")
    plt.close(fig)

    # combined JSON
    def pack(res, s):
        return {
            "l": res["l"], "betas": res["betas"], "m0": res["m0"],
            "per_scheme": {
                f"{lam}": {
                    "margin_range": s[f"{lam}"]["margin_range"],
                    "p_eps_all": s[f"{lam}"]["fit_all"]["eps"],
                    "p_eps_onscale": s[f"{lam}"]["fit_onscale"]["eps"] if s[f"{lam}"]["fit_onscale"] else None,
                    "p_delta_all": s[f"{lam}"]["fit_all"]["delta"],
                    "sum_eps": res["budgets"][f"{lam}"]["sum_eps"],
                    "budget_margin": res["budgets"][f"{lam}"]["margin"],
                    "closes": res["budgets"][f"{lam}"]["closes"],
                    "eps_vs_beta": [{"beta": x["beta"], "margin": x["margin"],
                                     "eps": x["eps"], "eps_err": x["eps_err"],
                                     "off_scale": x["off_scale"]} for x in s[f"{lam}"]["rows"]],
                } for lam in lambdas
            },
        }
    trunc = bal.truncation_order(2.9, p_fuse=8, tols=(1e-3, 1e-6, 1e-9))
    combined = {
        "description": "Balaban/Koch-Wittwer block-spin defect scaling scout: per-scheme "
                       "eps-exponent, budget, and item-12 character truncation order.",
        "lambdas": lambdas,
        "L12": pack(r12, s12),
        "L16": pack(r16, s16),
        "truncation_at_beta_eff_2p9": trunc,
    }
    out_json = f"{OUTBASE}/balaban-scaling-combined.json"
    json.dump(combined, open(out_json, "w"), indent=2)
    print("wrote", out_svg)
    print("wrote", out_json)


if __name__ == "__main__":
    main()
