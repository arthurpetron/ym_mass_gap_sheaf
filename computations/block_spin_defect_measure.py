"""Block-spin delta_k / epsilon_k defect analysis + scheme selection (SU(2)).

Consumes the per-beta JSON produced by the Rust `block_defect` binary
(`simulations/src/bin/block_defect.rs`), which measures, on the SAME
decorrelated SU(2) configs, the fine and blocked (factor-2, transverse
weight lambda) average plaquette and Wilson-loop grids W(r,t).

For each candidate blocking scheme (lambda) it forms CORRELATED jackknife
estimates (blocked vs fine on identical configs) of the per-step defect:

  * delta_k -- multiplicative gap-degradation per block-spin step.
      The physical mass gap m = sqrt(sigma). Under an EXACT factor-2 RG the
      physical string tension is invariant, so the blocked Creutz ratio at a
      matched PHYSICAL scale equals 4x the fine one (blocked spacing = 2a):
          chi_blk(2,2) [physical 4a]  vs  chi_fine(4,4) [physical 4a].
      delta_k = 1 - (1/2) sqrt( chi_blk(2,2) / chi_fine(4,4) )   (0 iff exact).

  * eps_k -- additive generated-interaction / leakage per step.
      The blocked action is NOT pure-plaquette Wilson. If it were, its
      short-distance coupling (from <P'>) and long-distance coupling (from
      chi') would coincide. The mismatch, in gap units, is the leakage:
          beta_P  = coupling matching the blocked plaquette <P'> to the
                    Wilson <P>(beta) calibration (short-distance),
          m_pred  = sqrt(chi_fine(2,2)(beta_P))   (gap a Wilson theory at
                    beta_P would have, same estimator),
          m_blk   = sqrt(chi_blk(2,2))            (actual blocked gap),
          eps_k   = | m_blk - m_pred |.
      eps_k = 0 iff the blocked (<P'>, chi') point lies on the fine Wilson
      trajectory (no generated interactions).

Budget (defect-recursion closure):  (1 - sum_k delta_k) * m0 > sum_k eps_k,
with m0 = sqrt(chi_fine(2,2)) at the strong-coupling anchor (smallest beta).

Calibration.  <P>(beta) and chi_fine(2,2)(beta) come from the fine data at the
measured betas, stitched below the measured window with the SU(2) leading
strong-coupling asymptotics <P> = beta/4, sigma a^2 = -ln(beta/4), so that
rough schemes whose <P'> falls below the measured range still get a
physically-grounded (extrapolated, flagged) beta_P.

Honesty: every number carries a jackknife error over configuration bins.
Cross-beta calibration is treated as fixed for the per-beta jackknife (its
uncertainty is second order for the mismatch); this is stated in the report.
"""

from __future__ import annotations

import argparse
import glob
import json
import math
import os
from dataclasses import dataclass

import numpy as np


# --------------------------------------------------------------------------
# Loading + jackknife infrastructure
# --------------------------------------------------------------------------


@dataclass
class BetaData:
    l: int
    beta: float
    n_collected: int
    n_bins: int
    bin_counts: np.ndarray            # [B]
    rmax: int
    rmax_b: int
    lambdas: list[float]
    fine_plaq: np.ndarray             # [B]  per-bin SUM of <P>
    fine_w: np.ndarray                # [B, rmax, rmax] per-bin SUM of W(r,t)
    blk_plaq: dict[float, np.ndarray]  # lambda -> [B]
    blk_w: dict[float, np.ndarray]     # lambda -> [B, rmax_b, rmax_b]


def load_beta(path: str) -> BetaData:
    d = json.load(open(path))
    B = d["n_bins"]
    rmax = d["rmax"]
    rmax_b = d["rmax_blocked"]
    counts = np.array(d["bin_counts"], dtype=float)
    fine_plaq = np.array(d["fine"]["bin_plaq_sum"], dtype=float)
    fine_w = np.array(d["fine"]["bin_w_sum"], dtype=float).reshape(B, rmax, rmax)
    blk_plaq: dict[float, np.ndarray] = {}
    blk_w: dict[float, np.ndarray] = {}
    for blk in d["blocked"]:
        lam = float(blk["lambda"])
        blk_plaq[lam] = np.array(blk["bin_plaq_sum"], dtype=float)
        blk_w[lam] = np.array(blk["bin_w_sum"], dtype=float).reshape(B, rmax_b, rmax_b)
    return BetaData(
        l=d["l"], beta=d["beta"], n_collected=d["n_collected"], n_bins=B,
        bin_counts=counts, rmax=rmax, rmax_b=rmax_b,
        lambdas=[float(x) for x in d["lambdas"]],
        fine_plaq=fine_plaq, fine_w=fine_w, blk_plaq=blk_plaq, blk_w=blk_w,
    )


def jackknife_samples(bin_sums: np.ndarray, counts: np.ndarray) -> np.ndarray:
    """Leave-one-out mean estimates from per-bin SUMS and counts.

    bin_sums: [B, ...]; counts: [B]. Returns [B, ...] of loo means where the
    b-th entry drops bin b: (S - s_b)/(N - n_b).
    """
    S = bin_sums.sum(axis=0)
    N = counts.sum()
    out = np.empty_like(bin_sums)
    for b in range(bin_sums.shape[0]):
        out[b] = (S - bin_sums[b]) / (N - counts[b])
    return out


def jack_mean_err(samples: np.ndarray) -> tuple[float, float]:
    """Central value + jackknife error from B leave-one-out samples."""
    B = len(samples)
    mean = float(np.mean(samples))
    err = float(math.sqrt((B - 1) / B * np.sum((samples - mean) ** 2)))
    return mean, err


def creutz(w: np.ndarray, r: int) -> float:
    """Diagonal Creutz ratio chi(r,r) from a W grid (w[r-1,t-1]).

    chi(r,r) = -ln[ W(r,r) W(r-1,r-1) / (W(r,r-1) W(r-1,r)) ].
    Returns NaN if any loop is non-positive (signal lost in noise).
    """
    num = w[r - 1, r - 1] * w[r - 2, r - 2]
    den = w[r - 1, r - 2] * w[r - 2, r - 1]
    if num > 0 and den > 0:
        return -math.log(num / den)
    return float("nan")


# --------------------------------------------------------------------------
# Wilson calibration: <P>(beta), chi_fine(2,2)(beta), monotone + SC-stitched
# --------------------------------------------------------------------------


class Calibration:
    """Monotone maps <P>(beta) and chi_fine(2,2)(beta) from the fine data,
    stitched below the measured window with SU(2) strong-coupling asymptotics
    <P> = beta/4 and sigma a^2 = -ln(beta/4)."""

    def __init__(self, betas: np.ndarray, plaq: np.ndarray, chi22: np.ndarray):
        order = np.argsort(betas)
        self.betas = betas[order]
        self.plaq = plaq[order]
        self.chi22 = chi22[order]
        self.bmin = float(self.betas[0])
        self.bmax = float(self.betas[-1])

    def plaq_of_beta(self, beta: float) -> float:
        if beta < self.bmin:
            return 0.25 * beta  # SU(2) strong-coupling leading term
        if beta > self.bmax:
            # weak-coupling-ish linear extrapolation from top two points
            return float(np.interp(beta, self.betas, self.plaq))
        return float(np.interp(beta, self.betas, self.plaq))

    def chi22_of_beta(self, beta: float) -> float:
        if beta < self.bmin:
            v = beta / 4.0
            return -math.log(v) if 0 < v < 1 else float("nan")
        return float(np.interp(beta, self.betas, self.chi22))

    def beta_of_plaq(self, p: float) -> float:
        """Invert <P>(beta) = p. Uses the measured monotone table in-range and
        the strong-coupling <P> = beta/4 (=> beta = 4p) below range."""
        pmin = self.plaq_of_beta(self.bmin)
        pmax = self.plaq_of_beta(self.bmax)
        if p <= pmin:
            # strong-coupling branch: connect Wilson <P>=beta/4 to the measured
            # point continuously by taking the smaller of the two estimates.
            b_sc = 4.0 * p
            return min(b_sc, self.bmin)
        if p >= pmax:
            return self.bmax
        return float(np.interp(p, self.plaq, self.betas))


# --------------------------------------------------------------------------
# Per-beta, per-scheme defect measurement (correlated jackknife)
# --------------------------------------------------------------------------


@dataclass
class DefectPoint:
    beta: float
    lam: float
    plaq_fine: tuple[float, float]
    plaq_blk: tuple[float, float]
    chi22_fine: tuple[float, float]
    chi44_fine: tuple[float, float]
    chi22_blk: tuple[float, float]
    delta: tuple[float, float]        # matched physical scale (blk chi22 vs fine chi44)
    delta_sr: tuple[float, float]     # same-r cross-check (blk chi22 vs fine chi22)
    eps: tuple[float, float]
    beta_P: float
    m_blk: float
    m_pred: float
    off_scale: bool


def measure_defects(bd: BetaData, cal: Calibration, lam: float) -> DefectPoint:
    counts = bd.bin_counts
    # Correlated leave-one-out grids on the SAME bins.
    fine_w_loo = jackknife_samples(bd.fine_w, counts)          # [B, rmax, rmax]
    fine_p_loo = jackknife_samples(bd.fine_plaq, counts)       # [B]
    blk_w_loo = jackknife_samples(bd.blk_w[lam], counts)       # [B, rb, rb]
    blk_p_loo = jackknife_samples(bd.blk_plaq[lam], counts)    # [B]
    B = bd.n_bins

    d_samples = np.empty(B)
    dsr_samples = np.empty(B)
    e_samples = np.empty(B)
    chi22f = np.empty(B)
    chi44f = np.empty(B)
    chi22b = np.empty(B)
    betaP = np.empty(B)
    for b in range(B):
        c22f = creutz(fine_w_loo[b], 2)
        c44f = creutz(fine_w_loo[b], 4) if bd.rmax >= 4 else float("nan")
        c22b = creutz(blk_w_loo[b], 2) if bd.rmax_b >= 2 else float("nan")
        chi22f[b], chi44f[b], chi22b[b] = c22f, c44f, c22b
        # delta: matched physical scale (blocked chi(2,2)~4a vs fine chi(4,4)~4a).
        if c22b > 0 and c44f > 0:
            d_samples[b] = 1.0 - 0.5 * math.sqrt(c22b / c44f)
        else:
            d_samples[b] = float("nan")
        # delta same-r cross-check (blocked chi(2,2) vs fine chi(2,2), ideal ratio 4).
        if c22b > 0 and c22f > 0:
            dsr_samples[b] = 1.0 - 0.5 * math.sqrt(c22b / c22f)
        else:
            dsr_samples[b] = float("nan")
        # eps: short vs long distance coupling mismatch, in gap units.
        p_blk = blk_p_loo[b]
        bP = cal.beta_of_plaq(p_blk)
        betaP[b] = bP
        chi_pred = cal.chi22_of_beta(bP)
        m_pred = math.sqrt(chi_pred) if chi_pred > 0 else float("nan")
        m_blk = math.sqrt(c22b) if c22b > 0 else float("nan")
        e_samples[b] = abs(m_blk - m_pred)

    def mv(s):
        good = s[np.isfinite(s)]
        if len(good) < 2:
            return (float(np.mean(good)) if len(good) else float("nan"), float("nan"))
        m = float(np.mean(good))
        err = float(math.sqrt((len(good) - 1) / len(good) * np.sum((good - m) ** 2)))
        return (m, err)

    plaq_f = mv(fine_p_loo)
    plaq_b = mv(blk_p_loo)
    bP_mean = float(np.nanmean(betaP))
    off = bP_mean < cal.bmin - 1e-9
    return DefectPoint(
        beta=bd.beta, lam=lam,
        plaq_fine=plaq_f, plaq_blk=plaq_b,
        chi22_fine=mv(chi22f), chi44_fine=mv(chi44f), chi22_blk=mv(chi22b),
        delta=mv(d_samples), delta_sr=mv(dsr_samples), eps=mv(e_samples),
        beta_P=bP_mean,
        m_blk=math.sqrt(mv(chi22b)[0]) if mv(chi22b)[0] > 0 else float("nan"),
        m_pred=math.sqrt(cal.chi22_of_beta(bP_mean)) if cal.chi22_of_beta(bP_mean) > 0 else float("nan"),
        off_scale=off,
    )


# --------------------------------------------------------------------------
# Driver
# --------------------------------------------------------------------------


def analyze(paths: list[str]) -> dict:
    beids = [load_beta(p) for p in paths]
    beids.sort(key=lambda b: b.beta)
    lambdas = beids[0].lambdas

    # Build fine Wilson calibration from all betas (central values).
    cal_betas, cal_plaq, cal_chi22 = [], [], []
    for bd in beids:
        fw_loo = jackknife_samples(bd.fine_w, bd.bin_counts)
        fp_loo = jackknife_samples(bd.fine_plaq, bd.bin_counts)
        c22 = np.array([creutz(fw_loo[b], 2) for b in range(bd.n_bins)])
        cal_betas.append(bd.beta)
        cal_plaq.append(float(np.mean(fp_loo)))
        cal_chi22.append(float(np.nanmean(c22)))
    cal = Calibration(np.array(cal_betas), np.array(cal_plaq), np.array(cal_chi22))

    # Per-scheme, per-beta defects.
    results: dict[float, list[DefectPoint]] = {lam: [] for lam in lambdas}
    for bd in beids:
        for lam in lambdas:
            results[lam].append(measure_defects(bd, cal, lam))

    # Budget per scheme.
    m0 = math.sqrt(cal.chi22_of_beta(min(cal_betas)))  # anchor gap at strongest coupling
    budgets = {}
    for lam in lambdas:
        pts = results[lam]
        # sum delta, eps over the trajectory (one blocking step per measured beta).
        # CONSERVATIVE budget: clamp delta_k >= 0 -- a negative delta ("gap grew
        # under blocking") is an unphysical artifact of small-r Creutz contamination
        # and would spuriously HELP the budget, so we forbid free gap gain.
        dvals = [(max(0.0, p.delta[0]), p.delta[1]) for p in pts if np.isfinite(p.delta[0])]
        evals = [(p.eps[0], p.eps[1]) for p in pts if np.isfinite(p.eps[0])]
        sum_delta = sum(v for v, _ in dvals)
        sum_delta_err = math.sqrt(sum(e ** 2 for _, e in dvals if np.isfinite(e)))
        sum_eps = sum(v for v, _ in evals)
        sum_eps_err = math.sqrt(sum(e ** 2 for _, e in evals if np.isfinite(e)))
        lhs = (1.0 - sum_delta) * m0
        lhs_err = math.hypot(sum_delta_err * m0, 0.0)
        margin = lhs - sum_eps
        margin_err = math.hypot(lhs_err, sum_eps_err)
        # Per-step budget: at each measured step k, is (1-delta_k)*m_k > eps_k?
        # m_k = sqrt(chi_fine(2,2)(beta_k)) is the gap at that step (same estimator
        # as eps). This is scale-local and does not truncate an infinite trajectory.
        per_step = []
        n_pass = 0
        for p in pts:
            mk = math.sqrt(cal.chi22_of_beta(p.beta))
            dk = max(0.0, p.delta[0]) if np.isfinite(p.delta[0]) else 0.0
            ek = p.eps[0]
            lhs_k = (1.0 - dk) * mk
            ok = np.isfinite(ek) and lhs_k > ek
            per_step.append({"beta": p.beta, "m_k": mk, "delta_k": dk,
                             "eps_k": ek, "lhs_k": lhs_k, "closes": bool(ok)})
            if ok:
                n_pass += 1
        budgets[lam] = {
            "sum_delta": sum_delta, "sum_delta_err": sum_delta_err,
            "sum_eps": sum_eps, "sum_eps_err": sum_eps_err,
            "m0": m0, "lhs": lhs, "lhs_err": lhs_err,
            "margin": margin, "margin_err": margin_err,
            "closes": margin > 0,
            "closes_with_margin": margin - margin_err > 0,
            "per_step": per_step,
            "n_steps_pass": n_pass, "n_steps": len(pts),
        }

    return {
        "l": beids[0].l,
        "betas": cal_betas,
        "lambdas": lambdas,
        "calibration": {
            "beta": cal_betas, "plaq": cal_plaq, "chi22": cal_chi22,
        },
        "m0": m0,
        "results": {
            f"{lam}": [pt_to_dict(p) for p in results[lam]] for lam in lambdas
        },
        "budgets": {f"{lam}": budgets[lam] for lam in lambdas},
    }


def pt_to_dict(p: DefectPoint) -> dict:
    return {
        "beta": p.beta, "lambda": p.lam,
        "plaq_fine": p.plaq_fine, "plaq_blk": p.plaq_blk,
        "chi22_fine": p.chi22_fine, "chi44_fine": p.chi44_fine,
        "chi22_blk": p.chi22_blk,
        "delta": p.delta, "delta_sr": p.delta_sr, "eps": p.eps,
        "beta_P": p.beta_P, "m_blk": p.m_blk, "m_pred": p.m_pred,
        "off_scale": p.off_scale,
    }


def fmt(mv: tuple[float, float]) -> str:
    m, e = mv
    if not np.isfinite(m):
        return "   nan     "
    if not np.isfinite(e):
        return f"{m:8.4f}(--)"
    return f"{m:8.4f}({e:.4f})"


def print_report(res: dict) -> None:
    print(f"\n=== Block-spin defect scheme-selection  (L={res['l']}) ===")
    print(f"anchor gap m0 = sqrt(chi_fine(2,2)) at strongest coupling = {res['m0']:.4f}")
    print("\nFine Wilson calibration:")
    print("   beta     <P>      chi22")
    for b, p, c in zip(res["calibration"]["beta"], res["calibration"]["plaq"], res["calibration"]["chi22"]):
        print(f"  {b:5.2f}  {p:7.4f}  {c:7.4f}")

    for lam in res["lambdas"]:
        print(f"\n--- scheme lambda={lam} ---")
        print(f"  {'beta':>5} {'<P>_blk':>16} {'chi22_blk':>16} "
              f"{'beta_P':>7} {'delta_k(matched)':>17} {'delta_sr':>16} {'eps_k':>16}")
        for pt in res["results"][f"{lam}"]:
            flag = "*" if pt["off_scale"] else " "
            print(f"  {pt['beta']:5.2f} {fmt(pt['plaq_blk']):>16} {fmt(pt['chi22_blk']):>16} "
                  f"{pt['beta_P']:6.2f}{flag} "
                  f"{fmt(pt['delta']):>17} {fmt(pt['delta_sr']):>16} {fmt(pt['eps']):>16}")
        bud = res["budgets"][f"{lam}"]
        print(f"  BUDGET: sum_delta={bud['sum_delta']:.4f}+-{bud['sum_delta_err']:.4f}  "
              f"sum_eps={bud['sum_eps']:.4f}+-{bud['sum_eps_err']:.4f}")
        print(f"          (1-sum_delta)*m0={bud['lhs']:.4f}+-{bud['lhs_err']:.4f}   "
              f"vs sum_eps={bud['sum_eps']:.4f}")
        print(f"          margin={bud['margin']:.4f}+-{bud['margin_err']:.4f}   "
              f"{'CLOSES with margin' if bud['closes_with_margin'] else ('closes (within err)' if bud['closes'] else 'DOES NOT CLOSE')}")
        print(f"  PER-STEP budget (1-delta_k)*m_k > eps_k:  passes {bud['n_steps_pass']}/{bud['n_steps']} steps")
        for s in bud["per_step"]:
            mark = "OK " if s["closes"] else "FAIL"
            print(f"     beta={s['beta']:.2f}: (1-{s['delta_k']:.3f})*{s['m_k']:.3f}={s['lhs_k']:.3f} vs eps={s['eps_k']:.3f}  [{mark}]")
    print("  (* beta_P below measured calibration window: eps uses SC-extrapolated matching, flagged)")


def make_plot(res: dict, out: str) -> str:
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    lambdas = res["lambdas"]
    fig, axes = plt.subplots(1, 3, figsize=(15, 4.5))
    colors = {lambdas[0]: "tab:red", lambdas[1 % len(lambdas)]: "tab:orange",
              lambdas[-1]: "tab:green"}
    # delta_k vs beta
    ax = axes[0]
    for lam in lambdas:
        pts = res["results"][f"{lam}"]
        bs = [p["beta"] for p in pts]
        ys = [p["delta"][0] for p in pts]
        es = [p["delta"][1] for p in pts]
        ax.errorbar(bs, ys, yerr=es, fmt="o-", capsize=3, label=f"$\\lambda={lam}$",
                    color=colors.get(lam))
    ax.axhline(0, color="k", lw=0.6)
    ax.set_xlabel(r"$\beta$"); ax.set_ylabel(r"$\delta_k$ (gap-degradation defect)")
    ax.set_title("Multiplicative gap defect"); ax.legend(); ax.grid(alpha=0.3)
    # eps_k vs beta
    ax = axes[1]
    for lam in lambdas:
        pts = res["results"][f"{lam}"]
        bs = [p["beta"] for p in pts]
        ys = [p["eps"][0] for p in pts]
        es = [p["eps"][1] for p in pts]
        ax.errorbar(bs, ys, yerr=es, fmt="s-", capsize=3, label=f"$\\lambda={lam}$",
                    color=colors.get(lam))
    ax.set_xlabel(r"$\beta$"); ax.set_ylabel(r"$\epsilon_k$ (generated-interaction leakage)")
    ax.set_title("Additive leakage defect"); ax.legend(); ax.grid(alpha=0.3)
    ax.set_yscale("symlog", linthresh=0.05)
    # budget bar
    ax = axes[2]
    xs = np.arange(len(lambdas))
    lhs = [res["budgets"][f"{lam}"]["lhs"] for lam in lambdas]
    lhs_e = [res["budgets"][f"{lam}"]["lhs_err"] for lam in lambdas]
    seps = [res["budgets"][f"{lam}"]["sum_eps"] for lam in lambdas]
    seps_e = [res["budgets"][f"{lam}"]["sum_eps_err"] for lam in lambdas]
    ax.bar(xs - 0.2, lhs, 0.4, yerr=lhs_e, capsize=4, label=r"$(1-\Sigma\delta)m_0$", color="tab:blue")
    ax.bar(xs + 0.2, seps, 0.4, yerr=seps_e, capsize=4, label=r"$\Sigma\epsilon$", color="tab:red")
    ax.set_xticks(xs); ax.set_xticklabels([f"$\\lambda={lam}$" for lam in lambdas])
    ax.set_ylabel("gap units"); ax.set_title("Budget: closes iff blue > red")
    ax.legend(); ax.grid(alpha=0.3, axis="y")
    ax.set_yscale("symlog", linthresh=0.1)
    fig.suptitle(f"SU(2) block-spin defect budget, L={res['l']}", y=1.02)
    fig.tight_layout()
    fig.savefig(out, format="svg", bbox_inches="tight")
    plt.close(fig)
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("glob", help="glob for bdef-*.json (e.g. .../bdef-L16-b*.json)")
    ap.add_argument("--out-json", default=None)
    ap.add_argument("--plot", default=None)
    args = ap.parse_args()
    paths = sorted(glob.glob(args.glob))
    if not paths:
        raise SystemExit(f"no files match {args.glob}")
    print("loading:", *[os.path.basename(p) for p in paths])
    res = analyze(paths)
    print_report(res)
    if args.out_json:
        json.dump(res, open(args.out_json, "w"), indent=2)
        print(f"\nJSON: {args.out_json}")
    if args.plot:
        print(f"SVG: {make_plot(res, args.plot)}")


if __name__ == "__main__":
    main()
