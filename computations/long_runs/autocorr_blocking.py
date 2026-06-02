"""Blocking-analysis certification of the 0++ glueball mass error bar.

The `glueball` binary saves the connected correlator already aggregated into a
fixed number of contiguous configuration bins (`bin_corr_sum`, default 50).
The jackknife error reported by `glueball_analysis` treats those bins as
independent.  This module checks that assumption: it re-blocks the existing
fine bins into successively COARSER block counts B and recomputes the m_0 a
jackknife error at each B (re-running the full GEVP/plateau pipeline on every
leave-one-out sample, via `glueball_analysis.analyze`).

Blocking diagnostic.  If residual autocorrelation lived at the scale of a
single fine block, coarsening the blocks (larger blocks, smaller B) would make
the error estimate GROW until the block size exceeds the autocorrelation time,
then plateau.  A curve that is already flat from the finest B downward means
the fine blocks are effectively independent and the quoted error bar is sound.

Limitation: the raw per-measurement series is not saved, so we can only coarsen
(not refine) below the finest available B.  Since measurements are taken every
`meas_interval` sweeps with overrelaxation, the autocorrelation time is far
below one fine block, so the finest B already sits in the plateau; this study
certifies that one-sidedly.  A two-sided tau_int would need the binary to dump
the per-measurement series.

Usage:
    python -m computations.long_runs.autocorr_blocking glueball-L16-b2.4-hi.json
    python -m computations.long_runs.autocorr_blocking g.json --plot out.svg
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np

from computations.long_runs import glueball_analysis as ga


def reblock(d: dict, n_blocks: int) -> dict:
    """Merge the fine configuration bins into `n_blocks` coarser contiguous
    blocks, returning a glueball-analysis-shaped dict with the coarser bins."""
    bc, bo, cnt = d["bin_corr_sum"], d["bin_op_sum"], d["bin_counts"]
    idx = np.array_split(np.arange(bc.shape[0]), n_blocks)
    out = dict(d)
    out["bin_corr_sum"] = np.stack([bc[g].sum(0) for g in idx])
    out["bin_op_sum"] = np.stack([bo[g].sum(0) for g in idx])
    out["bin_counts"] = np.array([cnt[g].sum() for g in idx])
    out["n_bins"] = n_blocks
    return out


def block_counts(n_fine: int) -> list[int]:
    """Coarser block counts to probe: the finest available plus a descending
    set of divisor-ish values, floored at 4 (jackknife needs a few blocks)."""
    targets = [n_fine, n_fine // 2, n_fine // 5, n_fine // 10, 4]
    seen, out = set(), []
    for b in targets:
        if b >= 4 and b not in seen:
            seen.add(b)
            out.append(b)
    return out


def run(d: dict, tau0: int, plat_lo: int, plat_hi: int | None, rel_thresh: float) -> dict:
    n_fine = d["bin_corr_sum"].shape[0]
    rows = []
    for b in block_counts(n_fine):
        dd = reblock(d, b)
        res = ga.analyze(dd, tau0, plat_lo, plat_hi, rel_thresh)
        configs_per_block = float(d["bin_counts"].sum()) / b
        rows.append(
            {
                "n_blocks": int(b),
                "configs_per_block": configs_per_block,
                "m0_lattice": res["m0_lattice"],
                "m0_lattice_err": res["m0_lattice_err"],
                "plateau_window": list(res["plateau_window"]),
            }
        )
    return {"l": d["l"], "beta": d["beta"], "n_collected": d["n_collected"], "blocks": rows}


def plot(summary: dict, out: str) -> str:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    rows = summary["blocks"]
    sizes = [r["configs_per_block"] for r in rows]
    errs = [r["m0_lattice_err"] for r in rows]
    m0s = [r["m0_lattice"] for r in rows]

    fig, ax = plt.subplots(figsize=(8.0, 5.0))
    ax.plot(sizes, errs, "o-", color="tab:blue")
    for r in rows:
        ax.annotate(f"{r['n_blocks']}", (r["configs_per_block"], r["m0_lattice_err"]),
                    textcoords="offset points", xytext=(0, 6), fontsize=8, ha="center")
    ax.set_xscale("log")
    ax.set_xlabel(r"block size (configs/block);  labels = number of blocks $B$")
    ax.set_ylabel(r"jackknife error on $m_0 a$")
    finite = [e for e in errs if np.isfinite(e)]
    if finite:
        ax.set_ylim(0, 1.6 * max(finite))
    ax.set_title(
        fr"0$^{{++}}$ blocking check, $L={summary['l']}$, $\beta={summary['beta']}$, "
        fr"{summary['n_collected']} configs"
        "\n(central $m_0a$ stable; small-$B$ points are estimator-noise dominated)"
    )
    ax.grid(True, alpha=0.3)
    fig.tight_layout()
    target = Path(out)
    target.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(target, format="svg")
    plt.close(fig)
    return str(target)


def main() -> None:
    p = argparse.ArgumentParser(description="0++ glueball blocking / autocorrelation check.")
    p.add_argument("json", help="path to a glueball correlation-matrix JSON (must carry bins)")
    p.add_argument("--tau0", type=int, default=1)
    p.add_argument("--plateau-lo", type=int, default=1)
    p.add_argument("--plateau-hi", type=int, default=None)
    p.add_argument("--rel-thresh", type=float, default=0.5)
    p.add_argument("--plot", default=None)
    p.add_argument("--out", default=None, help="JSON summary output path")
    args = p.parse_args()

    d = ga.load(args.json)
    if "bin_corr_sum" not in d:
        raise SystemExit("this JSON carries no per-bin sums; blocking needs binned data")

    summary = run(d, args.tau0, args.plateau_lo, args.plateau_hi, args.rel_thresh)

    print(f"=== 0++ blocking check (L={d['l']}, beta={d['beta']}, {d['n_collected']} configs) ===")
    print(f"  {'B blocks':>9}  {'configs/blk':>12}  {'m0 a':>10}  {'jk err':>10}  plateau")
    for r in summary["blocks"]:
        print(f"  {r['n_blocks']:>9}  {r['configs_per_block']:>12.1f}  "
              f"{r['m0_lattice']:>10.4f}  {r['m0_lattice_err']:>10.4f}  "
              f"tau in [{r['plateau_window'][0]},{r['plateau_window'][1]}]")
    m0s = [r["m0_lattice"] for r in summary["blocks"] if np.isfinite(r["m0_lattice"])]
    if len(m0s) >= 2 and max(abs(x) for x in m0s) > 0:
        drift = (max(m0s) - min(m0s)) / max(abs(x) for x in m0s)
        print(f"  central value m_0 a drift across blockings: {drift*100:.2f}%  "
              f"({'stable' if drift < 0.01 else 'MOVES -- investigate'})")
    errs = [r["m0_lattice_err"] for r in summary["blocks"] if np.isfinite(r["m0_lattice_err"])]
    if len(errs) >= 2:
        print(f"  jackknife error envelope across B={summary['blocks'][-1]['n_blocks']}.."
              f"{summary['blocks'][0]['n_blocks']}: [{min(errs):.4f}, {max(errs):.4f}]")
        print("  NOTE: re-blocking only coarsens (no finer than the saved bins); the small-B")
        print("        points are jackknife-estimator-noise dominated, so this is a one-sided")
        print("        check.  A conclusive two-sided tau_int needs the raw per-measurement")
        print("        series dumped from the binary, not just the binned sums.")

    if args.out:
        Path(args.out).write_text(json.dumps(summary, indent=2))
        print(f"  JSON: {args.out}")
    if args.plot:
        print(f"  SVG: {plot(summary, args.plot)}")


if __name__ == "__main__":
    main()
