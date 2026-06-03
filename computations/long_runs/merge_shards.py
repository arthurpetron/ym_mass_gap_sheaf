"""Merge per-shard measurement JSONs into one analysis-ready JSON.

The cloud campaign runs each `(beta, L)` point as `N` independent shards (the
`measure` binary with distinct seeds, one per VM), each emitting its own
`glueball-*.json` / `sigma-*.json` with that shard's configuration bins.  Shards
are independent Markov chains, so their bins are independent draws from the same
ensemble: concatenating them yields a single, larger jackknife ensemble that the
existing analysis (`glueball_analysis.py`, `string_tension_analysis.py`,
`autocorr_blocking.py`) consumes unchanged.

This tool does exactly that concatenation and recomputes the global
mean/correlator (glueball) or loop grid (sigma) from the unioned bin sums:

    mean_op[i]      = sum_b bin_op_sum[b][i] / N_collected
    corr[i][j][tau] = sum_b bin_corr_sum[b][i][j][tau] / N_collected
                      - mean_op[i] * mean_op[j]
    w[r][t]         = sum_b bin_w_sum[b][r][t] / N_collected

The kind (glueball vs sigma) is auto-detected from the schema.  `elapsed_seconds`
is reported as the wall time of the slowest shard (the runs are concurrent);
`total_cpu_seconds` and `n_shards` are added for the record.

Usage:
    python -m computations.long_runs.merge_shards --out glueball-L24-b2.5.json \
        runs/glueball-L24-b2.5-s0.json runs/glueball-L24-b2.5-s1.json ...
    python -m computations.long_runs.merge_shards --out sigma-L24-b2.5.json \
        runs/sigma-L24-b2.5-s*.json
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np


def _load(paths: list[str]) -> list[dict]:
    shards = [json.loads(Path(p).read_text()) for p in paths]
    if not shards:
        raise SystemExit("no shard files given")
    return shards


def _check_consistent(shards: list[dict], keys: list[str], paths: list[str]) -> None:
    """All shards of one point must share these identifying parameters."""
    ref = shards[0]
    for sh, p in zip(shards[1:], paths[1:]):
        for k in keys:
            if sh.get(k) != ref.get(k):
                raise SystemExit(
                    f"shard mismatch on '{k}': {paths[0]} has {ref.get(k)!r}, "
                    f"{p} has {sh.get(k)!r} -- are these the same (beta, L) point?"
                )
    seeds = [sh.get("seed") for sh in shards]
    if len(set(seeds)) != len(seeds):
        print(f"  WARNING: duplicate seeds across shards {seeds} -- "
              "the shards are NOT independent; statistics will be understated.")


def _provenance(shards: list[dict], n_collected: int) -> dict:
    return {
        "n_shards": len(shards),
        "shard_seeds": [sh.get("seed") for sh in shards],
        "shard_collected": [sh["n_collected"] for sh in shards],
        "elapsed_seconds": max(sh.get("elapsed_seconds", 0.0) for sh in shards),
        "total_cpu_seconds": sum(sh.get("elapsed_seconds", 0.0) for sh in shards),
    }


def merge_glueball(shards: list[dict], paths: list[str]) -> dict:
    _check_consistent(shards, ["l", "beta", "smear_levels", "meas_interval"], paths)
    nc = sum(sh["n_collected"] for sh in shards)
    if nc == 0:
        raise SystemExit("no collected configs across shards")

    # Concatenate the per-shard configuration bins.
    bin_counts = [c for sh in shards for c in sh["bin_counts"]]
    bin_op = [r for sh in shards for r in sh["bin_op_sum"]]
    bin_corr = [m for sh in shards for m in sh["bin_corr_sum"]]
    bin_op_e = [r for sh in shards for r in sh["bin_op_E_sum"]]
    bin_corr_e = [m for sh in shards for m in sh["bin_corr_E_sum"]]

    # Recompute the global connected correlator from the unioned bin sums.
    op = np.array(bin_op).sum(axis=0) / nc                  # [nlev]
    corr = np.array(bin_corr).sum(axis=0) / nc              # [nlev][nlev][tau]
    corr = corr - op[:, None, None] * op[None, :, None]
    op_e = np.array(bin_op_e).sum(axis=0) / nc              # [n_e]
    corr_e = np.array(bin_corr_e).sum(axis=0) / nc          # [n_e][n_e][tau]
    corr_e = corr_e - op_e[:, None, None] * op_e[None, :, None]

    ref = shards[0]
    out = {
        "l": ref["l"], "beta": ref["beta"], "n_therm": ref["n_therm"],
        "n_collected": nc,
        "smear_levels": ref["smear_levels"], "smear_alpha": ref["smear_alpha"],
        "n_overrelax": ref["n_overrelax"], "threads": ref["threads"],
        "meas_interval": ref["meas_interval"],
        "mean_op": op.tolist(),
        "corr": corr.tolist(),
        "n_bins": len(bin_counts), "bin_counts": bin_counts,
        "bin_op_sum": bin_op, "bin_corr_sum": bin_corr,
        "mean_op_E": op_e.tolist(), "corr_E": corr_e.tolist(),
        "bin_op_E_sum": bin_op_e, "bin_corr_E_sum": bin_corr_e,
    }
    out.update(_provenance(shards, nc))
    return out


def merge_sigma(shards: list[dict], paths: list[str]) -> dict:
    _check_consistent(shards, ["l", "beta", "r_max", "t_max", "meas_interval"], paths)
    nc = sum(sh["n_collected"] for sh in shards)
    if nc == 0:
        raise SystemExit("no collected configs across shards")

    bin_counts = [c for sh in shards for c in sh["bin_counts"]]
    bin_w = [m for sh in shards for m in sh["bin_w_sum"]]
    w = np.array(bin_w).sum(axis=0) / nc                    # [r_max][t_max]

    ref = shards[0]
    out = {
        "l": ref["l"], "beta": ref["beta"], "n_therm": ref["n_therm"],
        "n_collected": nc,
        "r_max": ref["r_max"], "t_max": ref["t_max"],
        "smear_steps": ref["smear_steps"], "smear_alpha": ref["smear_alpha"],
        "n_overrelax": ref["n_overrelax"], "threads": ref["threads"],
        "meas_interval": ref["meas_interval"],
        "w": w.tolist(),
        "n_bins": len(bin_counts), "bin_counts": bin_counts,
        "bin_w_sum": bin_w,
    }
    out.update(_provenance(shards, nc))
    return out


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out", required=True, help="merged JSON output path")
    ap.add_argument("shards", nargs="+", help="per-shard JSON files for one point")
    args = ap.parse_args()

    shards = _load(args.shards)
    kind = "glueball" if "corr" in shards[0] else "sigma" if "w" in shards[0] else None
    if kind is None:
        raise SystemExit(f"{args.shards[0]}: unrecognized schema (no 'corr' or 'w')")

    merged = merge_glueball(shards, args.shards) if kind == "glueball" \
        else merge_sigma(shards, args.shards)

    Path(args.out).write_text(json.dumps(merged))
    print(f"merged {len(shards)} {kind} shards -> {args.out}")
    print(f"  N_collected = {merged['n_collected']}  "
          f"(bins {merged['n_bins']}, shards {merged['n_shards']})")
    print(f"  wall {merged['elapsed_seconds']:.0f}s, "
          f"cpu {merged['total_cpu_seconds']:.0f}s across shards")


if __name__ == "__main__":
    main()
