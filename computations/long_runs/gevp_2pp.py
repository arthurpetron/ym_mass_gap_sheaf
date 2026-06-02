"""GEVP analysis of the 2++ glueball E channel.

Reads the JSON emitted by the (extended) Rust `glueball` binary, which carries
both the 0++ A_1 correlator (`corr`) and the 2++ E correlator (`corr_E`).  The
E channel has 2 operators per smear level (E_1, E_2 components of the cubic E
irrep, both spin-2), flattened as `[2*smear + comp]`.

Solves the GEVP C^E(tau) v = lambda(tau) C^E(tau0) v on the (2*nlev)x(2*nlev)
correlator, extracts the principal effective mass m_eff^{2++}(tau), identifies
a plateau, and reports m(2++) a in lattice units -- with a delete-one
configuration jackknife over the saved bins (the whole GEVP/plateau pipeline
re-run per leave-one-out sample, exactly like `glueball_analysis`).

Output: m(2++) a + jackknife err; combined with m(0++) a from the same JSON it
gives the ratio m(2++)/m(0++).  SU(2) continuum benchmark (Teper, etc.):
m(2++)/m(0++) ~ 1.45.

The remaining 2++ T_2 cubic irrep is NOT measured by this operator basis -- it
needs non-planar (clover) loops.  E ground-state mass = T_2 ground-state mass
in the continuum (the spin-2 multiplet), so E alone fixes m(2++).

Usage:
    python -m computations.long_runs.gevp_2pp glueball-L16-b2.4-2pp.json
    python -m computations.long_runs.gevp_2pp g.json --tau0 1 --plot out.svg
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np

from computations.long_runs import glueball_analysis as ga


def load(path: str) -> dict:
    d = json.loads(Path(path).read_text())
    d["corr"] = np.asarray(d["corr"], dtype=float)
    if "corr_E" not in d:
        raise SystemExit("this JSON has no `corr_E` field -- rebuild with the 2++ binary")
    d["corr_E"] = np.asarray(d["corr_E"], dtype=float)
    if "bin_corr_sum" in d:
        d["bin_corr_sum"] = np.asarray(d["bin_corr_sum"], dtype=float)
        d["bin_op_sum"] = np.asarray(d["bin_op_sum"], dtype=float)
        d["bin_counts"] = np.asarray(d["bin_counts"], dtype=float)
    if "bin_corr_E_sum" in d:
        d["bin_corr_E_sum"] = np.asarray(d["bin_corr_E_sum"], dtype=float)
        d["bin_op_E_sum"] = np.asarray(d["bin_op_E_sum"], dtype=float)
    return d


def connected_E(corr_sum: np.ndarray, op_sum: np.ndarray, n: float) -> np.ndarray:
    """Rebuild connected E correlator C^E_{ab}(tau) from unsubtracted sums."""
    m = op_sum / n
    return corr_sum / n - (m[:, None] * m[None, :])[:, :, None]


def analyze(d: dict, tau0: int, plat_lo: int, plat_hi: int | None, rel_thresh: float) -> dict:
    cE = d["corr_E"]
    meff_E = ga.meff_from_corr(cE, tau0)
    res = {"meff_2pp": meff_E}

    if "bin_corr_E_sum" in d:
        bc, bo, cnt = d["bin_corr_E_sum"], d["bin_op_E_sum"], d["bin_counts"]
        nb = bc.shape[0]
        tot_c, tot_o, tot_n = bc.sum(0), bo.sum(0), cnt.sum()
        meff_samples = np.full((nb, len(meff_E)), np.nan)
        for k in range(nb):
            nk = tot_n - cnt[k]
            ck = connected_E(tot_c - bc[k], tot_o - bo[k], nk)
            meff_samples[k] = ga.meff_from_corr(ck, tau0)
        meff_err = np.array([ga.jk_err(meff_samples[:, t]) for t in range(len(meff_E))])
        lo, hi = ga.choose_window(meff_E, meff_err, plat_lo, plat_hi, rel_thresh)
        m_samples = np.array([ga.plateau_value(meff_samples[k], lo, hi) for k in range(nb)])
        res["meff_2pp_err"] = meff_err
        res["m_2pp_lattice_err"] = ga.jk_err(m_samples)
        res["err_kind"] = f"jackknife ({nb} bins)"
    else:
        res["meff_2pp_err"] = None
        lo, hi = ga.choose_window(meff_E, None, plat_lo, plat_hi, rel_thresh)
        seg = meff_E[lo : hi + 1]
        seg = seg[np.isfinite(seg)]
        res["m_2pp_lattice_err"] = (
            float(seg.std(ddof=1) / np.sqrt(seg.size)) if seg.size > 1 else float("nan")
        )
        res["err_kind"] = "m_eff scatter (no bins; weak)"

    res["plateau_window"] = (lo, hi)
    res["m_2pp_lattice"] = ga.plateau_value(meff_E, lo, hi)
    return res


def plot(d: dict, res: dict, res_0pp: dict, out: str) -> str:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig, ax = plt.subplots(figsize=(8.0, 5.0))
    taus_E = np.arange(len(res["meff_2pp"]))
    if res.get("meff_2pp_err") is not None:
        ax.errorbar(taus_E, res["meff_2pp"], yerr=res["meff_2pp_err"], fmt="^-",
                    color="tab:red", markersize=7, capsize=3,
                    label="GEVP $2^{++}$ E-channel ground state")
    else:
        ax.plot(taus_E, res["meff_2pp"], "^-", color="tab:red", markersize=7,
                label="GEVP $2^{++}$ E-channel ground state")

    taus_A = np.arange(len(res_0pp["meff_gevp"]))
    if res_0pp.get("meff_err") is not None:
        ax.errorbar(taus_A, res_0pp["meff_gevp"], yerr=res_0pp["meff_err"], fmt="s-",
                    color="black", markersize=7, capsize=3, alpha=0.7,
                    label="GEVP $0^{++}$ ground state (for reference)")
    else:
        ax.plot(taus_A, res_0pp["meff_gevp"], "s-", color="black", markersize=7, alpha=0.7,
                label="GEVP $0^{++}$ ground state (for reference)")

    m2, e2 = res["m_2pp_lattice"], res["m_2pp_lattice_err"]
    lo, hi = res["plateau_window"]
    if np.isfinite(m2):
        ax.axhspan(m2 - (e2 if np.isfinite(e2) else 0),
                   m2 + (e2 if np.isfinite(e2) else 0), color="tab:red", alpha=0.18)
        ax.axhline(m2, color="tab:red", linewidth=1.5,
                   label=fr"plateau $m_{{2^{{++}}}} a = {m2:.3f} \pm {e2:.3f}$ "
                         fr"($\tau\in[{lo},{hi}]$)")
    m0 = res_0pp["m0_lattice"]
    if np.isfinite(m0):
        ax.axhline(m0, color="tab:green", linewidth=1.2, linestyle="--",
                   label=fr"$m_{{0^{{++}}}} a = {m0:.3f}$")

    ax.set_xlabel(r"Euclidean time $\tau$ (lattice units)")
    ax.set_ylabel(r"effective mass $m_{\mathrm{eff}}(\tau)\, a$")
    ax.set_title(fr"SU(2) $2^{{++}}$ (E-irrep) vs $0^{{++}}$, "
                 fr"$L={d['l']}$, $\beta={d['beta']}$, {d['n_collected']} configs")
    ax.grid(True, alpha=0.3)
    ax.legend(fontsize=8)
    fig.tight_layout()
    target = Path(out)
    target.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(target, format="svg")
    plt.close(fig)
    return str(target)


def main() -> None:
    p = argparse.ArgumentParser(description="2++ glueball (E channel) GEVP analysis.")
    p.add_argument("json", help="path to the extended glueball JSON (must carry corr_E)")
    p.add_argument("--tau0", type=int, default=1, help="GEVP reference time (default 1)")
    p.add_argument("--plateau-lo", type=int, default=1)
    p.add_argument("--plateau-hi", type=int, default=None)
    p.add_argument("--rel-thresh", type=float, default=0.5)
    p.add_argument("--plot", default=None)
    args = p.parse_args()

    d = load(args.json)
    res = analyze(d, args.tau0, args.plateau_lo, args.plateau_hi, args.rel_thresh)
    res_0pp = ga.analyze(d, args.tau0, args.plateau_lo, args.plateau_hi, args.rel_thresh)
    lo, hi = res["plateau_window"]

    print(f"=== 2++ glueball E channel (L={d['l']}, beta={d['beta']}, "
          f"{d['n_collected']} configs) ===")
    print(f"  E basis: 2*{len(d['smear_levels'])} = {2*len(d['smear_levels'])} ops "
          f"(2 cubic-E components per smear {d['smear_levels']} @ alpha={d['smear_alpha']})")
    err = res.get("meff_2pp_err")
    for t, mv in enumerate(res["meff_2pp"]):
        if np.isfinite(mv):
            e = f" +/- {err[t]:.4f}" if err is not None and np.isfinite(err[t]) else ""
            mark = "  <-- plateau" if lo <= t <= hi else ""
            print(f"    tau={t:>2}  m_eff = {mv:.4f}{e}{mark}")
    print(f"  plateau window tau in [{lo}, {hi}]  ({res['err_kind']})")
    m2, e2 = res["m_2pp_lattice"], res["m_2pp_lattice_err"]
    m0 = res_0pp["m0_lattice"]
    e0 = res_0pp["m0_lattice_err"]
    print(f"  m(2++) a = {m2:.4f} +/- {e2:.4f}")
    print(f"  m(0++) a = {m0:.4f} +/- {e0:.4f}   (from same configs)")
    if np.isfinite(m0) and m0 > 0 and np.isfinite(m2):
        r = m2 / m0
        re = r * np.sqrt((e2 / m2) ** 2 + (e0 / m0) ** 2) if (m2 > 0) else float("nan")
        print(f"  m(2++)/m(0++) = {r:.3f} +/- {re:.3f}   (SU(2) continuum, Teper: ~1.45)")
    if args.plot:
        print(f"  SVG: {plot(d, res, res_0pp, args.plot)}")


if __name__ == "__main__":
    main()
