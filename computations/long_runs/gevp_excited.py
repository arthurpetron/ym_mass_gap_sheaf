"""First-excited 0++ state from the glueball GEVP (re-analysis, no new run).

`glueball_analysis` solves the generalized eigenvalue problem
C(tau) v = lambda(tau) C(tau0) v and keeps only the largest eigenvalue
lambda_0(tau) -> ground-state mass m_0.  The SAME GEVP delivers the next
eigenvalue lambda_1(tau) -> first-excited 0++ mass m_1, for free, from the
existing correlation matrices.  This module extracts m_1 a and the gap
(m_1 - m_0) a with a delete-one jackknife over the saved configuration bins,
re-running the two-state GEVP on every leave-one-out sample.

Why it matters: a clean separation m_1 > m_0 with the ground state on a
plateau is direct evidence that the GEVP has isolated a single lowest state
(not a mixture) -- i.e. that m_0 a really is "the gap" in this channel, not an
artifact of operator overlap.

The excited state is noisier than the ground state and needs C(tau0) to expose
at least two positive eigenvalues; where it cannot, the value is reported NaN.

Usage:
    python -m computations.long_runs.gevp_excited glueball-L16-b2.4-hi.json
    python -m computations.long_runs.gevp_excited g.json --tau0 1 --plot out.svg
"""

from __future__ import annotations

import argparse
from pathlib import Path

import numpy as np

from computations.long_runs import glueball_analysis as ga


def gevp_eigs(corr: np.ndarray, tau0: int, k: int) -> np.ndarray:
    """Top-`k` GEVP eigenvalues lambda_n(tau), descending, for each tau.

    Solves the symmetric-definite problem C(tau) v = lambda C(tau0) v by
    whitening with C(tau0)^{-1/2}.  Returns shape (k, ntau); rows beyond the
    available positive spectrum, or taus where C(tau0) is not PD, are NaN."""
    from scipy.linalg import eigh

    nlev, _, ntau = corr.shape
    c0 = 0.5 * (corr[:, :, tau0] + corr[:, :, tau0].T)
    w, v = np.linalg.eigh(c0)
    out = np.full((k, ntau), np.nan)
    if w.min() <= 0:
        return out
    c0_invhalf = v @ np.diag(w ** -0.5) @ v.T
    for tau in range(ntau):
        ct = 0.5 * (corr[:, :, tau] + corr[:, :, tau].T)
        m = c0_invhalf @ ct @ c0_invhalf
        ev = np.sort(eigh(m, eigvals_only=True))[::-1]  # descending
        out[: min(k, ev.size), tau] = ev[: min(k, ev.size)]
    return out


def meff_levels(corr: np.ndarray, tau0: int, k: int) -> np.ndarray:
    """Effective mass m_n(tau) = ln(lambda_n(tau)/lambda_n(tau+1)) for top-k."""
    lams = gevp_eigs(corr, tau0, k)
    out = np.full((k, lams.shape[1] - 1), np.nan)
    for n in range(k):
        out[n] = ga.effective_mass(lams[n])
    return out


def plateau(meff: np.ndarray, lo: int, hi: int) -> float:
    return ga.plateau_value(meff, lo, hi)


def analyze(d: dict, tau0: int, plat_lo: int, plat_hi: int | None, rel_thresh: float) -> dict:
    corr = d["corr"]
    # reuse the ground-state window logic from glueball_analysis
    base = ga.analyze(d, tau0, plat_lo, plat_hi, rel_thresh)
    lo, hi = base["plateau_window"]

    meff = meff_levels(corr, tau0, 2)
    m0, m1 = plateau(meff[0], lo, hi), plateau(meff[1], lo, hi)

    res = {
        "m0_lattice": m0,
        "m1_lattice": m1,
        "gap_lattice": (m1 - m0) if (np.isfinite(m0) and np.isfinite(m1)) else float("nan"),
        "plateau_window": (lo, hi),
        "meff": meff,
    }

    if "bin_corr_sum" in d:
        bc, bo, cnt = d["bin_corr_sum"], d["bin_op_sum"], d["bin_counts"]
        nb = bc.shape[0]
        tot_c, tot_o, tot_n = bc.sum(0), bo.sum(0), cnt.sum()
        m1_s = np.full(nb, np.nan)
        gap_s = np.full(nb, np.nan)
        for kk in range(nb):
            nk = tot_n - cnt[kk]
            ck = ga.connected(tot_c - bc[kk], tot_o - bo[kk], nk)
            mk = meff_levels(ck, tau0, 2)
            mk0, mk1 = plateau(mk[0], lo, hi), plateau(mk[1], lo, hi)
            m1_s[kk] = mk1
            gap_s[kk] = mk1 - mk0
        res["m1_lattice_err"] = ga.jk_err(m1_s)
        res["gap_lattice_err"] = ga.jk_err(gap_s)
        res["err_kind"] = f"jackknife ({nb} bins)"
    else:
        res["m1_lattice_err"] = float("nan")
        res["gap_lattice_err"] = float("nan")
        res["err_kind"] = "no bins"
    return res


def plot(d: dict, res: dict, out: str) -> str:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    meff = res["meff"]
    lo, hi = res["plateau_window"]
    taus = np.arange(meff.shape[1])
    fig, ax = plt.subplots(figsize=(8.0, 5.0))
    ax.plot(taus, meff[0], "s-", color="black", markersize=7, label="GEVP ground state $m_0$")
    ax.plot(taus, meff[1], "^--", color="tab:red", markersize=7, label="GEVP first excited $m_1$")
    for val, col, lab in ((res["m0_lattice"], "tab:green", "m_0"),
                          (res["m1_lattice"], "tab:orange", "m_1")):
        if np.isfinite(val):
            ax.axhline(val, color=col, linewidth=1.2, alpha=0.8)
    ax.axvspan(lo, hi, color="tab:green", alpha=0.08, label=fr"plateau $\tau\in[{lo},{hi}]$")
    ax.set_xlabel(r"Euclidean time $\tau$ (lattice units)")
    ax.set_ylabel(r"effective mass $m_n(\tau)\, a$")
    ax.set_title(
        fr"0$^{{++}}$ GEVP ground + first excited, $L={d['l']}$, $\beta={d['beta']}$, "
        fr"{d['n_collected']} configs"
    )
    ax.grid(True, alpha=0.3)
    ax.legend(fontsize=8)
    fig.tight_layout()
    target = Path(out)
    target.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(target, format="svg")
    plt.close(fig)
    return str(target)


def main() -> None:
    p = argparse.ArgumentParser(description="First-excited 0++ from the glueball GEVP.")
    p.add_argument("json")
    p.add_argument("--tau0", type=int, default=1)
    p.add_argument("--plateau-lo", type=int, default=1)
    p.add_argument("--plateau-hi", type=int, default=None)
    p.add_argument("--rel-thresh", type=float, default=0.5)
    p.add_argument("--plot", default=None)
    args = p.parse_args()

    d = ga.load(args.json)
    res = analyze(d, args.tau0, args.plateau_lo, args.plateau_hi, args.rel_thresh)
    lo, hi = res["plateau_window"]
    print(f"=== 0++ GEVP ground + first excited (L={d['l']}, beta={d['beta']}, "
          f"{d['n_collected']} configs) ===")
    print(f"  basis: smear levels {d['smear_levels']} @ alpha={d['smear_alpha']}")
    print(f"  plateau window tau in [{lo},{hi}]  ({res['err_kind']})")
    print(f"  m_0 a = {res['m0_lattice']:.4f}")
    print(f"  m_1 a = {res['m1_lattice']:.4f} +/- {res['m1_lattice_err']:.4f}")
    print(f"  gap (m_1 - m_0) a = {res['gap_lattice']:.4f} +/- {res['gap_lattice_err']:.4f}")
    if np.isfinite(res["m1_lattice"]) and np.isfinite(res["m0_lattice"]) and res["m0_lattice"] > 0:
        print(f"  m_1 / m_0 = {res['m1_lattice']/res['m0_lattice']:.3f}  "
              "(clean separation > 1 => ground state is well isolated)")
    if args.plot:
        print(f"  SVG: {plot(d, res, args.plot)}")


if __name__ == "__main__":
    main()
