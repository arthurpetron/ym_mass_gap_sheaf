"""Analyze a 0++ glueball correlation matrix from the Rust `glueball` binary.

Reads the JSON emitted by `simulations/src/bin/glueball.rs` (the connected
correlation matrix C_ij(tau) over a smeared-operator variational basis),
solves the generalized eigenvalue problem (GEVP) for the ground-state
principal correlator, extracts the effective mass m_eff(tau), identifies a
plateau, and reports the 0++ glueball mass in lattice units with a plot.

The GEVP C(tau) v = lambda(tau) C(tau0) v isolates the lowest state: the
principal eigenvalue decays as lambda_0(tau) ~ exp(-m_0 (tau - tau0)), so
m_eff(tau) = ln(lambda_0(tau)/lambda_0(tau+1)) plateaus at m_0.

Statistical errors: when the JSON carries per-bin sums (`bin_corr_sum`,
`bin_op_sum`, `bin_counts`), the mass error is a genuine delete-one jackknife
over configuration bins -- the whole GEVP/plateau pipeline is re-run on each
leave-one-out sample.  Older JSON without bins falls back to the (much weaker)
scatter-of-m_eff estimate and says so.

The mass is in lattice units (1/a).  Converting to the physical
m(0++)/sqrt(sigma) ratio (~3.74, Teper) additionally requires the string
tension sigma from a Wilson-loop measurement (the companion driver).

Usage:
    python -m computations.long_runs.glueball_analysis g.json
    python -m computations.long_runs.glueball_analysis g.json --tau0 1 --plot out.svg
    python -m computations.long_runs.glueball_analysis g.json --plateau-lo 2 --plateau-hi 5
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np


def load(path: str) -> dict:
    d = json.loads(Path(path).read_text())
    d["corr"] = np.asarray(d["corr"], dtype=float)  # [nlev, nlev, tau_max+1]
    if "bin_corr_sum" in d:
        d["bin_corr_sum"] = np.asarray(d["bin_corr_sum"], dtype=float)  # [nb,L,L,ntau]
        d["bin_op_sum"] = np.asarray(d["bin_op_sum"], dtype=float)      # [nb, nlev]
        d["bin_counts"] = np.asarray(d["bin_counts"], dtype=float)      # [nb]
    return d


def connected(corr_sum: np.ndarray, op_sum: np.ndarray, n: float) -> np.ndarray:
    """Rebuild the connected matrix C_ij(tau) = <O_i O_j>(tau) - <O_i><O_j>."""
    m = op_sum / n
    return corr_sum / n - (m[:, None] * m[None, :])[:, :, None]


def gevp_principal(corr: np.ndarray, tau0: int) -> np.ndarray:
    """Largest GEVP eigenvalue lambda_0(tau) for each tau (NaN if C(tau0) not PD)."""
    from scipy.linalg import eigh

    nlev, _, ntau = corr.shape
    c0 = 0.5 * (corr[:, :, tau0] + corr[:, :, tau0].T)
    w, v = np.linalg.eigh(c0)
    if w.min() <= 0:
        return np.full(ntau, np.nan)
    c0_invhalf = v @ np.diag(w ** -0.5) @ v.T
    lam0 = np.full(ntau, np.nan)
    for tau in range(ntau):
        ct = 0.5 * (corr[:, :, tau] + corr[:, :, tau].T)
        m = c0_invhalf @ ct @ c0_invhalf
        lam0[tau] = eigh(m, eigvals_only=True)[-1]
    return lam0


def effective_mass(series: np.ndarray) -> np.ndarray:
    """m_eff(tau) = ln(C(tau)/C(tau+1)); NaN where ill-defined."""
    m = np.full(len(series) - 1, np.nan)
    for tau in range(len(series) - 1):
        a, b = series[tau], series[tau + 1]
        if a > 0 and b > 0:
            m[tau] = np.log(a / b)
    return m


def meff_from_corr(corr: np.ndarray, tau0: int) -> np.ndarray:
    """GEVP principal correlator -> effective mass, with a most-smeared-diagonal
    fallback if C(tau0) is not positive-definite."""
    lam0 = gevp_principal(corr, tau0)
    if np.isfinite(lam0).any():
        return effective_mass(lam0)
    return effective_mass(corr[-1, -1, :])


def jk_err(samples: np.ndarray) -> float:
    """Delete-one jackknife error from leave-one-out samples."""
    s = samples[np.isfinite(samples)]
    if s.size < 2:
        return float("nan")
    return float(np.sqrt((s.size - 1) / s.size * np.sum((s - s.mean()) ** 2)))


def choose_window(
    meff: np.ndarray,
    meff_err: np.ndarray | None,
    lo: int,
    hi: int | None,
    rel_thresh: float,
    err_growth_max: float = 5.0,
) -> tuple[int, int]:
    """Plateau window: a contiguous run from `lo` of timeslices that carry real
    signal -- finite, positive, statistically significant (err/|m_eff| <=
    rel_thresh), and not past the signal/noise cliff.

    Noise-cliff guard (`err_growth_max`).  A plateau ends where the principal
    correlator turns over and the signal is lost; the symptom is the per-step
    jackknife error *exploding* (a sudden >Nx jump), not the value alone.
    Without this guard the window can swallow the first noise-dominated
    timeslice -- which sneaks past the per-point significance cut by a hair --
    inflating the plateau error and biasing the central value.  Two artifacts
    this fixes: the first-excited 0++ window auto-extending from [1,1] to [1,2]
    once higher statistics shrink the noisy tau=2 error just under rel_thresh
    (error blows up ~13x there), and the re-blocking drift where coarser blocks
    pull tau into the noise.  A *consistency* (pull) test does NOT discriminate
    here: the bad timeslice has such a large error that it reads as consistent,
    while a genuine plateau point with a small error can read as a mild outlier.
    The error-growth cliff is the robust separator.
    """
    ntau = len(meff)
    lo = max(1, lo)
    if hi is not None:
        return lo, min(hi, ntau - 1)

    def good(t: int) -> bool:
        if not (np.isfinite(meff[t]) and meff[t] > 0):
            return False
        if meff_err is not None:
            e = meff_err[t]
            return np.isfinite(e) and e <= rel_thresh * abs(meff[t])
        return True

    if not good(lo):
        return lo, lo
    h = lo
    while h + 1 <= ntau - 1 and good(h + 1):
        if meff_err is not None:
            e_prev, e_next = meff_err[h], meff_err[h + 1]
            if np.isfinite(e_prev) and e_prev > 0 and e_next > err_growth_max * e_prev:
                break  # signal/noise cliff: the plateau ends here
        h += 1
    return lo, h


def plateau_value(meff: np.ndarray, lo: int, hi: int) -> float:
    seg = meff[lo : hi + 1]
    seg = seg[np.isfinite(seg)]
    return float(seg.mean()) if seg.size else float("nan")


def analyze(d: dict, tau0: int, plat_lo: int, plat_hi: int | None, rel_thresh: float) -> dict:
    corr = d["corr"]
    nlev = corr.shape[0]
    meff_gevp = meff_from_corr(corr, tau0)
    meff_diag = [effective_mass(corr[i, i, :]) for i in range(nlev)]
    res = {"meff_gevp": meff_gevp, "meff_diag": meff_diag}

    if "bin_corr_sum" in d:
        bc, bo, cnt = d["bin_corr_sum"], d["bin_op_sum"], d["bin_counts"]
        nb = bc.shape[0]
        tot_c, tot_o, tot_n = bc.sum(0), bo.sum(0), cnt.sum()
        # one jackknife pass: rebuild the GEVP effective mass on each leave-one-out sample
        meff_samples = np.full((nb, len(meff_gevp)), np.nan)
        for k in range(nb):
            nk = tot_n - cnt[k]
            ck = connected(tot_c - bc[k], tot_o - bo[k], nk)
            meff_samples[k] = meff_from_corr(ck, tau0)
        meff_err = np.array([jk_err(meff_samples[:, t]) for t in range(len(meff_gevp))])
        lo, hi = choose_window(meff_gevp, meff_err, plat_lo, plat_hi, rel_thresh)
        m0_samples = np.array([plateau_value(meff_samples[k], lo, hi) for k in range(nb)])
        res["meff_err"] = meff_err
        res["m0_lattice_err"] = jk_err(m0_samples)
        res["n_bins"] = int(nb)
        res["err_kind"] = f"jackknife ({nb} bins)"
    else:
        res["meff_err"] = None
        lo, hi = choose_window(meff_gevp, None, plat_lo, plat_hi, rel_thresh)
        seg = meff_gevp[lo : hi + 1]
        seg = seg[np.isfinite(seg)]
        res["m0_lattice_err"] = (
            float(seg.std(ddof=1) / np.sqrt(seg.size)) if seg.size > 1 else float("nan")
        )
        res["err_kind"] = "m_eff scatter (no bins; weak)"

    res["plateau_window"] = (lo, hi)
    res["m0_lattice"] = plateau_value(meff_gevp, lo, hi)
    return res


def plot(d: dict, res: dict, out: str) -> str:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig, ax = plt.subplots(figsize=(8.0, 5.0))
    levels = d["smear_levels"]
    for i, meff in enumerate(res["meff_diag"]):
        taus = np.arange(len(meff)) + 0.0
        ax.plot(taus, meff, "o--", alpha=0.35, markersize=4, label=fr"diag, {levels[i]} smear")
    taus = np.arange(len(res["meff_gevp"]))
    if res.get("meff_err") is not None:
        ax.errorbar(taus, res["meff_gevp"], yerr=res["meff_err"], fmt="s-", color="black",
                    markersize=7, capsize=3, label="GEVP ground state (jackknife)")
    else:
        ax.plot(taus, res["meff_gevp"], "s-", color="black", markersize=7, label="GEVP ground state")
    m0, err = res["m0_lattice"], res["m0_lattice_err"]
    lo, hi = res["plateau_window"]
    if np.isfinite(m0):
        if np.isfinite(err):
            ax.axhspan(m0 - err, m0 + err, color="tab:green", alpha=0.2)
        ax.axhline(m0, color="tab:green", linewidth=1.5,
                   label=fr"plateau $m_0 a = {m0:.3f} \pm {err:.3f}$ ($\tau\in[{lo},{hi}]$)")
    ax.set_xlabel(r"Euclidean time separation $\tau$ (lattice units)")
    ax.set_ylabel(r"effective mass $m_{\mathrm{eff}}(\tau)\, a$")
    ax.set_title(fr"0$^{{++}}$ glueball, $L={d['l']}$, $\beta={d['beta']}$, {d['n_collected']} configs")
    ax.grid(True, alpha=0.3)
    ax.legend(fontsize=8)
    fig.tight_layout()
    target = Path(out)
    target.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(target, format="svg")
    plt.close(fig)
    return str(target)


def main() -> None:
    p = argparse.ArgumentParser(description="0++ glueball GEVP / effective-mass analysis.")
    p.add_argument("json", help="path to the glueball correlation-matrix JSON")
    p.add_argument("--tau0", type=int, default=1, help="GEVP reference time (default 1)")
    p.add_argument("--plateau-lo", type=int, default=1, help="plateau window lower tau")
    p.add_argument("--plateau-hi", type=int, default=None, help="plateau window upper tau (default: auto)")
    p.add_argument("--rel-thresh", type=float, default=0.5,
                   help="auto-window keeps taus with jackknife err/|m_eff| <= this (default 0.5)")
    p.add_argument("--plot", default=None, help="SVG output path (default alongside JSON)")
    args = p.parse_args()

    d = load(args.json)
    res = analyze(d, args.tau0, args.plateau_lo, args.plateau_hi, args.rel_thresh)
    lo, hi = res["plateau_window"]
    print(f"=== 0++ glueball (L={d['l']}, beta={d['beta']}, {d['n_collected']} configs) ===")
    print(f"  basis: smear levels {d['smear_levels']} @ alpha={d['smear_alpha']}")
    print(f"  GEVP effective mass m_eff(tau) a (tau0={args.tau0}):")
    err = res.get("meff_err")
    for t, mv in enumerate(res["meff_gevp"]):
        if np.isfinite(mv):
            e = f" +/- {err[t]:.4f}" if err is not None and np.isfinite(err[t]) else ""
            mark = "  <-- plateau" if lo <= t <= hi else ""
            print(f"    tau={t:>2}  m_eff = {mv:.4f}{e}{mark}")
    print(f"  plateau window tau in [{lo}, {hi}]  ({res['err_kind']})")
    print(f"  m_0 a (lattice units) = {res['m0_lattice']:.4f} +/- {res['m0_lattice_err']:.4f}")
    print("  (For m(0++)/sqrt(sigma) ~ 3.74 [Teper], divide by sqrt(sigma) a from")
    print("   the string-tension driver: ratio = (m_0 a) / sqrt(sigma a^2).)")

    out = args.plot or str(Path(args.json).with_suffix(".svg"))
    print(f"  SVG: {plot(d, res, out)}")


if __name__ == "__main__":
    main()
