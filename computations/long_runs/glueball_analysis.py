"""Analyze a 0++ glueball correlation matrix from the Rust `glueball` binary.

Reads the JSON emitted by `simulations/src/bin/glueball.rs` (the connected
correlation matrix C_ij(tau) over a smeared-operator variational basis),
solves the generalized eigenvalue problem (GEVP) for the ground-state
principal correlator, extracts the effective mass m_eff(tau), identifies a
plateau, and reports the 0++ glueball mass in lattice units with a plot.

The GEVP C(tau) v = lambda(tau) C(tau0) v isolates the lowest state: the
principal eigenvalue decays as lambda_0(tau) ~ exp(-m_0 (tau - tau0)), so
m_eff(tau) = ln(lambda_0(tau)/lambda_0(tau+1)) plateaus at m_0.

The mass is in lattice units (1/a).  Converting to the physical m(0++)/sqrt(sigma)
ratio (~3.74, Teper) additionally requires the string tension sigma from a
Wilson-loop measurement (the companion driver); this script reports m_0 a and
flags that sigma is needed for the dimensionless ratio.

Usage:
    python -m computations.long_runs.glueball_analysis /tmp/glueball_L16.json
    python -m computations.long_runs.glueball_analysis g.json --tau0 1 --plot out.svg
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np


def load_corr(path: str) -> dict:
    d = json.loads(Path(path).read_text())
    d["corr"] = np.asarray(d["corr"], dtype=float)  # [nlev, nlev, tau_max+1]
    return d


def gevp_principal(corr: np.ndarray, tau0: int) -> np.ndarray:
    """Largest GEVP eigenvalue lambda_0(tau) for each tau, normalized to 1 at tau0.

    Solves C(tau) v = lambda C(tau0) v via the symmetric reduction
    C(tau0)^{-1/2} C(tau) C(tau0)^{-1/2}.  Falls back to NaN where C(tau0) is
    not positive-definite.
    """
    from scipy.linalg import eigh

    nlev, _, ntau = corr.shape
    c0 = 0.5 * (corr[:, :, tau0] + corr[:, :, tau0].T)
    evals0 = np.linalg.eigvalsh(c0)
    if evals0.min() <= 0:
        # not positive-definite; restrict to the dominant operator only
        return np.full(ntau, np.nan)
    # C(tau0)^{-1/2}
    w, v = np.linalg.eigh(c0)
    c0_invhalf = v @ np.diag(w ** -0.5) @ v.T
    lam0 = np.full(ntau, np.nan)
    for tau in range(ntau):
        ct = 0.5 * (corr[:, :, tau] + corr[:, :, tau].T)
        m = c0_invhalf @ ct @ c0_invhalf
        ev = eigh(m, eigvals_only=True)
        lam0[tau] = ev[-1]  # largest
    return lam0


def effective_mass(series: np.ndarray) -> np.ndarray:
    """m_eff(tau) = ln(C(tau)/C(tau+1)); NaN where ill-defined."""
    m = np.full(len(series) - 1, np.nan)
    for tau in range(len(series) - 1):
        a, b = series[tau], series[tau + 1]
        if a > 0 and b > 0:
            m[tau] = np.log(a / b)
    return m


def fit_plateau(meff: np.ndarray, lo: int, hi: int) -> tuple[float, float]:
    """Constant fit (unweighted mean ± std-of-mean) of m_eff over [lo, hi]."""
    seg = meff[lo : hi + 1]
    seg = seg[np.isfinite(seg)]
    if seg.size == 0:
        return float("nan"), float("nan")
    return float(seg.mean()), float(seg.std(ddof=1) / np.sqrt(seg.size)) if seg.size > 1 else 0.0


def analyze(d: dict, tau0: int) -> dict:
    corr = d["corr"]
    nlev = corr.shape[0]
    # GEVP ground-state principal correlator
    lam0 = gevp_principal(corr, tau0)
    meff_gevp = effective_mass(lam0) if np.isfinite(lam0).any() else None
    # diagonal effective masses (each smearing level)
    meff_diag = [effective_mass(corr[i, i, :]) for i in range(nlev)]
    # most-smeared operator is the best single-operator proxy
    meff_best = meff_diag[-1]
    # plateau: prefer GEVP if available, else best diagonal
    src = meff_gevp if meff_gevp is not None else meff_best
    ntau = len(src)
    # plateau window: skip tau=0 (contact term), use the middle
    lo = max(1, tau0)
    hi = min(ntau - 1, lo + max(1, ntau // 2))
    m0, m0_err = fit_plateau(src, lo, hi)
    return {
        "lam0": lam0,
        "meff_gevp": meff_gevp,
        "meff_diag": meff_diag,
        "plateau_window": (lo, hi),
        "m0_lattice": m0,
        "m0_lattice_err": m0_err,
        "used": "GEVP" if meff_gevp is not None else "diagonal(most-smeared)",
    }


def plot(d: dict, res: dict, out: str) -> str:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig, ax = plt.subplots(figsize=(8.0, 5.0))
    levels = d["smear_levels"]
    for i, meff in enumerate(res["meff_diag"]):
        taus = np.arange(len(meff)) + 0.0
        ax.plot(taus, meff, "o--", alpha=0.4, markersize=4,
                label=fr"diag, {levels[i]} smear")
    if res["meff_gevp"] is not None:
        taus = np.arange(len(res["meff_gevp"]))
        ax.plot(taus, res["meff_gevp"], "s-", color="black", markersize=7,
                label="GEVP ground state")
    m0 = res["m0_lattice"]
    err = res["m0_lattice_err"]
    lo, hi = res["plateau_window"]
    if np.isfinite(m0):
        ax.axhspan(m0 - err, m0 + err, xmin=0, xmax=1, color="tab:green", alpha=0.2)
        ax.axhline(m0, color="tab:green", linestyle="-", linewidth=1.5,
                   label=fr"plateau $m_0 a = {m0:.3f} \pm {err:.3f}$ ($\tau\in[{lo},{hi}]$)")
    ax.set_xlabel(r"Euclidean time separation $\tau$ (lattice units)")
    ax.set_ylabel(r"effective mass $m_{\mathrm{eff}}(\tau)\, a$")
    ax.set_title(
        fr"0$^{{++}}$ glueball, $L={d['l']}$, $\beta={d['beta']}$, "
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
    p = argparse.ArgumentParser(description="0++ glueball GEVP / effective-mass analysis.")
    p.add_argument("json", help="path to the glueball correlation-matrix JSON")
    p.add_argument("--tau0", type=int, default=1, help="GEVP reference time (default 1)")
    p.add_argument("--plot", default=None, help="SVG output path (default alongside JSON)")
    args = p.parse_args()

    d = load_corr(args.json)
    res = analyze(d, args.tau0)
    print(f"=== 0++ glueball (L={d['l']}, beta={d['beta']}, {d['n_collected']} configs) ===")
    print(f"  basis: smear levels {d['smear_levels']} @ alpha={d['smear_alpha']}")
    print(f"  estimator: {res['used']}, plateau window tau in {res['plateau_window']}")
    print(f"  m_0 a (lattice units) = {res['m0_lattice']:.4f} +/- {res['m0_lattice_err']:.4f}")
    print("  (For m(0++)/sqrt(sigma) ~ 3.74 [Teper], measure the string tension")
    print("   sigma via Wilson loops; m_0 a / sqrt(sigma a^2) gives the ratio.)")

    out = args.plot or str(Path(args.json).with_suffix(".svg"))
    svg = plot(d, res, out)
    print(f"  SVG: {svg}")


if __name__ == "__main__":
    main()
