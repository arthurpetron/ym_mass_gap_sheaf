"""Extract the SU(2) string tension from a Wilson-loop grid.

Reads the JSON emitted by `simulations/src/bin/string_tension.rs` (the
rectangular Wilson loops W(R,T)) and extracts the string tension sigma
(in lattice units, i.e. sigma * a^2) two independent ways:

  1. Creutz ratios  chi(r,r) = -ln[ W(r,r) W(r-1,r-1) / (W(r-1,r) W(r,r-1)) ],
     which cancel the perimeter and corner terms and tend to sigma a^2 at
     large r.

  2. Static potential  V(r) = lim_{t->inf} ln[ W(r,t)/W(r,t+1) ], fit to the
     Cornell form V(r) = V0 + sigma*r - c/r; the linear slope is sigma a^2.

The headline output is sqrt(sigma) * a (i.e. sqrt(sigma a^2)).  Combined with
a glueball mass m_0 a from the companion driver, the dimensionless ratio
m(0++)/sqrt(sigma) = (m_0 a) / sqrt(sigma a^2) can be set against the lattice
value ~3.74 (Teper) -- and sigma calibrates the constructive m_0 >= 0.999,
which is quoted in units of sqrt(sigma_0).

Usage:
    python -m computations.long_runs.string_tension_analysis s.json
    python -m computations.long_runs.string_tension_analysis s.json --plot out.svg
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import numpy as np


def load(path: str) -> dict:
    d = json.loads(Path(path).read_text())
    d["w"] = np.asarray(d["w"], dtype=float)  # w[r-1][t-1] = W(r, t)
    return d


def creutz_ratios(w: np.ndarray) -> dict[int, float]:
    """chi(r,r) for r = 2..r_max (lattice-unit string tension estimates)."""
    r_max = w.shape[0]
    out = {}
    for r in range(2, r_max + 1):
        # W(a,b) = w[a-1][b-1]
        num = w[r - 1, r - 1] * w[r - 2, r - 2]
        den = w[r - 1, r - 2] * w[r - 2, r - 1]
        if num > 0 and den > 0:
            out[r] = -math.log(num / den)
    return out


def static_potential(w: np.ndarray) -> dict[int, float]:
    """V(r) from the largest-t effective mass ln[W(r,t)/W(r,t+1)]."""
    r_max, t_max = w.shape
    out = {}
    for r in range(1, r_max + 1):
        # use the largest t with positive, decreasing signal
        best = None
        for t in range(1, t_max):
            a, b = w[r - 1, t - 1], w[r - 1, t]
            if a > 0 and b > 0 and a > b:
                best = math.log(a / b)
        if best is not None:
            out[r] = best
    return out


def fit_cornell(vr: dict[int, float], rmin: int) -> tuple[float, float, float, float]:
    """Fit V(r) = V0 + sigma r - c/r over r >= rmin.  Returns (V0, sigma, c, sigma_err)."""
    from scipy.optimize import curve_fit

    rs = np.array([r for r in sorted(vr) if r >= rmin], dtype=float)
    vs = np.array([vr[int(r)] for r in rs], dtype=float)
    if rs.size < 3:
        # too few points: fix the Luscher coefficient c = pi/12
        c = math.pi / 12.0

        def f2(r, v0, sigma):
            return v0 + sigma * r - c / r

        if rs.size < 2:
            return (float("nan"),) * 4
        popt, pcov = curve_fit(f2, rs, vs)
        return popt[0], popt[1], c, float(np.sqrt(pcov[1, 1]))

    def f3(r, v0, sigma, c):
        return v0 + sigma * r - c / r

    popt, pcov = curve_fit(f3, rs, vs, p0=[0.5, 0.1, math.pi / 12.0])
    return popt[0], popt[1], popt[2], float(np.sqrt(pcov[1, 1]))


def plot(d, creutz, vr, fit, out: str) -> str:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    v0, sigma, c, sig_err = fit
    fig, (axc, axv) = plt.subplots(1, 2, figsize=(11.0, 4.6))

    # Creutz ratios
    rs = sorted(creutz)
    axc.plot(rs, [creutz[r] for r in rs], "o-", color="tab:blue")
    if np.isfinite(sigma):
        axc.axhline(sigma, color="tab:green", linestyle="--",
                    label=fr"potential-fit $\sigma a^2 = {sigma:.4f}$")
    axc.set_xlabel(r"$r$ (lattice units)")
    axc.set_ylabel(r"Creutz ratio $\chi(r,r) \to \sigma a^2$")
    axc.set_title("Creutz ratios")
    axc.grid(True, alpha=0.3)
    axc.legend(fontsize=8)

    # static potential + fit
    rsv = np.array(sorted(vr), dtype=float)
    axv.plot(rsv, [vr[int(r)] for r in rsv], "s", color="tab:red", label="V(r) (lattice)")
    if np.isfinite(sigma):
        rr = np.linspace(rsv.min(), rsv.max(), 100)
        axv.plot(rr, v0 + sigma * rr - c / rr, "-", color="black",
                 label=fr"Cornell fit $V_0 + \sigma r - c/r$: $\sigma a^2={sigma:.4f}$")
    axv.set_xlabel(r"$r$ (lattice units)")
    axv.set_ylabel(r"static potential $V(r)\, a$")
    axv.set_title("Static quark potential")
    axv.grid(True, alpha=0.3)
    axv.legend(fontsize=8)

    fig.suptitle(fr"SU(2) string tension, $L={d['l']}$, $\beta={d['beta']}$, {d['n_collected']} configs")
    fig.tight_layout()
    target = Path(out)
    target.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(target, format="svg")
    plt.close(fig)
    return str(target)


def main() -> None:
    p = argparse.ArgumentParser(description="SU(2) string-tension extraction.")
    p.add_argument("json")
    p.add_argument("--rmin", type=int, default=2, help="min r for the Cornell fit (default 2)")
    p.add_argument("--plot", default=None)
    args = p.parse_args()

    d = load(args.json)
    w = d["w"]
    creutz = creutz_ratios(w)
    vr = static_potential(w)
    fit = fit_cornell(vr, args.rmin)
    v0, sigma, c, sig_err = fit

    print(f"=== SU(2) string tension (L={d['l']}, beta={d['beta']}, {d['n_collected']} configs) ===")
    print("  Creutz ratios chi(r,r) [-> sigma a^2 at large r]:")
    for r in sorted(creutz):
        print(f"    chi({r},{r}) = {creutz[r]:.5f}   sqrt = {max(creutz[r],0)**0.5:.4f}")
    print(f"  Cornell fit (r >= {args.rmin}):  V0={v0:.4f}  sigma a^2={sigma:.5f} +/- {sig_err:.5f}  c={c:.4f}")
    if np.isfinite(sigma) and sigma > 0:
        print(f"  => sqrt(sigma) a = {math.sqrt(sigma):.5f}  (lattice units)")
        print(f"     With a glueball m_0 a, the ratio m(0++)/sqrt(sigma) = (m_0 a)/{math.sqrt(sigma):.5f}.")
    out = args.plot or str(Path(args.json).with_suffix(".svg"))
    print(f"  SVG: {plot(d, creutz, vr, fit, out)}")


if __name__ == "__main__":
    main()
