"""Cross-relationships in the SU(2) lattice data (analysis-only, no new MCMC).

Mines the committed glueball / string-tension / plaquette JSONs for physical
relationships that the per-run analyzers do not surface on their own:

  (A) Asymptotic 2-loop scaling -- sqrt(sigma)/Lambda_L vs beta.  Constant iff
      the lattice runs correctly; the observed drift toward a stable value is
      the evidence that these couplings lie in the scaling window.
  (B) m_0 a vs sqrt(sigma) a -- a proportional fit localizes which observable
      carries the finite-volume anomaly (the beta=2.6/L=16 glueball deficit).
  (C) The fitted Cornell Coulomb/Luscher coefficient c vs the universal pi/12.
  (D) The plaquette scan as a finite-volume check (<P> is L-independent) and a
      specific-heat estimate d<P>/dbeta locating the strong->weak crossover.

Produces a 4-panel figure and a printed summary.

Usage:
    python -m computations.long_runs.data_relationships [--plot out.svg]
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import numpy as np

from computations.long_runs import glueball_analysis as gb
from computations.long_runs import string_tension_analysis as st

OUT = Path("visualizations/pilot/su2")

# (beta, L, glueball json, sigma json, Cornell rmin) -- the committed runs.
PAIRS = [
    (2.30, 12, "glueball-L12-b2.3.json", "sigma-L12-b2.3.json", 2),
    (2.40, 16, "glueball-L16-b2.4-hi.json", "sigma-L16-b2.4.json", 3),
    (2.45, 18, "glueball-L18-b2.45.json", "sigma-L18-b2.45.json", 3),
    (2.50, 16, "glueball-L16-b2.5.json", "sigma-L16-b2.5.json", 3),
    (2.60, 16, "glueball-L16-b2.6.json", "sigma-L16-b2.6.json", 3),
]

# Two-loop lattice Lambda parameter for SU(2) (pure gauge, Wilson, beta=4/g^2).
N = 2
B0 = 11 * N / (48 * math.pi**2)            # 11/(24 pi^2)
B1 = 34 * N**2 / (3 * (16 * math.pi**2)**2)  # 17/(96 pi^4)


def a_lambda(beta: float) -> float:
    g2 = 4.0 / beta
    return (B0 * g2) ** (-B1 / (2 * B0**2)) * math.exp(-1.0 / (2 * B0 * g2))


def collect() -> list[dict]:
    rows = []
    for beta, L, gf, sf, rmin in PAIRS:
        gd = gb.load(str(OUT / gf))
        gr = gb.analyze(gd, 1, 1, None, 0.5)
        sd = st.load(str(OUT / sf))
        _, sig, c, _ = st.fit_cornell(st.static_potential(sd["w"]), rmin)
        rows.append(dict(
            beta=beta, L=L, rsa=math.sqrt(sig), m0=gr["m0_lattice"],
            m0e=gr["m0_lattice_err"], c=c, plat=gr["plateau_window"],
            ratio=gr["m0_lattice"] / math.sqrt(sig), sLam=math.sqrt(sig) / a_lambda(beta),
        ))
    return rows


def plaquette_scan() -> tuple[list[float], dict, dict]:
    d = json.loads((OUT / "mcmc-continuum-scan.json").read_text())

    def find(o):
        if isinstance(o, list) and o and isinstance(o[0], dict) and "plaquette_mean" in o[0]:
            return o
        if isinstance(o, dict):
            for v in o.values():
                r = find(v)
                if r:
                    return r
        return None

    pts = find(d)
    betas = sorted({p["beta"] for p in pts})
    pbar = {b: float(np.mean([p["plaquette_mean"] for p in pts if p["beta"] == b])) for b in betas}
    spread = {b: float(max(p["plaquette_mean"] for p in pts if p["beta"] == b)
                       - min(p["plaquette_mean"] for p in pts if p["beta"] == b)) for b in betas}
    return betas, pbar, spread


def main() -> None:
    ap = argparse.ArgumentParser(description="SU(2) lattice cross-relationships.")
    ap.add_argument("--plot", default=str(OUT / "data-relationships.svg"))
    args = ap.parse_args()

    rows = collect()
    L16 = [r for r in rows if r["L"] == 16]
    print("beta   L   sqrt(s)a   m0a      ratio    c        sqrt(s)/Lambda_L  plateau")
    for r in rows:
        print(f"{r['beta']:.2f}  {r['L']:>2}   {r['rsa']:.4f}    {r['m0']:.4f}   "
              f"{r['ratio']:.3f}    {r['c']:+.3f}   {r['sLam']:.1f}             {r['plat']}")

    sl = [r["sLam"] for r in L16]
    print(f"\n(A) sqrt(sigma)/Lambda_L over L=16 (beta 2.4-2.6): "
          f"{[round(x,1) for x in sl]} -> drift {max(sl)/min(sl)-1:+.0%}")

    xs = np.array([r["rsa"] for r in L16]); ys = np.array([r["m0"] for r in L16])
    k = float(np.sum(xs * ys) / np.sum(xs * xs))
    print(f"(B) m0a = {k:.3f}*sqrt(s)a (L=16); residuals:")
    for r in L16:
        print(f"    beta={r['beta']:.2f} resid={r['m0']-k*r['rsa']:+.3f}")

    cs = [r["c"] for r in rows]
    print(f"(C) Cornell c: mean {np.mean(cs):.3f} +/- {np.std(cs, ddof=1):.3f} vs pi/12={math.pi/12:.3f}")

    betas, pbar, spread = plaquette_scan()
    dP = [( (pbar[betas[i+1]]-pbar[betas[i]]) / (betas[i+1]-betas[i]),
            0.5*(betas[i]+betas[i+1]) ) for i in range(len(betas)-1)]
    print(f"(D) <P> L-spread <= {max(spread.values()):.4f}; d<P>/dbeta peak at "
          f"beta~{max(dP)[1]:.2f} ({max(dP)[0]:.3f})")

    _plot(rows, L16, k, cs, betas, pbar, dP, args.plot)
    print(f"\nSVG: {args.plot}")


def _plot(rows, L16, k, cs, betas, pbar, dP, out):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig, ax = plt.subplots(2, 2, figsize=(11, 8.6))

    for r in rows:
        mk = "o" if r["L"] == 16 else "^"
        ax[0, 0].plot(r["beta"], r["sLam"], mk, color="tab:blue", markersize=9)
        ax[0, 0].annotate(f"L{r['L']}", (r["beta"], r["sLam"]),
                          textcoords="offset points", xytext=(5, 4), fontsize=8)
    ax[0, 0].axhline(44, color="tab:red", ls="--",
                     label=r"established SU(2) $\sqrt{\sigma}/\Lambda_L\approx44$")
    ax[0, 0].set_xlabel(r"$\beta$"); ax[0, 0].set_ylabel(r"$\sqrt{\sigma}/\Lambda_L$ (2-loop)")
    ax[0, 0].set_title(r"(A) asymptotic scaling: drifts toward the known value as $a\to0$")
    ax[0, 0].legend(fontsize=8); ax[0, 0].grid(alpha=0.3)

    xs = np.linspace(0, max(r["rsa"] for r in L16) * 1.1, 50)
    ax[0, 1].plot(xs, k * xs, "--", color="gray", label=fr"$m_0a={k:.2f}\,\sqrt{{\sigma}}a$ (L16)")
    for r in rows:
        col = "tab:red" if (r["L"] == 16 and abs(r["beta"] - 2.6) < 1e-6) else "tab:blue"
        ax[0, 1].errorbar(r["rsa"], r["m0"], yerr=r["m0e"], fmt="o", color=col, markersize=8, capsize=3)
        ax[0, 1].annotate(fr"$\beta${r['beta']}", (r["rsa"], r["m0"]),
                          textcoords="offset points", xytext=(5, -10), fontsize=8)
    ax[0, 1].set_xlabel(r"$\sqrt{\sigma}\,a$"); ax[0, 1].set_ylabel(r"$m_0 a$")
    ax[0, 1].set_title(r"(B) $m_0a$ vs $\sqrt{\sigma}a$: $\beta$=2.6 glueball falls below (torelon)")
    ax[0, 1].legend(fontsize=8); ax[0, 1].grid(alpha=0.3)

    ax[1, 0].axhline(math.pi / 12, color="tab:green", ls="--", label=r"universal $\pi/12=0.262$")
    ax[1, 0].axhline(float(np.mean(cs)), color="tab:purple", ls=":", alpha=0.7,
                     label=fr"mean $={np.mean(cs):.3f}$")
    ax[1, 0].plot([r["beta"] for r in rows], cs, "o", color="tab:purple", markersize=8)
    ax[1, 0].set_xlabel(r"$\beta$"); ax[1, 0].set_ylabel(r"fitted Cornell $c$")
    ax[1, 0].set_title(r"(C) L\"uscher coefficient: mean $\sim\pi/12$, individually noisy")
    ax[1, 0].legend(fontsize=8); ax[1, 0].grid(alpha=0.3)

    axb = ax[1, 1]; axt = axb.twinx()
    axb.plot(list(pbar), [pbar[b] for b in pbar], "o-", color="tab:blue")
    axt.plot([d[1] for d in dP], [d[0] for d in dP], "s--", color="tab:orange")
    axt.axvline(2.2, color="tab:red", ls=":", alpha=0.6)
    axb.set_xlabel(r"$\beta$"); axb.set_ylabel(r"$\langle P\rangle$", color="tab:blue")
    axt.set_ylabel(r"$d\langle P\rangle/d\beta$", color="tab:orange")
    axb.set_title(r"(D) plaquette: crossover peak $\beta\approx2.2$ ($L$-indep to $<0.3\%$)")
    axb.grid(alpha=0.3)

    fig.tight_layout()
    Path(out).parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out, format="svg")
    plt.close(fig)


if __name__ == "__main__":
    main()
