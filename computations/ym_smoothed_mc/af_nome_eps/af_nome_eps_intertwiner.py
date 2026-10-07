#!/usr/bin/env python3
"""
afNomeSchedule lit ε_j under both ApproxRgIntertwiner shapes (0++/√σ proxy).

Lit/MC only — NOT a proof of RG summability, intertwiner inhabitability, or AF.

Reuses a√σ knots from sibling af_nome_asqrt/ (commit a10b9ea4 sources):
  schedule 1-w_j = A/(j+κ⌊log2(j+1)⌋+4), A=1.942, κ=51/121;
  β=-1/(2 ln w); a√σ from FHK/UKQCD/two-loop as before.

Continuum-inspired PROXY (not a measured VacSq rate):
  μ = m(0++)/√σ  (continuum SU(2) lit)
  Δ_j = μ · (a√σ)_j
  λ_j = exp(−Δ_j)   # one-step transfer eigenvalue proxy for r_j

Lean RgRateRelation (κ-free):  rFine² ≤ rCoarse + ε
  ⇒ ε_needed = max(0, rFine² − rCoarse); also report signed defect.

κ-form (κ=1 lit probe): r_F² = κ(r_C²+ε) ⇒ ε_needed_κ = max(0, rFine² − rCoarse²).

Shape A — intertwine T_{j+1} ↔ T_j (unequal physical time):
  rFine=λ_{j+1}, rCoarse=λ_j
  ε^A_κfree, ε^A_κ as above.

Shape B — intertwine T_{j+1}² ↔ T_j (physical-time matched when a halves):
  continuum ideal λ_{j+1}² ≈ λ_j when a_{j+1}/a_j = 1/2
  ε^B = max(0, λ_{j+1}² − λ_j)  # same algebra as A κ-free; Lean-preferred matching
  also |λ_{j+1}² − λ_j| and a-ratio.

Weighted sums (Lean weightedErrorSum):
  S_n = Σ_{k=0}^{n-1} 2^k · ε(j0+k)   with j0=4, n=4 (steps 4→5..7→8)
Project-status form: Σ_{j=4}^{7} 2^j · ε_j

CPU-light; no Monte Carlo. Leave P11 multilevel job untouched.
"""
from __future__ import annotations

import csv
import math
import sys
from pathlib import Path

OUT = Path(__file__).resolve().parent

# --- continuum μ = m(0++)/√σ (SU(2) Wilson continuum) ---
# Primary: Lucini–Teper–Wenger, JHEP 06 (2004) 012 [hep-lat/0404008] Table 14:
#   SU(2) continuum m_{0++}/√σ = 3.78(7)
# Cross-check: Teper review hep-th/9812187: 3.74 ± 0.12
MU_PRIMARY = 3.78
MU_TEPER = 3.74
MU_TAG = "LTW04 Tab.14 SU(2) cont. 3.78(7) [hep-lat/0404008]; Teper98 3.74(12) [hep-th/9812187]"

# Hardcoded a√σ along afNomeSchedule from a10b9ea4 / af_nome_asqrt_table.csv
# (same numbers the sibling script regenerates; source tags preserved)
ASQRT_ROWS = [
    # j, beta, asqrt, short_source
    (4, 2.0164490138421893, 0.7283409486795629, "extrap FHK"),
    (5, 2.2750868684288794, 0.39171708580079007, "interp FHK"),
    (6, 2.5334853367026366, 0.17017162915456396, "interp FHK"),
    (7, 2.9005095829207477, 0.05540013456654193, "two-loop"),
    (8, 3.158562128210144, 0.02867148038448473, "two-loop"),
]


def try_import_sibling() -> list[tuple[int, float, float, str]] | None:
    """Prefer live values from sibling script if importable."""
    sib = OUT.parent / "af_nome_asqrt"
    if not sib.is_dir():
        return None
    sys.path.insert(0, str(sib))
    try:
        import af_nome_asqrt_schedule as sch  # type: ignore

        rows = []
        for j in range(4, 9):
            beta = sch.schedule_beta(j)
            asq, src, _ = sch.asqrt_at(beta)
            short = (
                "extrap FHK"
                if "extrap" in src
                else "interp FHK"
                if "interp" in src
                else "two-loop"
                if "two-loop" in src
                else src[:20]
            )
            rows.append((j, beta, asq, short))
        return rows
    except Exception as e:
        print(f"[warn] sibling import failed ({e}); using hardcoded a10b9ea4 knots")
        return None


def eps_needed(r_fine: float, r_coarse: float, kind: str) -> tuple[float, float]:
    """Return (ε_needed, signed_defect). kind in {'kfree','kappa'}."""
    if kind == "kfree":
        defect = r_fine * r_fine - r_coarse
    elif kind == "kappa":
        defect = r_fine * r_fine - r_coarse * r_coarse
    else:
        raise ValueError(kind)
    return max(0.0, defect), defect


def weighted_lean(eps_by_j: dict[int, float], j0: int, n: int) -> list[tuple[int, float]]:
    """Lean weightedErrorSum: S_m = Σ_{k=0}^{m-1} 2^k · ε(j0+k); return partials."""
    partials = []
    s = 0.0
    for m in range(1, n + 1):
        k = m - 1
        s += (2**k) * eps_by_j[j0 + k]
        partials.append((m, s))
    return partials


def weighted_project(eps_by_j: dict[int, float], js: list[int]) -> list[tuple[int, float]]:
    """Project-status: cumulative Σ 2^j ε_j over listed j (step labels)."""
    partials = []
    s = 0.0
    for j in js:
        s += (2**j) * eps_by_j[j]
        partials.append((j, s))
    return partials


def run(mu: float = MU_PRIMARY) -> dict:
    rows_src = try_import_sibling() or ASQRT_ROWS
    pts = []
    for j, beta, asq, src in rows_src:
        delta = mu * asq
        lam = math.exp(-delta)
        pts.append(dict(j=j, beta=beta, asqrt=asq, src=src, delta=delta, lam=lam))

    steps = []
    for i in range(len(pts) - 1):
        c, f = pts[i], pts[i + 1]
        j = c["j"]
        a_ratio = f["asqrt"] / c["asqrt"]
        # Shape A
        epsA_kf, defA_kf = eps_needed(f["lam"], c["lam"], "kfree")
        epsA_k, defA_k = eps_needed(f["lam"], c["lam"], "kappa")
        # Shape B: same κ-free algebra; interpret as T²↔T
        epsB, defB = eps_needed(f["lam"], c["lam"], "kfree")
        abs_mismatch = abs(f["lam"] ** 2 - c["lam"])
        steps.append(
            dict(
                j=j,
                beta=c["beta"],
                asqrt=c["asqrt"],
                delta=c["delta"],
                lam=c["lam"],
                lam_next=f["lam"],
                lam_next_sq=f["lam"] ** 2,
                a_ratio=a_ratio,
                epsA_kfree=epsA_kf,
                defA_kfree=defA_kf,
                epsA_kappa=epsA_k,
                defA_kappa=defA_k,
                epsB=epsB,
                defB=defB,
                abs_lam2_minus_lam=abs_mismatch,
                src=c["src"],
            )
        )
    # attach last point (no step) for table completeness
    last = pts[-1]
    return dict(mu=mu, pts=pts, steps=steps, last=last)


def main() -> None:
    data = run(MU_PRIMARY)
    mu = data["mu"]
    steps = data["steps"]
    pts = data["pts"]

    print("afNomeSchedule lit ε_j (0++/√σ proxy) — lit/MC only, NOT proof")
    print(f"μ = {mu}  ({MU_TAG})")
    print()
    print(
        f"{'j':>3} {'β':>8} {'a√σ':>10} {'Δ':>10} {'λ':>10}  "
        f"{'εA_kf':>10} {'εA_κ':>10} {'εB':>10} {'a_ratio':>8}"
    )
    print("-" * 100)
    for s in steps:
        print(
            f"{s['j']:3d} {s['beta']:8.3f} {s['asqrt']:10.6f} {s['delta']:10.6f} {s['lam']:10.6f}  "
            f"{s['epsA_kfree']:10.6f} {s['epsA_kappa']:10.6f} {s['epsB']:10.6f} {s['a_ratio']:8.4f}"
        )
    last = data["last"]
    print(
        f"{last['j']:3d} {last['beta']:8.3f} {last['asqrt']:10.6f} "
        f"{last['delta']:10.6f} {last['lam']:10.6f}  "
        f"{'(end)':>10} {'(end)':>10} {'(end)':>10} {'':>8}"
    )

    print()
    print("Signed defects (honesty; negative ⇒ ε_needed=0):")
    print(f"{'j':>3} {'λ_{j+1}²−λ_j':>14} {'λ_{j+1}²−λ_j²':>14} {'|λ²−λ|':>10}")
    for s in steps:
        print(
            f"{s['j']:3d} {s['defA_kfree']:14.6f} {s['defA_kappa']:14.6f} "
            f"{s['abs_lam2_minus_lam']:10.6f}"
        )

    # Weighted sums for each shape / form
    shapes = {
        "A_kfree": {s["j"]: s["epsA_kfree"] for s in steps},
        "A_kappa": {s["j"]: s["epsA_kappa"] for s in steps},
        "B": {s["j"]: s["epsB"] for s in steps},
    }
    j0, n = 4, 4
    print()
    print(f"Lean weightedErrorSum S_n = Σ_{{k=0}}^{{n-1}} 2^k · ε(j0+k), j0={j0}, n={n}:")
    lean_finals = {}
    for name, epsd in shapes.items():
        partials = weighted_lean(epsd, j0, n)
        lean_finals[name] = partials[-1][1]
        print(f"  {name}: " + ", ".join(f"S_{m}={s:.6f}" for m, s in partials)
              + f"  ⇒ S_{n}={partials[-1][1]:.6f}")

    print()
    print("Project-status Σ_j 2^j ε_j over j=4..7 (steps 4→5..7→8):")
    proj_finals = {}
    for name, epsd in shapes.items():
        partials = weighted_project(epsd, [4, 5, 6, 7])
        proj_finals[name] = partials[-1][1]
        print(f"  {name}: " + ", ".join(f"cum@j={j}:{s:.4f}" for j, s in partials)
              + f"  ⇒ Σ={partials[-1][1]:.6f}")

    # Sensitivity with Teper μ
    data_t = run(MU_TEPER)
    lean_t = {}
    for name, key in [("A_kfree", "epsA_kfree"), ("A_kappa", "epsA_kappa"), ("B", "epsB")]:
        epsd = {s["j"]: s[key] for s in data_t["steps"]}
        lean_t[name] = weighted_lean(epsd, j0, n)[-1][1]

    print()
    print(f"Sensitivity (Lean S_4) with Teper μ={MU_TEPER}: "
          + ", ".join(f"{k}={v:.6f}" for k, v in lean_t.items()))

    # CSV
    csv_path = OUT / "af_nome_eps_table.csv"
    with csv_path.open("w", newline="") as f:
        fields = [
            "j", "beta", "asqrt", "delta", "lam", "lam_next", "lam_next_sq",
            "a_ratio", "epsA_kfree", "defA_kfree", "epsA_kappa", "defA_kappa",
            "epsB", "defB", "abs_lam2_minus_lam", "src", "mu",
        ]
        w = csv.DictWriter(f, fieldnames=fields)
        w.writeheader()
        for s in steps:
            row = {k: s[k] for k in fields if k != "mu"}
            row["mu"] = mu
            w.writerow(row)
    print(f"\nWrote {csv_path}")

    # Emit a tiny summary JSON-ish for the note builder (stdout already has tables)
    summary_path = OUT / "af_nome_eps_summary.txt"
    with summary_path.open("w") as f:
        f.write(f"mu={mu}\n")
        for name, val in lean_finals.items():
            f.write(f"lean_S4_{name}={val:.10f}\n")
        for name, val in proj_finals.items():
            f.write(f"proj_sum_{name}={val:.10f}\n")
        for name, val in lean_t.items():
            f.write(f"lean_S4_teper_{name}={val:.10f}\n")
    print(f"Wrote {summary_path}")


if __name__ == "__main__":
    main()
