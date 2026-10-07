#!/usr/bin/env python3
"""
Dyadic β-schedule (a(β_{j+1})/a(β_j) = 1/2 exactly) + ε_j recompute.

Lit/MC only — NOT a proof of anything.

Single source of truth for a√σ(β): imported from sibling
  ../af_nome_asqrt/af_nome_asqrt_schedule.py   (commit a10b9ea4)
  - FHK/UKQCD knots, ln-linear interp in [2.20, 2.85]   → "interp"
  - lit-slope extrapolation below 2.20                  → "extrap"
  - two-loop SU(2) Wilson from β=2.85 anchor above 2.85 → "two-loop"
μ and the ε formulas are imported from ../af_nome_eps/af_nome_eps_intertwiner.py
(commit 398bac67) so the afNome side-by-side uses identical code.

Dyadic schedule: β^dy_{j+1} solves a√σ(β) = a√σ(β^dy_j)/2 (bisection, monotone).
Anchor is a CONVENTION: primary β^dy_4 = β^AF_4; sensitivity β^dy_6 = β^AF_6.
Nome: w = exp(-1/(2β))  (β = 4/g², g² = -8 ln w).
CPU-light; no Monte Carlo. P11 untouched.
"""
from __future__ import annotations

import csv
import math
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "af_nome_asqrt"))
sys.path.insert(0, str(HERE.parent / "af_nome_eps"))

import af_nome_asqrt_schedule as sch  # noqa: E402  (a10b9ea4: asqrt_at, schedule_beta, B0, B1)
import af_nome_eps_intertwiner as epsmod  # noqa: E402  (398bac67: MU_PRIMARY, eps_needed, weighted_*)

MU = epsmod.MU_PRIMARY  # 3.78(7) LTW04
J_MIN, J_MAX = 4, 12
LIT_LO, LIT_HI = 2.20, 2.85


def asqrt(beta: float) -> float:
    return sch.asqrt_at(beta)[0]


def region_tag(beta: float) -> str:
    if beta < LIT_LO:
        return "extrap"
    if beta > LIT_HI:
        return "two-loop"
    return "interp"


def nome(beta: float) -> float:
    return math.exp(-1.0 / (2.0 * beta))


def solve_beta_for(target: float, lo: float = 1.5, hi: float = 8.0) -> float:
    """Bisection for asqrt(β) = target (asqrt strictly decreasing)."""
    flo, fhi = asqrt(lo) - target, asqrt(hi) - target
    assert flo > 0 > fhi, (lo, hi, target)
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        fm = asqrt(mid) - target
        if fm > 0:
            lo = mid
        else:
            hi = mid
        if hi - lo < 1e-15:
            break
    return 0.5 * (lo + hi)


def dyadic_schedule(j_anchor: int, beta_anchor: float) -> dict[int, float]:
    betas = {j_anchor: beta_anchor}
    for j in range(j_anchor, J_MAX):  # upward: halve a
        betas[j + 1] = solve_beta_for(asqrt(betas[j]) / 2.0)
    for j in range(j_anchor, J_MIN, -1):  # downward: double a
        betas[j - 1] = solve_beta_for(asqrt(betas[j]) * 2.0)
    return dict(sorted(betas.items()))


def two_loop_dbeta_halving(beta: float) -> float:
    """Exact two-loop Δβ with aΛ(β+Δβ)/aΛ(β) = 1/2 (solve)."""
    target = sch.two_loop_aLambda(beta) / 2.0
    lo, hi = beta, beta + 2.0
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if sch.two_loop_aLambda(mid) > target:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def schedule_rows(betas: dict[int, float]) -> list[dict]:
    rows = []
    js = sorted(betas)
    for j in js:
        b = betas[j]
        b_af = sch.schedule_beta(j)
        w, w_af = nome(b), sch.schedule_w(j)
        a = asqrt(b)
        rows.append(
            dict(
                j=j, beta_dy=b, asqrt=a, src=region_tag(b),
                w_dy=w, one_minus_w_dy=1 - w,
                beta_af=b_af, w_af=w_af,
                dbeta=b - b_af, dw=w - w_af,
                ratio_1mw=(1 - w) / (1 - w_af),
                step_dbeta=(betas[j + 1] - b) if j + 1 in betas else float("nan"),
                step_dbeta_af=(sch.schedule_beta(j + 1) - b_af),
                a_ratio_next=(asqrt(betas[j + 1]) / a) if j + 1 in betas else float("nan"),
            )
        )
    return rows


def eps_rows(asq: dict[int, float]) -> list[dict]:
    """ε table from a dict j -> a√σ_j using the 398bac67 formulas."""
    out = []
    js = sorted(asq)
    for j in js[:-1]:
        lam_c = math.exp(-MU * asq[j])
        lam_f = math.exp(-MU * asq[j + 1])
        epsA_kf, defA_kf = epsmod.eps_needed(lam_f, lam_c, "kfree")
        epsA_k, defA_k = epsmod.eps_needed(lam_f, lam_c, "kappa")
        epsB, defB = epsmod.eps_needed(lam_f, lam_c, "kfree")
        # Shape A κ-form at ε=0: κ λ_c² = λ_f²  ⇒ κ = λ_f²/λ_c² (= 1/λ_c on exact dyadic)
        kappa0 = (lam_f * lam_f) / (lam_c * lam_c)
        out.append(
            dict(
                j=j, Delta=MU * asq[j], lam=lam_c, lam_next=lam_f,
                epsA_kfree=epsA_kf, defA_kfree=defA_kf,
                epsA_kappa=epsA_k, defA_kappa=defA_k,
                epsB=epsB, defB=defB,
                resid_A_kappa=lam_c - lam_c * lam_c,  # λ_j − λ_j² (dyadic identity)
                kappa0=kappa0, kappa0_minus1=kappa0 - 1.0,
                inv_lam_minus1=1.0 / lam_c - 1.0,
            )
        )
    return out


def lean_sum(vals: dict[int, float], j0: int, n: int) -> list[float]:
    s, out = 0.0, []
    for k in range(n):
        s += (2**k) * vals[j0 + k]
        out.append(s)
    return out


def proj_sum(vals: dict[int, float], js: list[int]) -> list[float]:
    s, out = 0.0, []
    for j in js:
        s += (2**j) * vals[j]
        out.append(s)
    return out


def fmt(x: float, p: int = 6) -> str:
    return "nan" if x != x else f"{x:.{p}f}"


def main() -> None:
    print("Dyadic β-schedule + ε recompute — lit/MC only, NOT proof")
    print(f"μ = {MU} (LTW04 hep-lat/0404008); a√σ(β) from a10b9ea4 module\n")

    # Two-loop asymptotics
    b0, b1 = sch.B0, sch.B1
    dbeta_inf = 8.0 * b0 * math.log(2.0)
    print(f"two-loop: b0={b0:.8f}, b1={b1:.8f}")
    print(f"asymptotic halving step Δβ_∞ = 8 b0 ln2 = 11 ln2/(3π²) = {dbeta_inf:.6f}")
    print(f"afNome smooth step ≈ 1/(2A) = {1/(2*sch.A):.6f}; A* = 3π²/(22 ln2) = "
          f"{3*math.pi**2/(22*math.log(2)):.6f} (vs A={sch.A})")
    for b in (2.85, 3.0, 3.5, 4.0, 5.0, 10.0, 100.0):
        d = two_loop_dbeta_halving(b) - b
        approx = dbeta_inf + (4.0 * b1 / b0) * math.log(1.0 + d / b)
        print(f"  exact two-loop halving Δβ at β={b:>6}: {d:.6f}  "
              f"(fixed-point 8b0 ln2 + (4b1/b0) ln(1+Δβ/β) = {approx:.6f})")
    print()

    all_out = {}
    for label, ja in (("anchor_j4", 4), ("anchor_j6", 6)):
        betas = dyadic_schedule(ja, sch.schedule_beta(ja))
        srows = schedule_rows(betas)
        asq = {r["j"]: r["asqrt"] for r in srows}
        erows = eps_rows(asq)
        all_out[label] = (srows, erows)

        print(f"=== {label}: β^dy_{ja} = β^AF_{ja} = {sch.schedule_beta(ja):.6f} (convention) ===")
        print(f"{'j':>3} {'β_dy':>9} {'a√σ':>10} {'src':>9} {'w_dy':>9} {'1-w_dy':>9} "
              f"{'β_AF':>9} {'Δβ':>9} {'Δw':>9} {'(1-w)r':>7} {'stepβdy':>8} {'stepβAF':>8} {'a_rat':>7}")
        for r in srows:
            print(f"{r['j']:3d} {r['beta_dy']:9.6f} {r['asqrt']:10.6f} {r['src']:>9} "
                  f"{r['w_dy']:9.6f} {r['one_minus_w_dy']:9.6f} {r['beta_af']:9.6f} "
                  f"{r['dbeta']:+9.5f} {r['dw']:+9.6f} {r['ratio_1mw']:7.4f} "
                  f"{fmt(r['step_dbeta'],5):>8} {r['step_dbeta_af']:8.5f} {fmt(r['a_ratio_next'],12):>7}")
        print()
        print(f"{'j':>3} {'Δ':>9} {'λ':>9} {'defB=λ²₊−λ':>12} {'εB':>6} {'εA_kf':>6} "
              f"{'εA_κ':>9} {'λ−λ²':>9} {'κ0':>9} {'κ0−1':>9}")
        for e in erows:
            print(f"{e['j']:3d} {e['Delta']:9.6f} {e['lam']:9.6f} {e['defB']:12.2e} "
                  f"{e['epsB']:6.0e} {e['epsA_kfree']:6.0e} {e['epsA_kappa']:9.6f} "
                  f"{e['resid_A_kappa']:9.6f} {e['kappa0']:9.4f} {e['kappa0_minus1']:9.4f}")
        maxdef = max(abs(e["defB"]) for e in erows)
        maxk = max(abs(e["kappa0"] - 1 / e["lam"]) / (1 / e["lam"]) for e in erows)
        print(f"max |λ_{{j+1}}² − λ_j| = {maxdef:.2e};  max rel|κ0 − 1/λ_j| = {maxk:.2e}")

        epsAk = {e["j"]: e["epsA_kappa"] for e in erows}
        km1 = {e["j"]: e["kappa0_minus1"] for e in erows}
        n = J_MAX - J_MIN
        print("Lean S_n (j0=4), ε^A_κ   : " + ", ".join(fmt(x, 4) for x in lean_sum(epsAk, 4, n)))
        print("Lean S_n (j0=4), κ_j−1   : " + ", ".join(fmt(x, 3) for x in lean_sum(km1, 4, n)))
        print("2^k·(κ_j−1) terms        : " + ", ".join(fmt((2**k) * km1[4 + k], 3) for k in range(n)))
        print("2^k·ε^A_κ terms          : " + ", ".join(fmt((2**k) * epsAk[4 + k], 3) for k in range(n)))
        print(f"proj Σ_{{j=4..7}} 2^j ε^A_κ = {proj_sum(epsAk, [4,5,6,7])[-1]:.4f};  "
              f"Σ_{{j=4..{J_MAX-1}}} = {proj_sum(epsAk, list(range(4, J_MAX)))[-1]:.4f}")
        print(f"proj Σ_{{j=4..7}} 2^j (κ_j−1) = {proj_sum(km1, [4,5,6,7])[-1]:.3f};  "
              f"Σ_{{j=4..{J_MAX-1}}} = {proj_sum(km1, list(range(4, J_MAX)))[-1]:.3f}")
        print()

    # Side-by-side with afNome (398bac67) for j=4..7, primary anchor
    af = epsmod.run(MU)["steps"]
    _, er = all_out["anchor_j4"]
    erd = {e["j"]: e for e in er}
    print("=== side-by-side ε (j→j+1): afNome (398bac67) vs dyadic anchor j4 ===")
    print(f"{'j':>3} {'εA_kf AF':>9} {'εA_kf dy':>9} {'εB AF':>9} {'εB dy':>9} "
          f"{'εA_κ AF':>9} {'εA_κ dy':>9} {'mismatch share of εA_κ':>22}")
    side = []
    for s in af:
        j = s["j"]
        d = erd[j]
        share = (s["epsA_kappa"] - d["epsA_kappa"]) / s["epsA_kappa"] if s["epsA_kappa"] else float("nan")
        side.append(dict(j=j, epsA_kfree_af=s["epsA_kfree"], epsA_kfree_dy=d["epsA_kfree"],
                         epsB_af=s["epsB"], epsB_dy=d["epsB"],
                         epsA_kappa_af=s["epsA_kappa"], epsA_kappa_dy=d["epsA_kappa"],
                         schedule_share_epsA_kappa=share))
        print(f"{j:3d} {s['epsA_kfree']:9.5f} {d['epsA_kfree']:9.1e} {s['epsB']:9.5f} {d['epsB']:9.1e} "
              f"{s['epsA_kappa']:9.5f} {d['epsA_kappa']:9.5f} {share:22.3f}")
    sum_af = {k: lean_sum({s['j']: s[k] for s in af}, 4, 4)[-1] for k in ("epsA_kfree", "epsB", "epsA_kappa")}
    sum_dy = {k: lean_sum({e['j']: e[k] for e in er}, 4, 4)[-1] for k in ("epsA_kfree", "epsB", "epsA_kappa")}
    print("Lean S_4 afNome : " + ", ".join(f"{k}={v:.4f}" for k, v in sum_af.items()))
    print("Lean S_4 dyadic : " + ", ".join(f"{k}={v:.4g}" for k, v in sum_dy.items()))

    # CSVs
    for label, (srows, erows) in all_out.items():
        with (HERE / f"dyadic_schedule_{label}.csv").open("w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(srows[0].keys()))
            w.writeheader(); w.writerows(srows)
        with (HERE / f"dyadic_eps_{label}.csv").open("w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(erows[0].keys()))
            w.writeheader(); w.writerows(erows)
    with (HERE / "eps_side_by_side_afnome_vs_dyadic.csv").open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(side[0].keys()))
        w.writeheader(); w.writerows(side)
    print(f"\nWrote CSVs under {HERE}")


if __name__ == "__main__":
    main()
