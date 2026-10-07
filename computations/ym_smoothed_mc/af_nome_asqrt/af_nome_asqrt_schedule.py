#!/usr/bin/env python3
"""
afNomeSchedule a√σ literature check (j=4..8).

MC/literature only — NOT a proof of RG summability or AF.

Schedule (BF4WilsonAllNomeAFPaddedTrajectory.lean / P11_TRAJECTORY_PLAN.md):
  1 - w_j = A / (j + κ ⌊log₂(j+1)⌋ + C)
  A = 1.942, κ = 51/121, C = 4
  β_j = -1/(2 ln w_j)   [= 4/g² with g² = -8 ln w]

Literature SU(2) Wilson a√σ points are hardcoded below with citations.
Where schedule β_j does not land on a published point:
  - inside lit window: linear interpolation of ln(a√σ) vs β  [MARKED interp]
  - just below lowest lit β: lit-slope extrapolation of ln(a√σ),
    cross-checked with two-loop  [MARKED extrap]
  - above highest lit β: two-loop asymptotic ratio from nearest anchor
    (Λ cancels in ratios)  [MARKED two-loop]
Do NOT invent unpublished table entries.

Two-loop (SU(2) Wilson, g²=4/β):
  b0 = 11/(24 π²), b1 = 17/(96 π⁴)
  aΛ(β) ∝ (b0 g²)^{-b1/(2 b0²)} exp(-1/(2 b0 g²))

CPU-light; no Monte Carlo. Leave P11 multilevel job untouched.
"""
from __future__ import annotations

import csv
import math
from pathlib import Path

A = 1.942
KAPPA = 51.0 / 121.0
C = 4.0

PI = math.pi
B0 = 11.0 / (24.0 * PI * PI)
B1 = 17.0 / (96.0 * PI**4)

# Primary literature knots (a√σ), Fingberg–Heller–Karsch compilation Table 3
# hep-lat/9208012, Nucl.Phys.B392 (1993) 493 — SU(2) Wilson, large lattices.
# β=2.85 also UKQCD/Booth et al. hep-lat/9209007 (√K a=0.063(3)).
LIT_POINTS: list[tuple[float, float, str]] = [
    (2.20, 0.4690, "FHK92 T3 hep-lat/9208012"),
    (2.30, 0.3690, "FHK92 T3 hep-lat/9208012"),
    (2.40, 0.2660, "FHK92 T3 hep-lat/9208012"),
    (2.50, 0.1905, "FHK92 T3 hep-lat/9208012"),
    (2.60, 0.1360, "FHK92 T3 hep-lat/9208012"),
    (2.70, 0.1015, "FHK92 T3 hep-lat/9208012"),
    (2.85, 0.0630, "FHK92 T3 / UKQCD hep-lat/9209007"),
]
# Cross-checks (documented, not primary knots):
# Michael–Perantonis J.Phys.G18 (1992) 1725: Ka²=0.0110(4)@β=2.7 → a√σ≈0.1049
# Bali et al. PRL71 (1993) 3059 hep-lat/9306024: 0.1836(13)@2.5115; 0.0911(8)@2.74
# Bali–Schilling–Schlichter PRD51 (1995) 5165 hep-lat/9409005:
#   Ka²≈0.0350/0.01458/0.00830 at 2.50/2.635/2.74


def floor_log2(n: int) -> int:
    if n <= 0:
        raise ValueError(n)
    return n.bit_length() - 1


def schedule_w(j: int) -> float:
    return 1.0 - A / (j + KAPPA * floor_log2(j + 1) + C)


def schedule_beta(j: int) -> float:
    return -1.0 / (2.0 * math.log(schedule_w(j)))


def two_loop_aLambda(beta: float) -> float:
    g2 = 4.0 / beta
    return (B0 * g2) ** (-B1 / (2.0 * B0 * B0)) * math.exp(-1.0 / (2.0 * B0 * g2))


def lit_sorted():
    return sorted(LIT_POINTS, key=lambda t: t[0])


def asqrt_at(beta: float) -> tuple[float, str, float | None]:
    """Return (a√σ, source_tag, optional_alt_two_loop_value)."""
    pts = lit_sorted()
    betas = [p[0] for p in pts]
    if beta < betas[0]:
        # Prefer short lit-slope extrapolation of ln(a√σ); also quote two-loop.
        b0, a0, c0 = pts[0]
        b1, a1, _ = pts[1]
        slope = (math.log(a1) - math.log(a0)) / (b1 - b0)
        asq_ex = math.exp(math.log(a0) + slope * (beta - b0))
        asq_2l = a0 * two_loop_aLambda(beta) / two_loop_aLambda(b0)
        tag = (
            f"extrap ln(a√σ) slope from β={b0}/{b1} ({c0}); "
            f"two-loop cross-check={asq_2l:.4f}"
        )
        return asq_ex, tag, asq_2l
    if beta > betas[-1]:
        b_a, asq_a, cite_a = pts[-1]
        asq = asq_a * two_loop_aLambda(beta) / two_loop_aLambda(b_a)
        # Secondary: lit slope from last two points (aggressive; AS violations)
        b0, a0, _ = pts[-2]
        b1, a1, _ = pts[-1]
        slope = (math.log(a1) - math.log(a0)) / (b1 - b0)
        asq_slope = math.exp(math.log(a1) + slope * (beta - b1))
        tag = (
            f"two-loop from {cite_a} @β={b_a}; "
            f"lit-slope alt={asq_slope:.4f} (AS-violating, illustrative)"
        )
        return asq, tag, asq_slope
    for b, a, cite in pts:
        if abs(b - beta) < 1e-9:
            return a, f"lit {cite}", None
    lo = max(i for i, b in enumerate(betas) if b <= beta)
    hi = lo + 1
    b0, a0, c0 = pts[lo]
    b1, a1, c1 = pts[hi]
    t = (beta - b0) / (b1 - b0)
    asq = math.exp((1.0 - t) * math.log(a0) + t * math.log(a1))
    tag = f"interp ln(a√σ) in β between {b0} and {b1} (FHK92)"
    return asq, tag, None


def main() -> None:
    out_dir = Path(__file__).resolve().parent
    js = list(range(4, 9))
    rows = []
    print("afNomeSchedule + a√σ (MC/lit only, not proof)")
    print(f"A={A}, κ={KAPPA:.10f}, C={C}")
    print(f"{'j':>3} {'w_j':>10} {'β_j':>10} {'a√σ':>10}  source")
    print("-" * 100)
    for j in js:
        w, beta = schedule_w(j), schedule_beta(j)
        asq, src, alt = asqrt_at(beta)
        rows.append(dict(j=j, w=w, beta=beta, asqrt=asq, source=src, alt=alt))
        alt_s = f"  [alt={alt:.4f}]" if alt is not None else ""
        print(f"{j:3d} {w:10.6f} {beta:10.6f} {asq:10.6f}  {src}{alt_s}")

    print()
    print(f"{'j':>3} {'r_lit':>10} {'r_2loop':>10} {'|log2 r+1|':>12}")
    print("-" * 40)
    deviations, ratio_rows = [], []
    for i in range(len(rows) - 1):
        r = rows[i + 1]["asqrt"] / rows[i]["asqrt"]
        r2 = two_loop_aLambda(rows[i + 1]["beta"]) / two_loop_aLambda(rows[i]["beta"])
        dev = abs(math.log(r, 2) + 1.0)
        deviations.append(dev)
        ratio_rows.append(
            dict(
                j=rows[i]["j"],
                ratio=r,
                ratio_2loop=r2,
                abs_log2_plus1=dev,
                target_half=0.5,
            )
        )
        print(f"{rows[i]['j']:3d} {r:10.6f} {r2:10.6f} {dev:12.6f}")

    s = 0.0
    print()
    for k, d in enumerate(deviations):
        s += d
        print(f"partial S after steps j={4+k}→{5+k}: {s:.6f}")
    print(f"S = Σ_{{j=4..7}} |log2(r_j)+1| = {s:.6f}")

    print()
    print("Two-loop-only |log2(r)+1| tail (schedule β, j=8..30):")
    tail = 0.0
    for j in range(8, 31):
        b0, b1 = schedule_beta(j), schedule_beta(j + 1)
        r = two_loop_aLambda(b1) / two_loop_aLambda(b0)
        d = abs(math.log(r, 2) + 1.0)
        tail += d
        if j in (8, 9, 10, 12, 15, 20, 30):
            print(f"  j={j}: r={r:.6f} |log2 r+1|={d:.6f} cum={tail:.6f}")
    print(f"two-loop tail sum j=8..30 ≈ {tail:.6f}")

    with (out_dir / "af_nome_asqrt_table.csv").open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=["j", "w", "beta", "asqrt", "source"])
        w.writeheader()
        for r in rows:
            w.writerow({k: r[k] for k in ("j", "w", "beta", "asqrt", "source")})
    with (out_dir / "af_nome_ratios.csv").open("w", newline="") as f:
        w = csv.DictWriter(
            f, fieldnames=["j", "ratio", "ratio_2loop", "abs_log2_plus1", "target_half"]
        )
        w.writeheader()
        w.writerows(ratio_rows)
    print(f"\nWrote CSVs under {out_dir}")


if __name__ == "__main__":
    main()
