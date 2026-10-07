# P11 trajectory plan: step ratio along `afNomeSchedule` (MC only; not proof) — 2026-10-06

Source: `BF4WilsonAllNomeAFPaddedTrajectory.lean` (recalibrated A=1942/1000).
- `afNomeSchedule`: `1 − w_j = A / (j + κ⌊log2(j+1)⌋ + 4)`, A=1.942, κ=51/121, C=4.
- Standard coupling: `g² = −8 ln w`, `β = 4/g² = −1/(2 ln w)`.
- Lean spatial side: `side j = 2^j` (`BF4DyadicWilsonSquare.side`). Padded anchor uses `M_j = side_j`.

## Schedule (β, Lean side) table

| j | w_j | β_j | Lean side = 2^j | MC status |
|---|---|---|---|---|
| 4 | 0.780 | 2.02 | 16 | no run |
| 5 | 0.803 | 2.28 | 32 | no run |
| **6** | **0.821** | **2.53** | **64** | **β=2.5 P10 approximates β; Lean side 64 not reachable** (MC window sides 2–4 only on 16³×32) |
| 6.5 (interp.) | — | ~2.7 | — | **β=2.7 P11** (this run); no integer j |
| **7** | **0.842** | **2.90** | **128** | gap (nearest existing: P5/P6/P7 at β=2.85–2.95, flow-loop only; no multilevel Y_j) |
| 8 | 0.854 | 3.16 | 256 | gap |

## What P10 + P11 actually test

MC "side" in P8–P11 is the **window / box parameter** `M = side` in `W = R_Y(s+1)/R_Y(s/2)` and `c(k) = side·(1−R_Y(k+1)/R_Y(k))`, i.e. the Lean padded state's `M_j`, not the continuum Wilson square `2^j`. On lattices we can reach, `M ∈ {2,3,4,5,6}` (P11 will report all of these); Lean wants `M_j = 2^j ∈ {64,128,…}` at the matching β.

So the trajectory table after P11 will be:

| β | schedule j (nearest) | Lean side wanted | MC M = side reported | source |
|---|---|---|---|---|
| 2.50 | 6 (β_sched=2.53) | 64 | 2, 3, 4 | P10 multilevel Y_j |
| 2.70 | between 6 and 7 | (64–128) | 2, 3, 4, 5, 6 | P11 multilevel Y_j |

**Gaps to flag:** no multilevel Y_j at (β≈2.53, M=64) or (β≈2.90, M=128); no exact schedule-β point at 2.70. The table tests the *shape* of c(k) and W along a (β, M) path that tracks the schedule's β(j), at accessible M ≪ 2^j.

## P11 lattice choice

At β=2.7, a√σ ≈ √0.0110 ≈ 0.105 (Michael–Perantonis).
- 16³: L√σ ≈ 1.68 — **inadequate**
- **24³×32: L√σ ≈ 2.52** — smallest usable (marginal; finite-volume caveat)
- 32³: L√σ ≈ 3.36 — safer, ~2.4× cost of 24³

Chose 24³×32. Lags for M≤6: need n+2M ≤ Lt ⇒ 6+1+12=19 ≤ 32, OK.
