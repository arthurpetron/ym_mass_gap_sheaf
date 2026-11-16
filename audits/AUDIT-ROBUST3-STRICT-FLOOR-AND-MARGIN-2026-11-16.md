# Audit: Robust3StrictFloor + Robust3MarginDischarge (2026-11-16)

Each check was a direct `lean -M 6144` run, one Lean process at a time.

| File | Lines | Wall | User CPU | Peak RSS | Min MemAvailable | rc | Warnings |
|---|---|---|---|---|---|---|---|
| `lean/YMGap/RG/Robust3StrictFloor.lean` (new) | 174 | 1.0 s | 0.9 s | 1702 MiB | 13016 MiB | 0 | 0 |
| `lean/YMGap/RG/Robust3MarginDischarge.lean` (new) | 127 | 1.0 s | 0.7 s | 1694 MiB | 12791 MiB | 0 | 0 |

## Robust3StrictFloor: what is PROVED
- **`r3Floor_lt_ecomp` :117:** `(k+1)/4 < ecomp k` for every k. This is the strict floor for the exact closed form
  E = D·B. The route:
  - `L_half` :96: `L_{k+14} ≥ L_1 = 1/2`;
  - `P_ten` :101: `P_{k+14} ≤ P_1 = 10`;
  - `P_nine` :107: `P_{k+14} ≥ 9` (used only for positivity);
  - `div_lower` :65: B ≥ 11/30;
  - `D_lower` :87: D ≥ m = k+4;
  - finally (k+4)·11/30 > (k+1)/4.

  The only numerics are closed `decide` checks at n = 1.
- **`r3Raw_eq` :164:** `r3Raw k = ecomp k`, so the (k+1)/4 floor is never active.
- **`r3Floor_lt_r3E` :171:** `(k+1)/4 < r3E k`. This strengthens `r3Floor_le` (≤) to a strict inequality.
- Monotonicity of the schedule was already structural, through the running-max envelope (`r3E_mono`, Robust3 file
  :109). **Not proved:** that `ecomp` itself is monotone, i.e. that the envelope is inactive. That remains analysis
  plus numerics (task2h (E) for j ≥ 1,000,007; arb for 10 ≤ j ≤ 10⁷).

## Robust3MarginDischarge: what is PROVED (task 3)
- **`margin_nonneg_of_floor` :40:** `0 < f` and `f ≤ 2^k·M` together give `0 ≤ M`.
- **`robust3_margin_nonneg` :68:** under the instance's hypotheses, `0 ≤ latticeMargin_n` for all n. It combines
  `floor_dy_value.2` (floor = 114517/5000000 > 0) with `robust3_crossover_instance … n`.2.
- **`robust3_physical_floor_noMargin` :99:** the same conclusion as `robust3_physical_floor`, with
  **hmargin_OPEN removed**. What remains OPEN: hcross_OPEN, hafδ_OPEN, hupper_OPEN, hschur_OPEN and hspacing_OPEN.
  No existing statement was edited.

## Axioms
`#print axioms` was run in a temp file, since deleted. `r3Floor_lt_ecomp`, `r3Raw_eq`, `r3Floor_lt_r3E`,
`margin_nonneg_of_floor`, `robust3_margin_nonneg` and `robust3_physical_floor_noMargin` all depend on
[propext, Quot.sound]. There is no sorry, admit, Classical, native_decide, omega, simpa or grind. (`grind` is avoided because it pulls in Classical.choice.)

**δ_min = 0 is only a necessary condition: it removes the obstruction but does not prove hafδ.**

**Build caveat:** compiled with direct `lean -M 6144` against the box overlay (`/workspace/v3logs/overlay`). This is
direct lean against copied oleans, not lake-verified (stale-trace caveat). No chart closure is claimed.

U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence. Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β; YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). Per the numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover.
