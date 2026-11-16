# Addendum: Numerics task2k, direct heat-kernel-action MC at the Robust3 window (2026-11-16)

Docs only; no Lean changes. Sources, read directly on the box (read-only):
`/workspace/ym_tmgap_2026-11-15/results/task2k_hk.md` (§§1–9) and the same directory's `README.md` §17.
Every number below is quoted from those files.

**Status label: Monte Carlo estimates, NOT proofs.** `hspacing_OPEN` stays OPEN. δ_min = 0 is only a necessary
condition: it removes the obstruction but does not prove hafδ. No chart closure is claimed.

## What was run (task2k_hk.md §1–3)
- **Action.** The SU(2) heat-kernel action f_w(U) = Σ_n (n+1) w^{n(n+2)} χ_n(U), from `coeffW` in
  `Continuum/BondMovingStep.lean:259`.
  - It is used directly at the Lean window nomes w6…w9 = 0.779, 0.794701, 0.808737, 0.821825 (`r3Tab`).
  - No coupling map is involved.
  - The truncation n ≤ 16 has relative error ≤ 9.3e-23 at w9.
- **Method.** Metropolis with 8 hits, using the same smeared-loop pipeline and jackknife as task2i.
- **Validation.** In Wilson mode at β = 2.355, ⟨P⟩ is within +0.6σ and all 7 estimators are within 1.15σ (PASS).

## Results (task2k_hk.md §4–7; README §17)
- **a√σ, primary estimator, L = 12:**

  | w | a√σ |
  |---|---|
  | w6 | 0.5136(42) |
  | w7 | 0.3211(30) |
  | w8 | 0.2003(28); L = 16 gives 0.2010(15) |
  | w9 | unreliable (L√σ ≈ 1.2–1.7, finite volume) |

  At w8, L16 − L12 = +0.0007 ± 0.0032.
- **ℓ6 = 0.678 ± 0.018** (primary; 0.652–0.691 across estimators).
  - ℓ6 − ℓ_min,6 (0.4739) = +0.204 (11σ); +0.178…+0.217 across estimators.
- **ℓ7 = 0.676 ± 0.018** (primary, with w8 at L16; 0.676–0.770 across estimators).
  - ℓ7 − ℓ_min,7 (0.5995) = +0.077 (4.4σ); +0.077…+0.171 across estimators.
  - With w8 at L12 instead, the margin is ≥ 3.3σ.
- **ρ needed at 2σ, against the Lean `r2RhoTab` values 6 ↦ 36/25 = 1.44 and 7 ↦ 33/25 = 1.32:**
  - ρ6: 1.28 (primary); 1.27–1.30 across estimators in the 2σ column.
  - ρ7: 1.28 (primary); 1.20–1.28.
  - README §17 summarises this as "ρ6 ≤ 1.30 and ρ7 ≤ 1.28".
- **P′ path minimum slack:** +0.204 (primary), +0.209 and +0.181, still at j6.
  - Compare 0.128 ± 0.056 (task2g) and −0.042 (task2i naive Wilson map).
  - If the untrusted heat-kernel ℓ8 is included, the minimum moves to j8 at +0.117 / +0.077. It stays positive, but it is not trusted.
- **Map comparison (§6).**
  - The heat-kernel action tracks neither map.
  - β_eff = 2.184(3), 2.355(3) and 2.49–2.52 at j6, j7, j8, i.e. 72%, 63% and 44–52% of the way from naive to matched.
  - β_eff − β_naive ≈ +0.18, +0.18 and +0.14–0.16. The naive and matched Wilson models bracket the heat-kernel scale.
- **task2i j6 failure.** The task2i j6 failure (naive ℓ6 = 0.432 ± 0.028, task2i_window.md / README §15) is described as an
  artefact of the naive identification below β = 2.2.
- **Window options (§7).**
  - (a) Raise ρ6: not needed.
  - (b) Move w6: not needed.
  - (c) Matched map: "not literally supported". The supported statement is to use the measured heat-kernel a(w) for j6 and j7.
- **j8 not settled.** It needs w9 at L ≥ 20–24 (≈ 0.25–0.4 CPU-h; not run). The literature-model j8 values (naive ≥ 0.92,
  matched 0.87, against ℓ_min,8 = 0.667) remain the evidence.

## Comparison with the YM Bot summary
Agrees on: ℓ6, ℓ7, the ≥ 11σ / ≥ 4.4σ margins, P′ slack ≥ +0.18, "no window fix needed", the naive j6 = 0.432 ± 0.028
artefact, and the heat-kernel action sitting between the two maps. Minor differences:
1. **"ρ needed 1.30/1.28".** This matches README §17 ("ρ6 ≤ 1.30 and ρ7 ≤ 1.28"), which is the worst case across estimators.
   For the primary estimator, task2k_hk.md §5 gives 1.28 for both ρ6 and ρ7 at 2σ (1.25 at 1σ).
2. **"β_eff about +0.17 above naive".** The file gives per-step values +0.18, +0.18 and +0.14–0.16 (§6), not a single +0.17.
   +0.17 is a fair average, but it is not a quoted number.
3. **"j8 pending (w9 at L20)".** The file says L ≥ 20–24.
4. **"No window fix is needed".** This holds for (a) and (b). The file also says option (c), the matched map, is
   "not literally supported": the endorsed route is the measured heat-kernel a(w), not a switch of map.
5. **Housekeeping, not a numbers issue.** README has no §16, and its STATUS block (dated 12:35 PM) still says "Tasks 2b–2i are done".

## Caveats (from task2k_hk.md §8, kept verbatim in substance)
- MC is evidence, never proof.
- "σ" is the smeared-loop slope at R ≤ 5, in the crossover regime.
- Estimator systematics are ±0.02 on ℓ6 and ±0.05 on ℓ7.
- Finite volume was checked only at w8, and w9 at L12 is unreliable.
- The T3 < T2 drift at w8 (~4%) is conservative for ℓ7.
- β_eff above 2.355 uses a BSS95 junction.
- Resources: ≈ 0.83 CPU-h, slightly over the ≈ 0.7 approved because of the L16 check.

## Effect on the Lean development
None. No Lean statement mentions a coupling map. `hspacing_OPEN` is a hypothesis on an abstract `a : Nat → Q'`
(see SCOPE-HSPACING-HEAT-KERNEL-WINDOW-2026-11-16.md), and the ρ table and P₃ are unchanged. The evidence supports
keeping ρ6 = 36/25 and ρ7 = 33/25, with no j6/ρ6/w6 change, pending j8.

Build caveat for any Lean work cited here: direct lean against copied oleans, not lake-verified (stale-trace caveat).
U(1) note: the window w ≈ 0.78–0.83 lies far above w ≈ 1/8. Per the standing note, a uniform gap there would NOT hold
for U(1), so this is genuine non-abelian content (not proved).
