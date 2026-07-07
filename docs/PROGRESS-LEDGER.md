# Forward-Progress Ledger — YM mass-gap solve

**Purpose.** Measure genuine forward progress toward the *solve* and detect
mathematical-theory **loops** (re-deriving the same irreducible obligation from a
new angle). Run `bash computations/progress_metric.sh` each iteration.

## The metric (three counters + a status ladder)

| Symbol | Meaning | Moves how |
|---|---|---|
| **D** | Critical-path obligations **DISCHARGED** (a load-bearing type newly inhabited axiom-clean **and the frontier guard drops below 5**). | **TRUE NORTH.** Solve done when the goal obligation is discharged. |
| **F** | Distinct **OPEN** obligations *not provably equivalent* to the current core. | Shrinks on discharge; may split (a real reduction) into strictly-weaker pieces. |
| **C** | **Confirmation aliases** `X := SingleStepDefectBound`. | A **LOOP counter.** C++ with no change to F or D = a loop. |

**singleStep status ladder** (the whole continuum gap is proved conditional on it):
0 conjectured → 1 numerically verified TRUE → 2 decomposed into strictly-weaker
sub-obligations → 3 sub-obligations discharged → 4 fully proved (guard breaks).

## Baseline (commit 05ae807, 2026-07-07)

- **D = 0** — nothing on the critical path is discharged; guard = 5 (intact).
- **F = 3** — `{ uniform_in_m_variance_monotonicity, channel_feedback, real_defect_identification }`.
- **C = 14** — fourteen modules reduced to `singleStep`.
- **singleStep at status 2** (verified true, safety factor 45; decomposed — but two of
  the three pieces are UNVERIFIED as strictly-weaker).

## What this reveals (honest)

The `C=14` is the loop, quantified. Roughly the last ~20 agent-rounds each applied a
new tool (curvature, OS/confinement, RG, OPE, reflection positivity, Simon–Lieb,
Schwinger–Dyson, Wetterich, instanton, MK, Birkhoff, …), and each ended by emitting a
`… := SingleStepDefectBound` alias — i.e. **re-deriving the same obligation**. Those
rounds produced genuine *side* theorems and a genuine *obstruction map* (real value),
but they did **not** move D and did **not** shrink the hard core.

**Genuine forward moves that DID happen** (these are the template for what counts):
1. The whole continuum gap became conditional on `singleStep` *alone* (F: many → 1).
2. `singleStep` moved 0 → 1 (numerically **verified true**, safety factor 45, via the
   `m`-fold concentration — refuting the old "linear-in-`m`" wall).
3. `singleStep` moved 1 → 2 (**decomposed**), and one piece (uniform-in-`m`) reduced to
   a single-functional statement `Var_m(cosθ) ≤ Var_2` that is genuinely strictly weaker.

## Critical-path DAG (proved reductions ⇒, open leaves in **bold**)

```
mass_gap  ⇐  rgFlow_gap_conditional ∧ MultiScalePolymerExpansion  (PROVED assembly)
          ⇐  additiveErosion_uniform_floor  (PROVED: floor given summable defect + anchor-dominance)
          ⇐  singleStep : realδ_k ≤ 6(1−w_k)²   (status-2 core)
                 ├─ **uniform_in_m_variance_monotonicity**  (Var_m(cosθ) ≤ Var_2 ; STRICTLY WEAKER — attackable)
                 ├─ **channel_feedback**       (s≥2 → next-scale s=1 ; NOT YET shown strictly weaker)
                 └─ **real_defect_identification** (real 4D block-spin defect = fusion object ; NOT YET shown strictly weaker)
```

## Anti-loop rule (enforced before spawning any attack)

Predict the attack's honest outcome. **If it is "produces another
`:= SingleStepDefectBound` alias" / "reduces to `singleStep`," it is a LOOP — do not
spawn it.** "The honest expectation is another confirmation" *is* the loop signal.

Only spawn an attack that would:
- **(a)** DISCHARGE a bold frontier obligation (inhabit it axiom-clean → D++, guard reacts), or
- **(b)** DECOMPOSE a frontier obligation into strictly-weaker *independent* pieces with a
  PROVED `(⋀ pieces) → parent` **and** a certificate that ≥1 piece is strictly weaker
  (single-scale/finite vs all-scale/uniform/continuum), or
- **(c)** REFUTE a genuinely-live candidate route (kills a branch, not a re-confirmation).

## Re-oriented plan (only F-moving work)

1. **Discharge uniform-in-`m`** (variance monotonicity `Var_m ≤ Var_2`). In flight. If
   proved: D-partial, F: 3 → 2 for that branch.
2. **Adjudicate the other two pieces.** Before attacking them, PROVE whether
   `channel_feedback` and `real_defect_identification` are (i) strictly weaker than
   `singleStep` (legit F-nodes) or (ii) logically **equal** to `singleStep` (in which case
   the "decomposition" is fake — record it, and the only honest attack left is on
   `singleStep` head-on or a declaration that it is the irreducible Clay core).
3. **No more new-tool sweeps** whose predicted outcome is a confirmation alias.
