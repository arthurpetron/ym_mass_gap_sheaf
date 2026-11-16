# AUDIT: Robust3 width-uniform floor from `hcross_unif` (2026-11-16, base 7d23391b)

**Label: PROVED conditional reduction. NOT chart closure, NOT gap evidence.** New file only:
`lean/YMGap/RG/Robust3CrossUniform.lean` (151 lines; budget 70–110, stop at about 200). It implements `audits/SCOPE-HCROSS-UNIF-2026-11-16.md`.
The existing `hcross_OPEN` and all other statements are untouched.

## Contents (file:line)
| name | line | role |
|---|---|---|
| `VC`, `PhiFam` | 45/49 | carrier at width `W j`; width-indexed maps `Φ_{W,n}` |
| `fineAt`, `coarseAt` | 52/57 | fine two-step factor / coarse attainment at width W, step n |
| `hupper_unif` | 67 | OPEN: `‖Φ_{W,n}y‖_C ≤ ‖y‖_F` for every W |
| `hcross_unif` | 76 | OPEN: for n < 6, a W-independent budget `SchurBudget (f n) (c n) (1/64)`, plus `fineAt W n (f n) ∧ coarseAt W n (Φ W n) (c n)` for **every** W |
| `hafδ_unif` | 81 | OPEN: the same for n ≥ 6, with budget `afGap²/10` |
| `step_data` | 86 | PROVED: per-step data at the cap `capDelta n` |
| `hschur_unif_of_spectral` | 98 | PROVED: width-uniform `SchurDecomposition` with `D_{W,n} := schurSlack`, δ = capDelta |
| `robust3_floor_width_uniform_schur` | 108 | PROVED reduction, Schur form: Φ and D indexed by W; δ and the caps W-independent |
| `robust3_floor_width_uniform` | 134 | PROVED reduction (the `lmax` wiring) |

**Main theorem.** `robust3_floor_width_uniform` holds ∀ W n, and its conclusion has two conjuncts:
- (a) `WilsonVacuumSqContraction` at nome w_n and width `W n`, with the **W-independent** rate `relativeRate timeRate capDelta n`;
- (b) `floor·aHK(w_n) ≤ (P₃·aHK(w_0))·latticeMargin(relativeRate timeRate capDelta)_n`.

Its open hypotheses are `hupper_unif`, `hcross_unif`, `hafδ_unif`, `hpos`, `hwin_MC` and `hoff_OPEN`.

**Honesty note.** Conjunct (b) never mentions W; it is the same inequality as in the existing theorems. When I first wrote
the conclusion as (b) alone, Lean flagged `W` as an unused variable. I therefore added (a), the width-W carrier contraction
from `robust3_crossover_instance` (`Robust3UndershootCrossoverInstance.lean:97`). (a) is what makes the theorem width-uniform:
the same rate holds at every width.

**U(1).** The module docstring and the theorem docstring record that finite-volume `hcross` (one width, task2n ≤ 12 sites) does not
give `hcross_unif`. U(1) is expected to fail `hcross_unif` at step 2 (task2n estimate, not run). No formal non-implication is proved.

**Non-vacuity.** None for the carrier hypotheses: `hupper_unif`, `hcross_unif` and `hafδ_unif` have no witness.

## Checks
- Total RAM 16002 MiB. No Numerics processes before any run (no waits). Direct `lean -M 6144`, one process at a time.
  - Build 1: rc 0, with **2 warnings** (unused `W`, fixed as described above).
  - Build 2 (final): rc 0, zero warnings. Wall 1.0 s, CPU 0.7 s user + 0.3 s sys, peak RSS 1666 MiB.
    Available RAM 9050 MiB (56%) before, minimum 8851 MiB (55%).
  - Axiom temp file (deleted): wall 2.0 s, CPU 1.7 s, peak RSS 1640 MiB, minimum available 56%.
- `#print axioms`: `step_data`, `hschur_unif_of_spectral`, `robust3_floor_width_uniform_schur` and `robust3_floor_width_uniform`
  all depend on `[propext, Quot.sound]`.
- grep: no sorry/admit/Classical/native_decide/omega/simpa/grind.

## Standard caveats
- Build: direct lean against copied oleans, not lake-verified (stale-trace caveat).
- δ_min: per task2n, it is exact under the KS carrier (analytic, handwritten, conditional). Lean has only the sufficiency core.
- U(1): see above.
- Not chart closure.
