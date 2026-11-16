# AUDIT: Robust3 Schur budget from spectral data (task2n (A), abstract form), 2026-11-16

**Label: PROVED conditional reduction. NOT chart closure, NOT gap evidence.** Base bb181cbf. New file only:
`lean/YMGap/RG/Robust3SchurRankOne.lean` (263 lines; budget ≈ 400). Nothing existing was edited.

## What task2n claims (quoted, `results/task2n_hafdelta.md` §1)
- "the least δ ∈ [0,1] for which some pair (Φ, D) satisfies hupper and hschur is exactly δ*_n = max(0, 1 − (1 − ρ_F⁴)/(1 − ρ_C²))"
  under "the meta-identification T = KS transfer matrix".
- Attained: "Take Φ(y) := ‖y‖·v_C … (R) reduces to ‖T_F²y‖² ≤ (δ + (1−δ)ρ_C²)‖y‖²".
- Caveat: "this needs a scalar action of the constructive real ‖y‖ … otherwise use a rational approximation at O(ε) cost."
- Nature: the characterization is a short **handwritten analytic argument** (lower bound + rank-one attainment),
  conditional on the TM identification and spectral facts (i)–(iii). The ℓ_j values and the δ* = 0 table are
  **numerical** (HK MC j6–7, 15 models j6–10, arb tail 10 ≤ j ≤ 10⁷ for models).

## What is proved in Lean (file:line)
| name | line | statement |
|---|---|---|
| `SchurBudget f c δ` | 53 | `f ≤ δ + (1−δ)c` (rational form of δ ≥ δ_min, f ≈ ρ_F⁴, c ≈ ρ_C²) |
| `budget_eps` | 57 | `f + (1−δ)ε ≤ δ + (1−δ)c₀ → SchurBudget f (c₀−ε) δ` (the ε cost is exactly (1−δ)ε ≤ ε) |
| `rel_of_budget` | 88 | RC core: `F ≤ fA`, `cA ≤ C`, `A ≥ 0`, budget ⇒ `F ≤ δA + (1−δ)C` |
| `slack_dec` | 116 | relative comparison ⇒ `D := (A−F) − (1−δ)(A−C) ≥ 0` and the exact Schur identity |
| `schurSlack` | 129 | carrier slack |
| `schur_of_spectral` | 138 | `WilsonVacuumSqTwoStepFactor … f` + coarse attainment `c‖y‖² ≤ ‖T_C(1)Φy‖²` + budget ⇒ repo `SchurDecomposition … δ Φ (schurSlack …)` |
| `schur_of_spectral_rate` | 152 | same, fine input as one-step `WilsonVacuumSqContraction … rF` (f = rF⁴, via `vacuumSq_implies_twoStepFactor`) |
| `robust3_physical_floor_spectral_HK` | 171 | the final theorem with `D`, `hschur_OPEN` replaced by `hfine_OPEN`, `hcoarse_OPEN`, `hbudget_OPEN` |
| `capDelta`, `_nonneg`, `_le_one` | 207/210/218 | δ := 1/64 (n<6), afGap²/10 (n≥6) |
| `robust3_physical_floor_lmax_HK` | 233 | δ, hd0, hd1, hcross, hafδ, D, hschur all discharged; remaining: hupper, hfine, hcoarse, `hbudget_OPEN n : SchurBudget (f n) (c n) (capDelta n)` (= ℓ_n ≤ ℓ_max(n), rational form), plus the HK spacing/positivity binders |

Repo interfaces used: `SchurDecomposition` (`RelativeDissipationScaleChain.lean:77`), `relative_comparison_iff_dissipation`
(`BF4WilsonAllNomeRGRelativeDissipation.lean:102`), `WilsonVacuumSqTwoStepFactor` (`BF4WilsonAllNomeRGStepComposition.lean:278`),
`vacuumSq_implies_twoStepFactor` (`:293`), `robust3_physical_floor_noMargin_HK` (`Robust3SpacingHeatKernel.lean:75`), whose
hafδ binder is at `:80`. `DyadicRGStep` (`DyadicCrossoverSchedule.lean:47`) is not used: its (SC) `w_f² ≤ w_c` is only the
strong-coupling-model analogue (m ≈ 3t) of ℓ ≤ 1 and has no link to the carrier.

## What is NOT proved (stays OPEN / meta)
- **Existence of the rank-one Φ on the completed carrier.** `VacuumComplement` has no scalar action by a constructive real
  `‖y‖ = √completedInner(y,y)`, so `Φ(y) = ‖y‖v_C` cannot be defined in the repo. It enters only through `hcoarse_OPEN`
  (with `hupper_OPEN`). Handling: `c` is a rational parameter; a rational approximation of ‖y‖ or v_C gives `c = c₀ − ε`, and
  `budget_eps` shows that the budget then costs `(1−δ)ε`.
- The necessity direction (δ ≥ δ_min for every Φ) is not formalised. It is not needed for the reduction.
- The spectral facts f ≥ ρ_F⁴-type contraction and c ≈ ρ_C², the TM identification, and δ_min = 0 ⇔ ℓ ≤ 1 (needs exp/log) are not formalised.
- Non-vacuity: there is no joint witness for hupper + hfine + hcoarse + hbudget. The proved seed rate `mixRate` would give a
  valid `hfine`, but it is close to 1, so the budget would fail for small δ. Not attempted.

## Checks
- Direct `lean -M 6144` against `/workspace/v3logs/overlay`, one process at a time, rc 0, zero warnings/output.
  - Run 1 (first 164 lines): wall 7.8 s, CPU 1.2 s user + 0.9 s sys, peak RSS 1668 MiB. Total RAM 16002 MiB; available 7379 MiB (46%) before, minimum 7334 MiB (45%).
  - Run 2 (full file): wall 1.2 s, CPU 1.0 s user + 0.3 s sys, peak RSS 1680 MiB; available 9133 MiB (57%), minimum 8898 MiB (55%).
  - Axiom check (temp file, now deleted): wall 2.0 s, CPU 1.7 s user, peak RSS 1646 MiB; minimum available 55%.
  - No Numerics processes before any run (no waits).
- `#print axioms`: all 9 public theorems depend on `[propext, Quot.sound]`. The temp file's deliberate `1 = 2` check
  errored as expected, confirming the checker reports errors.
- grep: no sorry/admit/Classical/native_decide/omega/simpa/grind.

## Standard caveats
- Build: direct lean against copied oleans, not lake-verified (stale-trace caveat).
- δ_min: task2n upgrades "δ_min = 0 necessary only" to "δ_min exact, given the TM identification + spectral data (analytic, handwritten)".
  The Lean here proves only the sufficiency core, abstractly.
- U(1): nothing here is group-specific. The budget is satisfied by U(1) at small volume (task2n §2), so any non-abelian
  content sits in the volume-uniform version (`audits/SCOPE-HCROSS-UNIF-2026-11-16.md`).
- Not chart closure.
