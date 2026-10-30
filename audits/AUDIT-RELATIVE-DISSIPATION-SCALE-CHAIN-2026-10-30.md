# Audit — Relative-Dissipation Scale Chain (Milestone 456, 2026-10-30)

## Scope & honest label
- Module: `lean/YMGap/RG/RelativeDissipationScaleChain.lean` (284 lines).
- Label: **conditional reduction. NOT gap evidence, NOT a proof of the 4D Yang–Mills mass gap.** The chain holds verbatim for any carrier satisfying the hypotheses, U(1) included.

## Proved (from the stated hypotheses)
- `hrelative_of_schurDecomposition`, `hrelative_of_schurDecomposition_carrier`: Schur decomposition `A-F = (1-δ)(A-C)+D`, `D ≥ 0` ⟹ relative comparison.
- `explicitRate_congr`, `contraction_congr`, `scaleChain_contraction`, `scaleChain_contraction_mixRate` (seed from the PROVED `wilsonVacuumSqContraction_mixRate`).
- `relativeRate_side_floor`: `(1-seed)(seed-D) ≤ 2^n·(1-r_n)` (conclusion, not hypothesis).
- `inv_nonneg`, `inv_sq_le_tele`, `afGap_le`, `finSum_le_tele`, `afQuadratic_prefix_budget`, `scaleChain_afBudget_floor`, `afBudget_example` (decide).

## OPEN (explicit hypotheses)
- `hupper_OPEN` (per-scale upper norm comparison), `hschur_OPEN` (per-scale Schur decomposition — equivalent to the relative comparison itself, i.e. a reformulation, not new information), `hafδ_OPEN` (`δ_k ≤ C·afGap²`), `hbudget` (numerical, decidable).

## Fixes vs the box draft
- Guessed name `Q'.ofNat_pos_of_pos` replaced by a local `ofNat_nonneg''`; `Q'.eqv_symm` takes implicit args; `Int.ofNat_nonneg` → `Int.natCast_nonneg`; unused `hc` dropped from `finSum_le_tele`.

## Verification
- Mac worktree `~/ymlean_prover_scratch/wt`, `LEAN_NUM_THREADS=2 nice -n 10 python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 8 --check …` with `--check-output` olean: 0 errors, 0 warnings.
- Axioms (temp-file collectAxioms over all 19 module constants, file deleted): union `{propext, Quot.sound}`.
