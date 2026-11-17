# PLAN: replace the 625 convenience guard in the strong-coupling seed chain, in place (2026-11-16, base c29e1688)

**Label: plan only. No `.lean` edits and no Lean runs in this round.** Executing it needs darthur's explicit OK on where the rebuild runs.
**Abelian-valid:** the improved reach (w ≤ 1/55 → w ≤ 1/48) is in the regime where U(1) is also strong-coupled. It is **not non-abelian evidence**.
Not chart closure.

## 1. Why the 625 is a convenience constant here (verified from source)
- In the descent chain the only use of `hs : entropyRate 625 (adjustedCoreRate w hd) < 1` is `oldGuard_coreRate_le`
  (`Continuum/BF4ExactSlabDescentDistanceDecay.lean:77`). It turns hs into `adjustedCoreRate ≤ comparisonCoreRate = 1/384` (:70).
- `oldGuard_distance_bound` (:160) then uses only that inequality together with the genuine descent count 96 (`connecting_weight_tail` :49, `comparison_guard` :74).
- `oldGuardBudget` (:98) does not depend on hs, and `timeRate = entropyRate 96 comparisonCoreRate = 1/4` (`BF4WilsonDescentUniformConnectedDecay.lean:45`).
- So the honest hypothesis is **`adjustedCoreRate w hd ≤ comparisonCoreRate`** ("384-guard"). It is implied by the 625 guard (via `oldGuard_coreRate_le`), so every existing caller keeps working through a one-token bridge.
- Reach (exact guard formula A(δ) = (2δ+δ²)(1−δ)^(−48), δ = 128w³): 384·A ≤ 1 holds at w = 1/48 (value 0.940) and fails at 1/47 (1.005). The real-root threshold is 1/47.1.
  The cheap no-go (dropping the collar factor) gives 384·pairedRate(δ) ≥ 1 from w ≥ 1/46 (value 1.011).
  These numbers are floating point; the Lean instances will use `decide +kernel`.
- **Scope note:** outside this chain, `entropyRate 625` appears in 239 files as the *genuine* older DFS lattice-animal degree K = (24+1)² = 625
  (`ClusterCount4DProgress.lean:44,300`), used as an actual decay rate there. Those uses are **not** part of this fix (see the CONVENIENCE-CONSTANTS audit, item F).

## 2. Edited statements (hypothesis weakened 625 → 384; conclusions unchanged)
| # | file:line | statement | change |
|---|---|---|---|
| 1 | `Continuum/BF4ExactSlabDescentDistanceDecay.lean:160` | `oldGuard_distance_bound` | `(hs : entropyRate 625 (adjustedCoreRate W hd) < 1)` → `(hs : adjustedCoreRate W hd ≤ comparisonCoreRate)`. In the proof, `oldGuard_coreRate_le hs` → `hs`. Keep `oldGuard_coreRate_le` (:77) as the bridge. Optionally rename to `guard384_distance_bound` with a deprecated alias. |
| 2 | `Continuum/BF4ExactSlabDescentSelectedCovariance.lean:65` | `finite_covariance_distance_bound` | same hypothesis change; the proof passes hs through |
| 3 | same file :113 | `covariance_distance_bound` | same |
| 4 | `Continuum/BF4WilsonDescentUniformConnectedDecay.lean:92` (hyp :95) | `connectedScalar_uniform_bound` | same |
| 5 | `Continuum/BF4WilsonAllNomeStrongCouplingUniformRate.lean:228,284,343,357,371` | `originalWindowScalar_connected_sc_bound`, `intrinsic_centered_sc_bound`, `scEvenMoment_le_geometric`, `scEvenMoment_first_le`, `sc_centered_twoStep_bound` | same |
| 6 | same file :385 (section variable) | → `sc_representative_twoStep_form_gap` :394, `sc_completed_twoStep_form_gap` :404, `sc_oneStep_norm_gap` :422, `allNome_strongCoupling_vacuumSq` :436, `allNome_strongCoupling_vacuumSq_all_widths` :443 | same. Module docstring :22–23 updated |
| 7 | same file :453/:461 | `existingNome_allNome_strongCoupling` | **statement unchanged**; the proof passes `oldGuard_coreRate_le existingNome_entropyRate.2` |
| 8 | `RG/StrongCouplingNomeThreshold.lean:53` | `def SCGuards` | `entropyRate 625 (adjustedCoreRate w hd) < 1` → `adjustedCoreRate w hd ≤ comparisonCoreRate`. Docstrings :1–27, :57 updated (1/55 → 1/48, 1/54 → 1/46) |
| 9 | same :61 | `def threshold` | → `threshold384 d hd := pairedRate d · (1−d)^(−48)`; the guard becomes `threshold384 d0 ≤ 1/384` |
| 10 | same :106 | `guards_of_delta_le` | hypothesis `hT : threshold d0 hd0 < 1` → `hT : threshold384 d0 hd0 ≤ comparisonCoreRate`; the last step drops the `625·` multiplication |
| 11 | same :149 | `threshold_inv55` | restated for threshold384 (still true); kept so `scGuards_of_le_inv55` (:156, **statement unchanged**) still proves |
| 12 | same, new | `inv48`, `threshold384_inv48` (`decide +kernel`), `scGuards_of_le_inv48`, `uniformSeedGap_of_le_inv48` | new theorems (additive) |
| 13 | same :186 | `not_scGuards_of_inv54_le` | **becomes FALSE** under the new guard (1/54 < 1/47.1 passes). Replace by `not_scGuards_of_inv46_le` (cheap bound `384·pairedRate(δ(1/46)) ≥ 1`). No external consumers (rg) |
| 14 | same :212 | `not_scGuards_dyadic` | **statement unchanged** (1/32 … 1/2 still fail); the proof re-routes via `not_scGuards_of_inv46_le` |
- **Call-site-only edits (statements unchanged; one bridge token each):**
  - `Continuum/BF4WilsonDescentCompletedGap.lean:58` (`hs` → `oldGuard_coreRate_le hs`);
  - `Continuum/BF4WilsonAllNomeRGStepComposition.lean:1294–1295`;
  - `Continuum/SpectralHalvingStrongCouplingCarrier.lean:74–75` (`existingNome_entropyRate.2` → `oldGuard_coreRate_le existingNome_entropyRate.2`).
- **Untouched (statements and proofs):** `uniformRate_of_guards` (:68), `uniformSeedGap_of_guards`, `scGuards_of_le_inv55`, `uniformSeedGap_of_le_inv55`, `uniformSeedGap_inv64`, `inv55`/`inv54` defs, `timeRate_eq`, `remainder_ge_one_quarter_half`.
- Estimated diff: ≈ 60–90 changed lines plus ≈ 40 new lines (item 12–13), in 8 files. One commit, under 400 lines.

## 3. Robust3 / r49 chain consumers
- `uniformRate_of_guards` + `scGuards_of_le_inv55` are used by:
  - `Robust3UndershootCrossoverInstance.lean:84–85` (`r3_seed`);
  - `RobustUndershootCrossoverInstance.lean:84–85`, `Robust2UndershootCrossoverInstance.lean:84–85`, `UndershootCrossoverInstance.lean:81–82`, `TwoLoopCrossoverInstance.lean:82–83`, `DyadicCrossoverInstance.lean:115–116`, `CrossoverInstance.lean:102–103`;
  - `Robust3MarginDischarge.lean:30` (open only).
- `SeededAfNomeSchedule.lean:47,143` uses `inv55`/`uniformSeedGap_of_le_inv55`; `Robust2UndershootAfSchedule.lean:159` uses `inv55`.
- **All their statements and proof terms stay unchanged.** `SCGuards` changes meaning (weaker), but `scGuards_of_le_inv55` still inhabits it. They only need recompiling.
  `robust3_floor_width_uniform` / `robust3_physical_floor_lmax_HK` / `Robust3CrossUniform` and the r49 docs are unaffected in statement.
- Optional follow-up (not in this plan): relax the seed joins (`robust3_join.1 : w₀ ≤ 1/55`) to ≤ 1/48. That is a statement change in schedule files and would need its own approval.

## 4. Rebuild cost
- Import closure (reverse dependencies over `lean/YMGap`, computed by a script over `import` lines) of the 5 statement-edited modules: **64 modules** (26 Continuum, 38 RG), ≈ 14,500 source lines. The 3 call-site files are inside that set.
  - Per module: DescentDistanceDecay 64, DescentSelectedCovariance 63, DescentUniformConnectedDecay 62, AllNomeStrongCouplingUniformRate 58, StrongCouplingNomeThreshold 33.
  - RG modules in the closure include all Robust/Robust2/Robust3 crossover, schedule and physical-units modules, Robust3CrossUniform, Robust3SchurRankOne and RelativeDissipationScaleChain.
- Timings: there are **no recorded per-file timings** for the 26 Continuum modules. The recorded RG overlay checks (`/workspace/v3logs/direct/cpu_2026-11-16.log`) take 1–8 s wall with ≈ 1.7 GB peak RSS each.
  Earlier `safe-lean` lake runs (`/workspace/v3logs/build_deps.log`) show build RSS up to ≈ 4.4 GB on heavy Continuum files.
- **Estimate (rough):** 38 RG × ~2–10 s plus 26 Continuum × ~20–120 s ≈ **10–60 CPU-min** sequentially (jobs = 1). Peak RSS ≈ 2–5 GB per job (fits `-M 6144`).
  The `decide +kernel` instance at 1/48 handles rationals with ~48-fold powers, comparable to the existing `threshold_inv55`.
- **Caveat:** the box worktree's oleans are a stale-trace overlay, not lake-verified. A real `lake build` may decide to rebuild much more than the 64-module closure. The direct-`lean` overlay route rebuilds exactly the closure in topological order.
  Box RAM is currently 16–27 % available (VM-level pressure), so a box rebuild must wait for ≥ 25 %. Mac use needs darthur's OK under the Mac safety rules.

## 5. Verification plan (when approved)
- Edit in one commit. Rebuild the 64 modules in import order with direct `lean -M 6144`, one at a time, RAM ≥ 25 %.
- Axiom check on `scGuards_of_le_inv48`, `uniformRate_of_guards`, `allNome_strongCoupling_vacuumSq_all_widths`, `r3_seed`, and `robust3_floor_width_uniform`: must be ⊆ {propext, Quot.sound}.
- Zero warnings. Re-verify the bundle.

## 6. Status update — 2026-11-16 (PT)
- **DEFERRED.** Per the 4:18 PM PT decision (darthur: "Okay. Please commit and push when it is a good place to do so."; YM Bot chose option (1)), the 625 in-place edit is **deferred to its own next build-and-push checkpoint**.
- The current push covers only the additive work through 3654e7cf plus this note. No `.lean` file is edited for the 625 fix in this checkpoint.
