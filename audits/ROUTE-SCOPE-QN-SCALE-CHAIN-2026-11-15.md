# ROUTE SCOPE — scale chain with per-step ratio `q_n` instead of 2 (2026-11-15)

**Label: SCOPING ONLY. Nothing built: the estimate is above the ~300-line threshold. No theorem claimed.** Box only.

U(1) note: the seed witness at `w ≤ 1/55` is abelian-valid, so it isn't non-abelian evidence. Any uniform gap at `w ≳ 1/8` would NOT hold for U(1), so it would be genuine non-abelian content. YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved.

## Verdict
- **Additive: yes.** No edits to existing statements are needed. The final per-scale conclusion `WilsonVacuumSqContraction hw0 hw1 width r` (`BF4WilsonAllNomeExprMixRateContraction.lean:61`) is a time-1 contraction at a single scale. It does not depend on the factor 2, so a parallel chain can produce it at every scale, next to `scaleChain_afBudget_floor` and `scaleChain_crossover_floor`.
- **Not a route-(i)-type blocker:** the 2 is baked into definitions, but only definitions of the chain's own machinery, which can be duplicated under new names. It is not in any definition that downstream gap statements consume.
- **Size: about 500–750 lines over 3–4 commits, so above ~300. Not built**, per the brief.

## Where the 2 is baked in (all would get new parallel versions)
1. `SchurDecomposition` (`RG/RelativeDissipationScaleChain.lean:77–85`): uses `completedTime hwF0 hwF1 2` against `completedTime hwC0 hwC1 1`.
2. `contraction_of_relative_comparison` (`Continuum/BF4WilsonAllNomeRGRelativeDissipation.lean:152`, hypothesis at :161) and `twoStepFactor_of_relative_comparison` (:123).
3. `WilsonVacuumSqTwoStepFactor` (`Continuum/BF4WilsonAllNomeRGStepComposition.lean:278–283`): `completedTime 2`.
4. `vacuumSq_explicitRate_of_twoStepFactor` (`Continuum/BF4WilsonAllNomeRGTwoStepRecovery.lean`, 144 lines). It recovers the one-step rate from a two-step bound via Cauchy–Schwarz, `‖Ty‖² = ⟨y, T²y⟩ ≤ ‖y‖·‖T²y‖`.
5. `explicitRate α = (3 + α)/4` (`Continuum/RGExplicitRationalRate.lean:31`, 127 lines). This is the rational square-root upper bound (`√α ≤ (1+α)/2`, squared form).
6. `relativeRate` (`Continuum/BF4WilsonAllNomeRGDissipationBudget.lean:178`) and `relativeRate_margin_lower` (:232, the `half^n` at :237). `relativeRate_side_floor` (`RG/RelativeDissipationScaleChain.lean:163`) then gives the `2^n` floor.

## Design of the `q_n` chain (what would be built)
- **Integer times.** `completedTime` takes `Nat`, so the ratio must be rational: `q_n = p_n / p'_n`, comparing `T_F(p_n)` with `T_C(p'_n)`.
  - Integer `p_n` alone is not enough. If `p > q_true`, the floor bounds `∏p·(1−r_n)`, and the physical mass bound `∏q·(1−r_n)/a_0 ≥ floor·∏(q/p)/a_0` decays.
  - Example: `afNome` jump steps (mass ratio ≈ 2^1.42 ≈ 2.68) would use `8/3`; ordinary steps `2/1`.
- Pieces:
  a. `SchurDecompositionQ p p'` and `pStepFactor` defs: about 40 lines.
  b. Coarse multi-step contraction: `WilsonVacuumSqContraction r` ⇒ `‖T_C(p')x‖² ≤ r^{2p'}‖x‖²`, by induction with `completedInner_time_sum` (`BF4WilsonAllNomeCompletedTime.lean:158`): about 60 lines.
  c. p-step recovery: `‖T_F(p)y‖² ≤ α‖y‖²` ⇒ `‖T_F(1)y‖² ≤ α^{1/p}‖y‖²` in rational form. This needs log-convexity, `‖Ty‖^{2p} ≤ ‖y‖^{2(p−1)}·‖T^p y‖²`, by induction on Cauchy–Schwarz in `RC`. That is the riskiest piece (the two-step version alone is 144 lines): about 150–250 lines.
  d. Rational p-th root bound `explicitRateP p α = ((p−1) + α)/p ≥ α^{1/p}` (Bernoulli / AM–GM over `Q'`): about 60–100 lines.
  e. Rate recursion `r_{n+1} = explicitRateP(p_n, δ_n + (1−δ_n)·r_n^{2p'_n})`, and the margin lower bound `∏_{i<n} q_i · (1 − r_n) ≥ (1−s)(s − Dq)` replacing `half^n`. The existing `computedRate` machinery in `DissipationBudget` is specialised to 1/2, so this is about 150–200 lines.
  f. `scaleChain_q_floor` (and a `_crossover` variant), mirroring the existing proofs: about 60–80 lines.

## Composition with the gap conclusion
- At scale `j0+n` the chain gives lattice rate `r_n`, so lattice mass `m_n ≥ −ln r_n ≥ 1 − r_n`.
- The spacing is `a_n = a_0/∏_{i<n} q_i`, so the physical mass is `m_n/a_n ≥ ∏q_i·(1−r_n)/a_0 ≥ floor/a_0`.
- So `∏q_i(1−r_n)` is the right quantity; it reduces to today's `2^n(1−r_n)` at `q ≡ 2`. This composition is analysis (one line of algebra once (e) exists), not built.
- `δ_min` would then become `max(0, 1 − (1−ρ_F^{2p})/(1−ρ_C^{2p'}))`, which is 0 iff `p·m_F ≥ p'·m_C`. Numerics can rerun it with the per-step ratios.

## Risks
- (c) in constructive `RC`: Cauchy–Schwarz iteration plus rational roots, without Mathlib.
- The `p_n` choice must match the true physical ratio, and is itself an input per step. A wrong `p_n` either moves the cost into `δ` (p too small) or makes the continuum floor decay (p too large).
- None of this addresses `hupper` / `hschur`, which stay OPEN.

## Recommendation
Build only if YM Bot approves about 600 lines (3–4 commits). Order: (b), (d) and (a) first (cheap and checkable), then (c), then (e) and (f). A cheaper alternative that needs no new chain is a schedule whose per-step mass ratio is ≈ 2 throughout: a smooth log term instead of `⌊log₂(j+1)⌋`, and about 1.4× finer crossover steps per Numerics §7. That is a new `NomeSchedule` (about 150–250 lines) plus a new instance.
