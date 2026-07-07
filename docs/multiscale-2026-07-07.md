# The Multi-Scale Bałaban Polymer Expansion — assembly + isolation

**File:** `lean/YMGap/Continuum/MultiScalePolymerAssembly.lean` (new, imported in `YMGap.lean`).
**Status:** full `lake build` GREEN (exit 0), `YMGapGuard` GREEN (exit 0), axiom-clean
(`propext`/`Quot.sound` only, no `sorryAx`/`Classical`/`native_decide`/`ring`/`sorry`).

## What the obligation was

The Bałaban RG assembles the continuum measure scale-by-scale: at each scale `k` the single-scale
polymer (cluster) expansion is controlled (KP, `Σ|z_n|≤1/(1−μg²)`, PROVED single-scale); the
continuum measure is the MULTI-SCALE product `∏_k(single-scale_k) = ∏_k(1−δ_k)`; this product
converges to a positive limit iff the per-scale defects `δ_k` are summable. Build the multi-scale
polymer bound and isolate exactly where the scale-by-scale convergence needs `singleStep`.

## What is BUILT (genuine, PROVED, axiom-clean)

1. **Single-scale (PROVED, reused).** `singleScale_partition_bounded` re-exports the PROVED KP
   convergence `Σ_{n<N}|z_n(w_k)| ≤ 1/(1−μg_k²)` at EVERY scale `k` (`KPFieldAmplitude.clusterSum_le`).
   Each single-scale polymer measure is a bounded `Q'` — the per-scale factor the product multiplies.

2. **The multi-scale product (NEW).** `polymerProduct δ K = ∏_{k<K}(1−δ_k)`, the scale-indexed
   continuum-measure product (empty product = 1; `polymerProduct_succ` = `… * (1−δ_k)`).

3. **THE MULTI-SCALE CONVERGENCE GIVEN SUMMABILITY (NEW, PROVED) — the decisive piece.**
   `multiScaleProduct_floor`: for `δ_k ∈ [0,1]` with the finite scale-by-scale budget
   `Σ_{k<K}δ_k ≤ B_δ` (the summability) and anchor-dominance `B_δ < 1`,

   ```
   ∀ K,  (1 − B_δ) ≤ ∏_{k<K}(1 − δ_k)   ∧   0 < 1 − B_δ .
   ```

   So the continuum measure is `> 0` — GIVEN the summable per-scale defect. This is the Weierstrass
   product bound `∏(1−δ) ≥ 1 − Σδ`, discharged through the PROVED telescoping ADEQUACY
   `additiveErosion_uniform_floor` with additive erosion `ε ≡ 0`, `B_ε = 0`, anchor `margin 0 = 1`.
   The multiplicative step `(1−δ_k)·P_k ≤ P_{k+1}` is exactly the additive step with `ε ≡ 0`
   (proved by `mul_comm`).

4. **The assembly (NEW).** `MultiScalePolymerExpansion` bundles the scale-indexed single-scale KP
   data (`kp`, `smallField`) with the per-scale defect (`δ`, `δ_nonneg`, `δ_le_one`) and its finite
   summability budget (`Bδ`, `budget : ∀k, tailSum δ 0 k ≤ Bδ`, `summable : Bδ < 1`).
   `continuumMeasure_floor` derives the positive continuum product floor; `singleScale_bounded`
   supplies the per-scale KP bound. The summability fields are the SOLE open input. UNINHABITED.

## Where it needs `singleStep` (the isolation, NEW)

- `trueMargin_is_multiscale_product`: `SingleStepDefectBound.singleStep`
  (`(1−δ_model_k)·trueMargin_k ≤ trueMargin_{k+1}`) IS exactly the per-scale multiplicative erosion
  step the multi-scale product `∏(1−δ_model_k)` is built from — the true margin as running product.
- `trueMargin_multiscale_floor_of_budget`: from a `SingleStepDefectBound S` (open field = `singleStep`)
  plus the (model) rational scale-by-scale summability budget `Σ afDefectSeq ≤ B_δ`, `B_δ < 1`, the
  WHOLE positive continuum floor holds for the TRUE margin. `afDefectSeq` nonneg/`≤1` are PROVED; the
  step is `S.singleStep`; the anchor `0 ≤ trueMargin 0` is the PROVED strong-coupling `107/108`.
- `MultiScalePolymerSummability := SingleStepDefectBound` (+ `_eq` rfl): the real per-scale defect
  summability is identified with `singleStep` at the level of the SAME irreducible core (the sanctioned
  def-alias pattern, matching `MultiScaleLargeFieldControl`, `MultiScaleLargeFieldControl_eq`).

## HONEST verdict (maximally adversarial)

- The **single-scale** polymer bounds are PROVED (`clusterSum_le`, reused scale-indexed).
- The **multi-scale product converges to a positive continuum measure GIVEN the summable per-scale
  defect** `Σδ_k ≤ B_δ < 1` — and THAT implication is now PROVED (`multiScaleProduct_floor`, the
  Weierstrass bound via the telescoping adequacy). This is a **genuine assembly piece — it is BUILT.**
- The **REAL per-scale summability** (that the true 4D non-abelian multi-link per-scale polymer defect
  `realδ_k` actually satisfies `Σ realδ_k ≤ B_δ < 1`) is **NOT proved: it is `singleStep`**, the real
  per-step defect bound `realδ_k ≤ δ_model_k`. The MODEL defect `δ_model = afDefectSeq` is the PROVED
  transverse quadratic `≤ 6·pMult·(1−w)²` and IS summable (numerics: `Σ1/k² = 1.6449…` finite; the
  linear activity `Σ1/k` diverges — so summability is a real condition, not automatic). The REAL
  defect being `≤` the model is the interacting-measure / config-space-`z_1` / fusion-local-CLT input —
  UNINHABITED.

**So: the multi-scale polymer expansion ASSEMBLES the continuum measure GIVEN the summable per-scale
defect (the adequacy, BUILT), and the assembly ISOLATES the real per-scale summability = `singleStep`
(the real per-scale defect bound).** A single-scale bound is a piece, not the continuum measure; the
scale-by-scale convergence needs `singleStep`. No overclaim: the assembly-given-summability is built;
the real summability is `singleStep`. No guarded frontier bundle is inhabited (only an uninhabited
structure + a def-alias to the existing residual); nothing is faked; the 4D Yang–Mills mass gap
remains OPEN.

## Numerics (mpmath dps 45, sympy exact)

- Weierstrass product bound `∏_{k<K}(1−δ_k) ≥ 1−Σ_{k<K}δ_k` for `δ_k∈[0,0.3]`: PASS (6 random trials,
  `K≤40`); hence `Σδ ≤ B_δ < 1 ⟹ ∏(1−δ) ≥ 1−B_δ > 0`.
- `Σ1/k² = 1.64493406684822643647…` (finite: transverse-quadratic model defect summable); `Σ1/k`
  diverges (linear activity NOT summable).
- `1/(1−½) = 2` (matches single-scale KP head bound).

## `#print axioms` (all load-bearing declarations)

```
lt_of_lt_of_le                                   : [propext]
tailSum_zero_le                                  : [propext]
singleScale_partition_bounded                    : [propext, Quot.sound]
multiScaleProduct_floor                          : [propext, Quot.sound]
MultiScalePolymerExpansion.continuumMeasure_floor: [propext, Quot.sound]
MultiScalePolymerExpansion.singleScale_bounded   : [propext, Quot.sound]   (no sorryAx)
trueMargin_is_multiscale_product                 : [propext, Quot.sound]
trueMargin_multiscale_floor_of_budget            : [propext, Quot.sound]
multiScalePolymerSummability_eq                  : [propext, Quot.sound]
```

## Guard / STOP

Only CONDITIONAL producers (open binders on `MultiScalePolymerExpansion` / `SingleStepDefectBound` /
budget hypotheses). Inhabits NONE of the 5 guarded frontier types (`Tier0Scorecard`,
`UniformSpacingFloor`, `ClayTarget`, `ClayTargetPinned`, `FrontierDAG`). `YMGapGuard` exit 0. No STOP
condition tripped; the 4D Yang–Mills mass gap remains OPEN.
