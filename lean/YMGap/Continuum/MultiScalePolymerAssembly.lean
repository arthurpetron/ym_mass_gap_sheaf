/-
Track B / R2 — **THE MULTI-SCALE (scale-by-scale) BAŁABAN POLYMER EXPANSION**: assembling the
PROVED single-scale polymer bounds into a scale-indexed product and isolating EXACTLY where the
scale-by-scale convergence of the continuum measure needs `singleStep`.

# The obligation (read first)

The Bałaban RG assembles the continuum measure scale-by-scale.  At each scale `k` the single-scale
polymer (cluster) expansion is controlled — the Kotecký–Preiss bound
`Σ_{n<N} |z_n(w_k)| ≤ 1/(1 − μ·g_k²)` (`KPFieldAmplitude.clusterSum_le`, PROVED combinatorially).
Each single-scale polymer measure is thus a bounded `Q'`.  The CONTINUUM measure is the MULTI-SCALE
product of the per-scale factors:

    continuumMeasure  =  ∏_{k=0}^∞ (single-scale factor at scale k)  =  ∏_{k} (1 − δ_k) ,

where `δ_k ∈ [0,1]` is the per-scale POLYMER DEFECT (the per-scale erosion `1 − (single-scale_k
survival)`).  This infinite product converges to a STRICTLY POSITIVE limit — the measure does not
collapse to `0` — **iff the scale-by-scale defects are summable**, `Σ_k δ_k < ∞`; concretely, with a
finite budget `Σ_k δ_k ≤ B_δ < 1`, the product is floored by `1 − B_δ > 0`.

# What this module builds (axiom-clean `Q'`/`Nat`)

  * **Single-scale (PROVED, reused).**  `singleScale_partition_bounded` re-exports the PROVED KP
    convergence `Σ_{n<N} |z_n(w_k)| ≤ 1/(1 − μg_k²)` at EVERY scale `k` — the scale-indexed
    single-scale polymer bound.

  * **The multi-scale product (NEW).**  `polymerProduct δ K = ∏_{k<K}(1 − δ_k)`, the scale-indexed
    continuum-measure product.

  * **THE MULTI-SCALE CONVERGENCE GIVEN SUMMABILITY (NEW, PROVED).**
    `multiScaleProduct_floor` — for `δ_k ∈ [0,1]` with the finite budget `Σ_{k<K} δ_k ≤ B_δ` (the
    scale-by-scale summability) and the anchor-dominance `B_δ < 1`, the multi-scale product is
    uniformly floored:

        ∀ K,  (1 − B_δ)  ≤  ∏_{k<K}(1 − δ_k)   ∧   0 < 1 − B_δ .

    So the continuum measure is `> 0` — GIVEN the summable per-scale defect.  This is the
    Weierstrass product bound `∏(1 − δ_k) ≥ 1 − Σδ_k`, discharged through the PROVED telescoping
    ADEQUACY `additiveErosion_uniform_floor` (with additive erosion `ε ≡ 0`).

  * **The assembly (NEW).**  `MultiScalePolymerExpansion` bundles the scale-indexed single-scale KP
    data with the per-scale defect and its finite summability budget; `continuumMeasure_floor`
    derives the positive continuum product floor.  The summability budget field is the SOLE open
    input.  DELIBERATELY UNINHABITED for the physical defect.

  * **The isolation (NEW).**  `trueMargin_is_multiscale_product` shows `SingleStepDefectBound`'s
    `singleStep` IS exactly the per-scale multiplicative erosion step `(1 − δ_model_k)·m_k ≤ m_{k+1}`
    of the multi-scale product; `trueMargin_multiscale_floor_of_budget` derives the whole positive
    continuum floor for the TRUE margin from `singleStep` + the (model) rational summability budget.
    `MultiScalePolymerSummability := SingleStepDefectBound` records the identity of the real
    per-scale summability with `singleStep` at the level of the SAME irreducible core.

# HONEST VERDICT (maximally adversarial — AGENTS.md Rule 6 / Rule 9)

The single-scale polymer bounds are PROVED (KP `clusterSum_le`).  The multi-scale product converges
to a POSITIVE continuum measure GIVEN the summable per-scale defect `Σδ_k ≤ B_δ < 1` — and THAT
implication is now PROVED (`multiScaleProduct_floor`, the telescoping adequacy: the Weierstrass
product bound made machine-checked).  So the multi-scale assembly given summability is a GENUINE
piece — it is BUILT.

The REAL per-scale defect summability (that the true 4D non-abelian per-scale polymer defect
`realδ_k` actually satisfies `Σ realδ_k ≤ B_δ < 1`) is NOT proved: it is `singleStep`, the real
per-step defect bound `realδ_k ≤ δ_model_k`.  The MODEL defect `δ_model = afDefectSeq` is the PROVED
transverse quadratic `≤ 6·pMult·(1 − w)²` and IS summable (`Σ 1/k²`, the deep-UV floor); the REAL
defect being `≤` it is the interacting-measure / fusion-local-CLT input — the config-space `z_1` /
`singleStep` — UNINHABITED.

So: the multi-scale polymer expansion ASSEMBLES the continuum measure GIVEN the summable per-scale
defect (the adequacy, BUILT), and the assembly ISOLATES the real per-scale summability = `singleStep`
(the real per-scale defect bound).  A single-scale bound is a piece, not the continuum measure; the
scale-by-scale convergence needs `singleStep`.  No guarded frontier bundle is inhabited; nothing is
faked; the 4D Yang–Mills mass gap remains OPEN.

# Numerics (mpmath dps 45, sympy exact — verified in scratch)

  * Weierstrass product bound `∏_{k<K}(1 − δ_k) ≥ 1 − Σ_{k<K}δ_k` for `δ_k ∈ [0,0.3]`: PASS (6
    random trials, `K ≤ 40`); hence `Σδ ≤ B_δ < 1 ⟹ ∏(1 − δ) ≥ 1 − B_δ > 0`.
  * summability distinction: `Σ 1/k² = 1.6449…` (finite: the transverse-quadratic model defect IS
    summable) vs `Σ 1/k` diverges (the linear single-polymer activity is NOT summable) — the
    per-scale summability is a genuine real condition, not automatic.
  * closed geometric budget `1/(1 − ½) = 2` (matches the single-scale KP head bound).

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat`, reusing the PROVED `additiveErosion_uniform_floor` (telescoping adequacy),
`KPFieldAmplitude.clusterSum_le` (single-scale KP), `afDefectSeq_nonneg`/`afDefectSeq_le_one`, and
the `SingleStepDefectBound` residual.  Every load-bearing declaration is `#print axioms`-gated to
`propext`/`Quot.sound` only.  No `Classical.*`, no `native_decide`, no `ring`, no `sorry`.  All
witnesses `Type`-level.  No frontier bundle inhabited.
-/
import YMGap.Continuum.AdditiveErosionAdequacy
import YMGap.Continuum.KPFieldAmplitude
import YMGap.Continuum.SingleStepDefectReduction

namespace YMGap.Continuum.MultiScalePolymerAssembly

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.UniformCouplingFromAF
open YMGap.Continuum.FieldSpaceCluster
open YMGap.Continuum.KPFieldAmplitude
open YMGap.Continuum.SingleStepDefectReduction

/-! ## 0. Local `Q'` order glue (self-contained, axiom-clean). -/

/-- `a < b ≤ c ⟹ a < c` on `Q'` (local copy; the `≤` on the RIGHT, mirroring the
`BalabanLargeFieldEntropy` helper). -/
theorem lt_of_lt_of_le {a b c : Q'} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  have e1 : a.num * (b.den : Int) < b.num * (a.den : Int) := h1
  have e2 : b.num * (c.den : Int) ≤ c.num * (b.den : Int) := h2
  show a.num * (c.den : Int) < c.num * (a.den : Int)
  have s1 : (a.num * (c.den : Int)) * (b.den : Int)
          < (b.num * (a.den : Int)) * (c.den : Int) := by
    have := Int.mul_lt_mul_of_pos_right e1
      (by exact_mod_cast c.den_pos : (0 : Int) < (c.den : Int))
    have hr : (a.num * (b.den : Int)) * (c.den : Int)
            = (a.num * (c.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (b.den : Int) (c.den : Int)]
    rwa [hr] at this
  have s2 : (b.num * (a.den : Int)) * (c.den : Int)
          ≤ (c.num * (a.den : Int)) * (b.den : Int) := by
    have := Int.mul_le_mul_of_nonneg_right e2
      (by exact_mod_cast Nat.le_of_lt a.den_pos : (0 : Int) ≤ (a.den : Int))
    have hr : (b.num * (c.den : Int)) * (a.den : Int)
            = (b.num * (a.den : Int)) * (c.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (c.den : Int) (a.den : Int)]
    have hr2 : (c.num * (b.den : Int)) * (a.den : Int)
             = (c.num * (a.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (b.den : Int) (a.den : Int)]
    rw [hr, hr2] at this; exact this
  have s3 : (a.num * (c.den : Int)) * (b.den : Int)
          < (c.num * (a.den : Int)) * (b.den : Int) :=
    Int.lt_of_lt_of_le s1 s2
  exact Int.lt_of_mul_lt_mul_right s3
    (by exact_mod_cast Nat.le_of_lt b.den_pos : (0 : Int) ≤ (b.den : Int))

/-- The additive-erosion sequence `ε ≡ 0` has a vanishing budget: `tailSum (fun _ => 0) 0 k ≤ 0`.
The multi-scale polymer product is a PURE multiplicative product (no additive erosion), so its
adequacy application takes `ε ≡ 0`, `B_ε = 0`. -/
theorem tailSum_zero_le (k : Nat) : tailSum (fun _ => (0 : Q')) 0 k ≤ (0 : Q') := by
  induction k with
  | zero => exact Q'.le_refl' 0
  | succ M ih =>
      show tailSum (fun _ => (0 : Q')) 0 M + (0 : Q') ≤ 0
      rw [Q'.add_zero']
      exact ih

/-! ## 1. THE SINGLE-SCALE POLYMER BOUND (PROVED, scale-indexed — reused).

At each scale `k` the single-scale cluster expansion is controlled: the KP convergence
`Σ_{n<N} |z_n(w_k)| ≤ 1/(1 − μ·g_k²)` holds uniformly in the cluster size `N`.  Re-exported straight
from the PROVED `KPFieldAmplitude.clusterSum_le`.  This is the scale-`k` single-scale polymer
measure, a bounded `Q'` — the per-scale factor the multi-scale product multiplies. -/

/-- **THE SCALE-INDEXED SINGLE-SCALE POLYMER BOUND** (PROVED).  At scale `k`, GIVEN the KP
small-activity gate `0 < 1 − μ·g_k²`, the single-scale cluster partition sum is bounded uniformly in
`N`:  `Σ_{n<N} |z_n(w_k)| ≤ 1/(1 − μ·g_k²)`.  Reuses `KPFieldAmplitude.clusterSum_le`. -/
theorem singleScale_partition_bounded {afr : AFRateModulus} (D : KPAmplitude afr) (k : Nat)
    (hsmall : (0 : Q') < 1 - D.mu * fieldActivity (afr.w (afCutoff afr + k))) (N : Nat) :
    finSum (D.zAmp k) N
      ≤ Q'.divPos 1 (1 - D.mu * fieldActivity (afr.w (afCutoff afr + k))) hsmall :=
  clusterSum_le D k hsmall N

/-! ## 2. THE MULTI-SCALE PRODUCT and its convergence GIVEN summability (NEW, PROVED).

The continuum measure is the scale-indexed product `∏_{k<K}(1 − δ_k)` of the per-scale polymer
factors, `δ_k` the per-scale defect.  It converges to a strictly positive limit iff the defects are
summable; with the finite budget `Σδ_k ≤ B_δ < 1` the product is floored by `1 − B_δ > 0`.  We
discharge this through the PROVED telescoping adequacy `additiveErosion_uniform_floor` (with additive
erosion `ε ≡ 0`, anchor `margin 0 = 1`) — the Weierstrass product bound `∏(1 − δ) ≥ 1 − Σδ` made
machine-checked. -/

/-- **THE MULTI-SCALE POLYMER PRODUCT** `∏_{k<K}(1 − δ_k)` — the scale-indexed continuum-measure
product of the per-scale polymer factors (empty product `= 1`). -/
def polymerProduct (δ : Nat → Q') : Nat → Q'
  | 0 => (1 : Q')
  | k + 1 => polymerProduct δ k * (1 - δ k)

@[simp] theorem polymerProduct_zero (δ : Nat → Q') : polymerProduct δ 0 = 1 := rfl
@[simp] theorem polymerProduct_succ (δ : Nat → Q') (k : Nat) :
    polymerProduct δ (k + 1) = polymerProduct δ k * (1 - δ k) := rfl

/-- **THE MULTI-SCALE CONVERGENCE GIVEN SUMMABILITY (PROVED).**  For a per-scale polymer defect
`δ_k ∈ [0,1]` with the finite scale-by-scale budget `Σ_{k<K}δ_k ≤ B_δ` (the summability) and the
anchor-dominance `B_δ < 1`, the multi-scale product is uniformly floored by the strictly positive
`1 − B_δ`:

    ∀ K,  (1 − B_δ)  ≤  ∏_{k<K}(1 − δ_k)   ∧   0 < 1 − B_δ .

So the continuum measure is `> 0` — GIVEN the summable per-scale defect.  This is the Weierstrass
product bound `∏(1 − δ) ≥ 1 − Σδ`, discharged through the PROVED telescoping adequacy
`additiveErosion_uniform_floor` (`ε ≡ 0`, `B_ε = 0`, `margin 0 = 1`). -/
theorem multiScaleProduct_floor (δ : Nat → Q') (Bδ : Q')
    (hδnn : ∀ k, (0 : Q') ≤ δ k) (hδ1 : ∀ k, δ k ≤ 1)
    (hbudget : ∀ k, tailSum δ 0 k ≤ Bδ) (hsum : Bδ < 1) :
    ∀ k, (1 - Bδ) ≤ polymerProduct δ k ∧ (0 : Q') < 1 - Bδ := by
  -- The multiplicative step is exactly the additive step with ε ≡ 0.
  have hstep : ∀ k,
      (1 - δ k) * polymerProduct δ k - (fun _ => (0 : Q')) k ≤ polymerProduct δ (k + 1) := by
    intro k
    show (1 - δ k) * polymerProduct δ k - (0 : Q') ≤ polymerProduct δ k * (1 - δ k)
    rw [Q'.sub_zero']
    exact Q'.le_of_eqv (Q'.mul_comm_eqv (1 - δ k) (polymerProduct δ k))
  -- anchor: 0 < 1 − B_δ, hence 0 < (1 − B_δ)·(margin 0 = 1).
  have hpos : (0 : Q') < 1 - Bδ := qSubPosOfLt hsum
  have hanchor : (0 : Q') < (1 - Bδ) * polymerProduct δ 0 := by
    show (0 : Q') < (1 - Bδ) * (1 : Q')
    exact lt_of_lt_of_le hpos (Q'.ge_of_eqv (Q'.mul_one_eqv (1 - Bδ)))
  -- The floor witness `additiveErosion_uniform_floor` returns is `(1 − B_δ)·1 − 0 ≃ 1 − B_δ`.
  have heqvFloor : ((1 - Bδ) * polymerProduct δ 0 - 0).eqv (1 - Bδ) := by
    show ((1 - Bδ) * (1 : Q') - 0).eqv (1 - Bδ)
    rw [Q'.sub_zero']
    exact Q'.mul_one_eqv (1 - Bδ)
  have R := additiveErosion_uniform_floor (polymerProduct δ) δ (fun _ => 0) Bδ 0
    hstep hδnn hδ1 (fun _ => Q'.le_refl' 0)
    (by show (0 : Q') ≤ (1 : Q'); decide) hbudget tailSum_zero_le hanchor
  intro k
  refine ⟨?_, ?_⟩
  · exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv heqvFloor) (R k).1
  · exact lt_of_lt_of_le (R k).2 (Q'.le_of_eqv heqvFloor)

/-! ## 3. THE ASSEMBLY — single-scale KP data + summable per-scale defect ⟹ positive measure. -/

/-- **`MultiScalePolymerExpansion afr` — the scale-by-scale Bałaban polymer expansion (`Type`,
Rule 6a; DELIBERATELY UNINHABITED for the physical defect).**  Bundles:

  * `kp` — the scale-indexed single-scale KP data (`KPAmplitude afr`): each scale's single-polymer
    activity, cluster amplitudes, and the PROVED tree-graph domination;
  * `smallField` — the per-scale KP small-activity gate `0 < 1 − μ·g_k²`, under which the single-scale
    cluster sum is bounded (`singleScale_partition_bounded`);
  * `δ` — the per-scale POLYMER DEFECT `δ_k ∈ [0,1]` (the per-scale erosion `1 − (single-scale_k
    survival)`);
  * **`budget` + `summable`** — THE SCALE-BY-SCALE SUMMABILITY, the SOLE open input: the finite
    budget `Σ_{k<K} δ_k ≤ B_δ` at every scale and the anchor-dominance `B_δ < 1`.  This is exactly
    what makes the multi-scale product `∏_k(1 − δ_k)` converge to a POSITIVE continuum measure.

For the physical 4D per-scale polymer defect the summability fields cannot be honestly supplied — they
are `singleStep` (§4).  UNINHABITED. -/
structure MultiScalePolymerExpansion (afr : AFRateModulus) : Type where
  /-- The scale-indexed single-scale KP amplitude data. -/
  kp : KPAmplitude afr
  /-- The per-scale KP small-activity gate `0 < 1 − μ·g_k²`. -/
  smallField : ∀ k, (0 : Q') < 1 - kp.mu * fieldActivity (afr.w (afCutoff afr + k))
  /-- The per-scale polymer defect `δ_k`. -/
  δ : Nat → Q'
  /-- `0 ≤ δ_k`. -/
  δ_nonneg : ∀ k, (0 : Q') ≤ δ k
  /-- `δ_k ≤ 1`. -/
  δ_le_one : ∀ k, δ k ≤ (1 : Q')
  /-- The finite scale-by-scale budget bound. -/
  Bδ : Q'
  /-- **THE SUMMABILITY** `Σ_{k<K} δ_k ≤ B_δ` at every scale (open input). -/
  budget : ∀ k, tailSum δ 0 k ≤ Bδ
  /-- **THE ANCHOR-DOMINANCE** `B_δ < 1` — the measure does not collapse (open input). -/
  summable : Bδ < (1 : Q')

/-- **THE CONTINUUM MEASURE** as the multi-scale polymer product `∏_{k<K}(1 − δ_k)`. -/
def MultiScalePolymerExpansion.continuumMeasure {afr : AFRateModulus}
    (M : MultiScalePolymerExpansion afr) (K : Nat) : Q' := polymerProduct M.δ K

/-- **THE POSITIVE CONTINUUM-MEASURE FLOOR** — the multi-scale product converges to a strictly
positive limit.  `(1 − B_δ) ≤ ∏_{k<K}(1 − δ_k)` at every truncation `K`, and `0 < 1 − B_δ`, from the
single summability datum (`budget` + `summable`) via `multiScaleProduct_floor` (the adequacy). -/
theorem MultiScalePolymerExpansion.continuumMeasure_floor {afr : AFRateModulus}
    (M : MultiScalePolymerExpansion afr) :
    ∀ K, (1 - M.Bδ) ≤ M.continuumMeasure K ∧ (0 : Q') < 1 - M.Bδ :=
  multiScaleProduct_floor M.δ M.Bδ M.δ_nonneg M.δ_le_one M.budget M.summable

/-- **THE SCALE-INDEXED SINGLE-SCALE BOUND of the assembly** (PROVED, reused).  At every scale `k`
the single-scale cluster partition sum is bounded, `Σ_{n<N} |z_n(w_k)| ≤ 1/(1 − μg_k²)`. -/
theorem MultiScalePolymerExpansion.singleScale_bounded {afr : AFRateModulus}
    (M : MultiScalePolymerExpansion afr) (k N : Nat) :
    finSum (M.kp.zAmp k) N
      ≤ Q'.divPos 1 (1 - M.kp.mu * fieldActivity (afr.w (afCutoff afr + k))) (M.smallField k) :=
  singleScale_partition_bounded M.kp k (M.smallField k) N

/-! ## 4. THE ISOLATION — the real per-scale summability = `singleStep`. -/

/-- **`singleStep` IS the per-scale multiplicative erosion step of the multi-scale product.**  The
`SingleStepDefectBound.singleStep` inequality `(1 − δ_model_k)·trueMargin_k ≤ trueMargin_{k+1}` is
EXACTLY the per-scale multiplicative step the multi-scale product `∏(1 − δ_model_k)` is built from —
with the true margin as the running partial product.  This exhibits `singleStep` as precisely the
recursion the scale-by-scale convergence consumes. -/
theorem trueMargin_is_multiscale_product (S : SingleStepDefectBound) (k : Nat) :
    (1 - afDefectSeq S.afr k) * S.trueMargin k - (fun _ => (0 : Q')) k ≤ S.trueMargin (k + 1) := by
  show (1 - afDefectSeq S.afr k) * S.trueMargin k - (0 : Q') ≤ S.trueMargin (k + 1)
  rw [Q'.sub_zero']
  exact S.singleStep k

/-- **THE TRUE-MARGIN CONTINUUM FLOOR FROM `singleStep` + THE (MODEL) RATIONAL SUMMABILITY BUDGET.**
Given a `SingleStepDefectBound S` (whose sole open field is `singleStep`) AND the rational
scale-by-scale summability budget of the MODEL defect `δ_model = afDefectSeq` — `Σ_{k<K} δ_model ≤ B_δ`
and `B_δ < 1` — the whole positive continuum floor holds FOR THE TRUE MARGIN:

    ∀ k,  (1 − B_δ)·trueMargin 0 − 0  ≤  trueMargin k    ∧    0 < (1 − B_δ)·trueMargin 0 − 0 .

The `δ_model` nonneg / `≤ 1` are PROVED (`afDefectSeq_nonneg`, `afDefectSeq_le_one`); the step is
`S.singleStep`; the anchor `0 ≤ trueMargin 0` is the PROVED strong-coupling `107/108`.  So the
true-margin continuum floor — the multi-scale polymer product for the TRUE margin — rests on exactly:
(i) `singleStep` (the real per-scale defect bound), and (ii) the rational summability budget of the
model defect (the rational form of the PROVED `Σ 1/k²` / product-floor summability).  This is the
scale-by-scale assembly of the continuum measure, with `singleStep` isolated as the real input. -/
theorem trueMargin_multiscale_floor_of_budget (S : SingleStepDefectBound) (Bδ : Q')
    (hbudget : ∀ k, tailSum (afDefectSeq S.afr) 0 k ≤ Bδ) (hsum : Bδ < 1) :
    ∀ k, (1 - Bδ) * S.trueMargin 0 - 0 ≤ S.trueMargin k
       ∧ (0 : Q') < (1 - Bδ) * S.trueMargin 0 - 0 := by
  have hstep : ∀ k,
      (1 - afDefectSeq S.afr k) * S.trueMargin k - (fun _ => (0 : Q')) k ≤ S.trueMargin (k + 1) :=
    trueMargin_is_multiscale_product S
  -- anchor-dominance: 0 = B_ε < (1 − B_δ)·trueMargin 0.
  have hpos : (0 : Q') < 1 - Bδ := qSubPosOfLt hsum
  have hanchor : (0 : Q') < (1 - Bδ) * S.trueMargin 0 :=
    Q'.mul_pos hpos S.trueMargin0_pos
  exact additiveErosion_uniform_floor S.trueMargin (afDefectSeq S.afr) (fun _ => 0) Bδ 0
    hstep (afDefectSeq_nonneg S.afr) (afDefectSeq_le_one S.afr) (fun _ => Q'.le_refl' 0)
    (Q'.le_of_lt S.trueMargin0_pos) hbudget tailSum_zero_le hanchor

/-- **THE REAL PER-SCALE SUMMABILITY = `singleStep` (named residual, NOT faked).**  The multi-scale
product converges to a positive continuum measure GIVEN the summable per-scale defect
(`multiScaleProduct_floor`, PROVED), and the single-scale bounds are PROVED
(`singleScale_partition_bounded`).  The REAL per-scale polymer defect being summable (`Σ realδ_k ≤
B_δ < 1` for the true 4D non-abelian multi-link defect) is the spacing-uniform gap survival
`SingleStepDefectReduction.SingleStepDefectBound.singleStep` — `realδ_k ≤ δ_model_k`.  Restated as a
`Type`-alias; UNINHABITED (it IS the real RG estimate).  A product built with an ASSUMED summable real
defect would be the Rule-9 fake — deliberately not written.  (Identification at the level of the SAME
irreducible core across confirmations, not an `rfl` between the distinct structures.) -/
def MultiScalePolymerSummability : Type :=
  SingleStepDefectReduction.SingleStepDefectBound

/-- The def-alias is exactly the named residual (Rule 9.8, proof not prose). -/
theorem multiScalePolymerSummability_eq :
    MultiScalePolymerSummability = SingleStepDefectReduction.SingleStepDefectBound := rfl

/-! ## 5. Honest verdict (AGENTS.md Rule 6 / Rule 9). -/

/-- **HONEST FINAL VERDICT.**

The multi-scale (scale-by-scale) Bałaban polymer expansion is BUILT and assessed.
**CONSTRUCTED / PROVED (the genuine pieces):**
  * **Single-scale (PROVED, reused):** the scale-indexed single-scale KP bound
    `Σ_{n<N}|z_n(w_k)| ≤ 1/(1 − μg_k²)` (`singleScale_partition_bounded`, from `clusterSum_le`) — each
    single-scale polymer measure is a bounded `Q'`.
  * **Multi-scale product (NEW):** `polymerProduct δ = ∏_{k<K}(1 − δ_k)`, the continuum-measure product.
  * **Multi-scale convergence GIVEN summability (NEW, PROVED):** `multiScaleProduct_floor` — for
    `δ_k ∈ [0,1]` with `Σδ_k ≤ B_δ < 1`, the product is floored by `1 − B_δ > 0`; the continuum
    measure is positive GIVEN the summable defect.  This is the Weierstrass product bound
    `∏(1 − δ) ≥ 1 − Σδ`, discharged through the PROVED telescoping adequacy
    `additiveErosion_uniform_floor` (`ε ≡ 0`).
  * **Assembly (NEW):** `MultiScalePolymerExpansion` + `continuumMeasure_floor` — single-scale KP data
    plus a summable per-scale defect give the positive continuum-measure floor.
  * **Isolation (NEW):** `trueMargin_is_multiscale_product` shows `singleStep` IS the per-scale
    multiplicative step; `trueMargin_multiscale_floor_of_budget` derives the whole true-margin
    continuum floor from `singleStep` + the (model) rational summability budget.

**RESIDUAL (NOT closed) — the real per-scale summability = `singleStep`:** the REAL 4D non-abelian
per-scale polymer defect being summable (`Σ realδ_k ≤ B_δ < 1`) is `singleStep` (`realδ_k ≤
δ_model_k`), `MultiScalePolymerSummability = SingleStepDefectBound` (UNINHABITED).  The MODEL defect
`δ_model = afDefectSeq` is the PROVED transverse quadratic and IS summable; the REAL defect being `≤`
it is the interacting-measure / config-space-`z_1` input.

So the multi-scale polymer expansion ASSEMBLES the continuum measure GIVEN the summable per-scale
defect (the adequacy, BUILT), and it ISOLATES the real per-scale summability = `singleStep` (the real
per-scale defect bound).  The multi-scale assembly given summability is a genuine piece; the real
summability is `singleStep`.  A single-scale bound is a piece, not the continuum measure; the
scale-by-scale convergence needs `singleStep`.  No guarded frontier bundle is inhabited; nothing is
faked; the 4D Yang–Mills mass gap remains OPEN. -/
theorem multiScalePolymerAssembly_honesty : True := trivial

end YMGap.Continuum.MultiScalePolymerAssembly

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.MultiScalePolymerAssembly.lt_of_lt_of_le
#print axioms YMGap.Continuum.MultiScalePolymerAssembly.tailSum_zero_le
#print axioms YMGap.Continuum.MultiScalePolymerAssembly.singleScale_partition_bounded
#print axioms YMGap.Continuum.MultiScalePolymerAssembly.multiScaleProduct_floor
#print axioms YMGap.Continuum.MultiScalePolymerAssembly.MultiScalePolymerExpansion.continuumMeasure_floor
#print axioms YMGap.Continuum.MultiScalePolymerAssembly.MultiScalePolymerExpansion.singleScale_bounded
#print axioms YMGap.Continuum.MultiScalePolymerAssembly.trueMargin_is_multiscale_product
#print axioms YMGap.Continuum.MultiScalePolymerAssembly.trueMargin_multiscale_floor_of_budget
#print axioms YMGap.Continuum.MultiScalePolymerAssembly.multiScalePolymerSummability_eq
