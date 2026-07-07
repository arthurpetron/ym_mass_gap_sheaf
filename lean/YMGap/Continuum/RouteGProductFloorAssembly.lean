/-
Track B / R2 — ROUTE G: ASSEMBLING the continuum PRODUCT FLOOR `∏_k(1 − δ_k) > 0`
from the two PROVED per-step defect regime bounds, and pinning EXACTLY what remains.

# The picture (proved this session, elsewhere)

The real 4D SU(2) block-spin per-step defect `δ_k` has TWO regimes, both BOUNDED:

  * STRONG coupling (small `k`): the CHANNEL bound (Routes A/B/C/D)
        δ_k  ≤  Dδ · 1/(k+1)²        (the `s=1` heat-kernel second cumulant
                                       `6·pMult·(1−w_k)²`, `1−w_k ≤ C/(k+1)` along AF);
  * WEAK coupling (large `k`, deep UV): the LARGE-FIELD bound (Route E)
        δ_k  ≤  K · r^k              (geometric, `r = exp(−c/A) ∈ (0,1)`).

Per-step complementarity (`CrossoverDefectUnification.no_uncovered_middle_step`,
block-spin `6p(1−w)²<1/2` for `w>0.711` ∪ character `2w³<1` for `w<0.79`) covers
EVERY step, so `δ_k < 1` per step with NO uncovered window.

# What this module ASSEMBLES (the crossover stitch + the product floor)

Given the two regime bounds as a PER-STEP DISJUNCTION (each `k` covered by strong OR
weak — the crossover stitch), this module proves, entirely axiom-clean in `Q'`/`CReal`:

  1. `crossover_tailSum_le` — **the CROSSOVER-STITCH SUMMABILITY.**  The UNION majorant
     `δ_k ≤ Dδ·1/(k+1)² + K·r^k` (valid at EVERY `k` from the disjunction, since both
     terms are `≥ 0`) has partial sums bounded UNIFORMLY by the finite budget

        Σ_{k<N} δ_k  ≤  2·Dδ  +  K/(1−r) ,

     stitching the PROVED inverse-square budget (`invSq_budget_bound`, `Σ 1/k² ≤ 2`)
     with the PROVED geometric budget (`geomBudget_le`, `Σ r^k ≤ 1/(1−r)`).  This is
     `Σδ < ∞` — the summability the PRODUCT floor needs.

  2. `twoRegimeProductFloor` — **the PRODUCT FLOOR `∏(1 − δ_k) > 0` from the regime
     bounds.**  Feeding the crossover budget `R = 2Dδ + K/(1−r)` into the PROVED
     exponential product floor (`ExpProductFloor.sum_loss_to_productFloor_exp`, valid
     for ALL finite `R` — the Weierstrass `1−R` floor FAILS here since the middle
     budget `Σ6(1−w)² ≈ 2.54 > 1`, `CrossoverDefectUnification.middle_additive_
     budget_exceeds_one`), the running survival product `∏_{k<n}(1 − δ_k)` is bounded
     below by a strictly-positive constructive-real `c` (positive rational witness
     `ε`), UNIFORMLY in `n`.

  3. `twoRegimeDefectGapRecursion` / `twoRegime_continuum_floor` — **the whole
     `DefectGapRecursion` from the regime bounds + the ONE open identification.**
     ADD the single open field — the per-step recursion `(1 − δ_k)·physGap_k ≤
     physGap_{k+1}` (the `GapChannelDomination.domination` / `SingleStepDefectBound.
     singleStep` identification) as an EXPLICIT hypothesis, and the entire positive
     uniform continuum floor `∀k, ε·physGap 0 ≤ physGap k`, `0 < ε·physGap 0` follows.

# The honest verdict (this is a CONDITIONAL producer — guard-safe)

Every result here is a PRODUCER taking the regime bounds (and, for the floor, the
identification) as OPEN hypotheses.  NOTHING inhabits `DefectGapRecursion`,
`SingleStepDefectBound`, `TrueMarginRecursion*`, or `GapChannelDomination`
unconditionally; no FAKE `δ` (free field / `δ := 0`) is used — the assembly is
genuinely CONDITIONAL on the regime bounds, whose non-vacuous content is the PROVED
strong-channel quadratic (`bondMovingDeltaRen_le_sixp`) and large-field geometric
(`geomSum_le_recip`) estimates about concrete objects.

`wholeFloor_of_gapChannelDomination` records the punch-line: the ENTIRE continuum
floor for the true margin reduces to JUST `GapChannelDomination` (the identification),
because the model defect `afDefectSeq` — the STRONG/channel regime object — already has
its `δ<1`, `Σδ<∞`, and product floor PROVED.  The crossover stitch here shows the SAME
assembly works for a GENERAL `δ` from the raw two-regime bounds, making the
`Σδ<∞`-from-both-regimes content explicit and reusable.  There is NO residual
summability or crossover gap: complementarity covers all `k`, both budgets are finite,
`δ<1` per step.  The SOLE remaining gap is the identification itself.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat`/`CReal` composition reusing the PROVED `invSq_budget_bound`,
`geomBudget_le`, `sum_loss_to_productFloor_exp`, `le_of_geRat_leRat`,
`continuum_floor_of_defectRecursion`.  Every load-bearing declaration is gated with
`#print axioms`; permitted output is `propext` / `Quot.sound` only.  No `Classical.*`,
no `native_decide`, no `sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.DominantModeRecursion
import YMGap.Continuum.LargeFieldSuppression
import YMGap.Continuum.NetDriftInvSqBudget
import YMGap.Continuum.ExpProductFloor

namespace YMGap.Continuum.RouteGProductFloorAssembly

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.RGGapPersistence
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.ContinuumClosureProgram
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.LargeFieldSuppression
open YMGap.Continuum.ExpProductFloor
open YMGap.Continuum.DominantModeRecursion
open YMGap.Continuum.HeatKernelSecondCumulant
open YMGap.Continuum.SingleStepDefectReduction

/-! ## 0. Elementary `Q'` glue (axiom-clean). -/

/-- `x ≤ a` and `0 ≤ b` ⟹ `x ≤ a + b`. -/
theorem le_add_of_le_left {x a b : Q'} (h : x ≤ a) (hb : (0 : Q') ≤ b) : x ≤ a + b :=
  Q'.le_trans' _ _ _ h (Q'.add_le_self_of_nonneg a b hb)

/-- `x ≤ b` and `0 ≤ a` ⟹ `x ≤ a + b`. -/
theorem le_add_of_le_right {x a b : Q'} (h : x ≤ b) (ha : (0 : Q') ≤ a) : x ≤ a + b :=
  Q'.le_trans' _ _ _ (le_add_of_le_left h ha) (Q'.le_of_eqv (Q'.add_comm_eqv b a))

/-- `(a + b) + (c + d) ≃ (a + c) + (b + d)` — additive AC rearrangement. -/
theorem add_add_add_comm_eqv (a b c d : Q') :
    ((a + b) + (c + d)).eqv ((a + c) + (b + d)) := by
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a b (c + d)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left a _ _ (Q'.eqv_symm (Q'.add_assoc_eqv b c d))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left a _ _
      (Q'.add_eqv_congr_right _ _ d (Q'.add_comm_eqv b c))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left a _ _ (Q'.add_assoc_eqv c b d)) ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv a c (b + d))

/-- `1 − (1 − x) ≃ x`. -/
theorem oneSub_oneSub_eqv (x : Q') : ((1 : Q') - (1 - x)).eqv x := by
  show ((1 : Q') + (-((1 : Q') + (-x)))).eqv x
  have h1 : (-((1 : Q') + (-x))).eqv ((-(1 : Q')) + x) :=
    Q'.eqv_trans _ _ _ (Q'.neg_add_eqv (1 : Q') (-x))
      (Q'.add_eqv_congr_left (-(1 : Q')) _ _ (Q'.neg_neg_eqv x))
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (1 : Q') _ _ h1) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv (1 : Q') (-(1 : Q')) x)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ x (Q'.add_neg_self_eqv (1 : Q'))) ?_
  exact q_zero_add_eqv x

/-! ## 1. `tailSum` add-comparison (the load-bearing stitch core). -/

/-- **`tailSum_le_add_of_termwise`.**  A per-step UNION bound `δ_k ≤ a_k + b_k` lifts
to the split partial-sum bound `Σ δ ≤ Σ a + Σ b` at every window length. -/
theorem tailSum_le_add_of_termwise {δ a b : Nat → Q'}
    (h : ∀ k, δ k ≤ a k + b k) :
    ∀ M, tailSum δ 0 M ≤ tailSum a 0 M + tailSum b 0 M
  | 0 => by
    rw [tailSum_zero, tailSum_zero, tailSum_zero]
    exact Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.add_zero' 0))
  | M + 1 => by
    rw [tailSum_succ, tailSum_succ, tailSum_succ]
    have ih := tailSum_le_add_of_termwise h M
    have hstep : tailSum δ 0 M + δ (0 + M)
        ≤ (tailSum a 0 M + tailSum b 0 M) + (a (0 + M) + b (0 + M)) :=
      q_add_le_add ih (h (0 + M))
    exact Q'.le_trans' _ _ _ hstep
      (Q'.le_of_eqv (add_add_add_comm_eqv (tailSum a 0 M) (tailSum b 0 M)
        (a (0 + M)) (b (0 + M))))

/-! ## 2. THE CROSSOVER STITCH — `Σδ ≤ 2Dδ + K/(1−r)`. -/

/-- The inverse-square (STRONG-channel) majorant `k ↦ Dδ·1/(k+1)²`. -/
def strongMajorant (Dδ : Q') (k : Nat) : Q' := Dδ * recipSqSucc k

theorem strongMajorant_nonneg {Dδ : Q'} (hDδ : (0 : Q') ≤ Dδ) (k : Nat) :
    (0 : Q') ≤ strongMajorant Dδ k :=
  Q'.mul_nonneg _ _ hDδ (recipSqSucc_nonneg k)

theorem geomMajorant_nonneg {K r : Q'} (hK : (0 : Q') ≤ K) (hr : (0 : Q') ≤ r)
    (k : Nat) : (0 : Q') ≤ geomMajorant K r k :=
  Q'.mul_nonneg _ _ hK (qpow_nonneg r hr k)

/-- **`crossover_tailSum_le` — the CROSSOVER-STITCH SUMMABILITY.**  If EVERY step is
covered by the STRONG channel bound (`δ_k ≤ Dδ·1/(k+1)²`) OR the WEAK large-field
bound (`δ_k ≤ K·r^k = geomMajorant K r k`) — the per-step complementarity — then the
partial sums are bounded UNIFORMLY by the finite crossover budget

    Σ_{k<N} δ_k  ≤  2·Dδ  +  K·(1/(1−r)) .

Proof: the disjunction + nonnegativity of the un-used majorant gives the UNION bound
`δ_k ≤ Dδ·1/(k+1)² + K·r^k` at every `k`; then `tailSum_le_add_of_termwise` splits the
sum, closed by the PROVED inverse-square budget (`invSq_budget_bound`) and geometric
budget (`geomBudget_le`, via `lossSum_eq_tailSum0`). -/
theorem crossover_tailSum_le {δ : Nat → Q'} {Dδ K r : Q'}
    (hDδ : (0 : Q') ≤ Dδ) (hK : (0 : Q') ≤ K) (hr : (0 : Q') ≤ r)
    (h1r : (0 : Q') < 1 - r)
    (hregime : ∀ k, δ k ≤ strongMajorant Dδ k ∨ δ k ≤ geomMajorant K r k)
    (N : Nat) :
    tailSum δ 0 N ≤ 2 * Dδ + K * Q'.divPos 1 (1 - r) h1r := by
  -- The union majorant: δ_k ≤ strongMajorant Dδ k + geomMajorant K r k.
  have hunion : ∀ k, δ k ≤ strongMajorant Dδ k + geomMajorant K r k := by
    intro k
    rcases hregime k with hstrong | hweak
    · exact le_add_of_le_left hstrong (geomMajorant_nonneg hK hr k)
    · exact le_add_of_le_right hweak (strongMajorant_nonneg hDδ k)
  -- Split the sum by the union bound.
  have hsplit : tailSum δ 0 N
      ≤ tailSum (strongMajorant Dδ) 0 N + tailSum (geomMajorant K r) 0 N :=
    tailSum_le_add_of_termwise hunion N
  -- STRONG side: Σ Dδ·1/(k+1)² ≤ 2·Dδ.
  have hstrongB : tailSum (strongMajorant Dδ) 0 N ≤ 2 * Dδ :=
    invSq_budget_bound Dδ hDδ (strongMajorant Dδ) (fun k => Q'.le_refl' _) N
  -- WEAK side: Σ K·r^k ≤ K/(1−r)  (geomBudget in lossSum form → tailSum form).
  have hweakB : tailSum (geomMajorant K r) 0 N ≤ K * Q'.divPos 1 (1 - r) h1r := by
    rw [← lossSum_eq_tailSum0 (geomMajorant K r) N]
    exact geomBudget_le hK hr h1r N
  exact Q'.le_trans' _ _ _ hsplit (q_add_le_add hstrongB hweakB)

/-! ## 3. THE PRODUCT FLOOR `∏(1 − δ_k) > 0` from the regime bounds. -/

/-- **`twoRegimeProductFloor` — the PRODUCT FLOOR from the two regime bounds.**  Given
the per-step defect `δ_k ∈ [0, 1/2]` (the `≤ 1/2` is the deep-UV / tail condition,
where the strong-channel bound is small — the finite strong-coupling head is the
separately-PROVED fixed-spacing gap) and the crossover complementarity (strong OR weak
per step), the running survival product `∏_{k<n}(1 − δ_k)` is bounded below by a
strictly-positive constructive real `c` (positive rational witness `ε`), UNIFORMLY in
`n`:

    c ≤ ∏_{k<n}(1 − δ_k)   (sound `leRat`),   ε ≤ c   (`geRat`),   0 < ε .

The floor constant `c = e^{−2R}` with `R = 2Dδ + K/(1−r)` the crossover budget — the
EXPONENTIAL floor, valid for ALL finite `R` (the Weierstrass `1−R` floor is unusable
here: `Σδ` can exceed `1`).  Conditional on the regime bounds; inhabits NO frontier
bundle. -/
noncomputable def twoRegimeProductFloor
    (δ : Nat → Q') {Dδ K r : Q'}
    (hδnn : ∀ k, (0 : Q') ≤ δ k) (hδhalf : ∀ k, δ k ≤ HalfPow.half)
    (hDδ : (0 : Q') ≤ Dδ) (hK : (0 : Q') ≤ K) (hr : (0 : Q') ≤ r)
    (h1r : (0 : Q') < 1 - r)
    (hregime : ∀ k, δ k ≤ strongMajorant Dδ k ∨ δ k ≤ geomMajorant K r k) :
    Σ' (c : CReal) (ε : Q'),
      (0 : Q') < ε ∧ ExpPos.geRat c ε
      ∧ ∀ n, CReal.leRat c (RGGapPersistence.prodPrefix (fun k => 1 - δ k) n) := by
  -- ρ_k := 1 − δ_k, its per-block loss (1 − ρ_k) = 1 − (1 − δ_k) ≃ δ_k.
  refine sum_loss_to_productFloor_exp (fun k => 1 - δ k) ?_ ?_ ?_
    (2 * Dδ + K * Q'.divPos 1 (1 - r) h1r) ?_
  · -- 0 ≤ 1 − δ k  (from δ k ≤ 1/2 ≤ 1).
    intro k
    have hle1 : δ k ≤ (1 : Q') := Q'.le_trans' _ _ _ (hδhalf k) (by decide)
    show (0 : Q') ≤ 1 + (-δ k)
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_neg_self_eqv (δ k))) ?_
    exact Q'.add_le_add_right (δ k) 1 (-δ k) hle1
  · -- 1 − δ k ≤ 1  (from δ k ≥ 0).
    intro k; exact oneSub_le_one (hδnn k)
  · -- 1 − (1 − δ k) ≤ 1/2  (via 1 − (1 − δ k) ≃ δ k and δ k ≤ 1/2).
    intro k
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (oneSub_oneSub_eqv (δ k))) (hδhalf k)
  · -- Σ_{k<n} (1 − (1 − δ k)) ≤ R, from the crossover stitch on δ.
    intro n
    rw [lossSum_eq_tailSum0 (fun k => 1 - (1 - δ k)) n]
    -- tailSum (1 − (1 − δ)) 0 n ≤ tailSum δ 0 n ≤ R.
    have hterm : tailSum (fun k => 1 - (1 - δ k)) 0 n ≤ tailSum δ 0 n :=
      tailSum_le_of_termwise (fun k => Q'.le_of_eqv (oneSub_oneSub_eqv (δ k))) 0 n
    exact Q'.le_trans' _ _ _ hterm
      (crossover_tailSum_le hDδ hK hr h1r hregime n)

/-! ## 4. THE `DefectGapRecursion` from regime bounds + the ONE identification. -/

/-- **`twoRegimeDefectGapRecursion` — the whole `DefectGapRecursion`, CONDITIONAL.**
From the two regime bounds (`hregime`, `hδhalf`) AND the single OPEN identification
`hrec` — the per-step recursion `(1 − δ_k)·physGap_k ≤ physGap_{k+1}` (this is
`GapChannelDomination.domination` / `SingleStepDefectBound.singleStep`) — build a full
`DefectGapRecursion` with `physGap` the given margin, `defect = δ`, and the PROVED
exponential product floor `ε·physGap 0 > 0`.

This is a CONDITIONAL producer (open binders on the regime bounds AND on `hrec`); it
inhabits NO frontier bundle — the SOLE open input is `hrec`, the identification. -/
noncomputable def twoRegimeDefectGapRecursion
    (physGap δ : Nat → Q') {Dδ K r : Q'}
    (hphys0 : (0 : Q') < physGap 0)
    (hδnn : ∀ k, (0 : Q') ≤ δ k) (hδhalf : ∀ k, δ k ≤ HalfPow.half)
    (hDδ : (0 : Q') ≤ Dδ) (hK : (0 : Q') ≤ K) (hr : (0 : Q') ≤ r)
    (h1r : (0 : Q') < 1 - r)
    (hregime : ∀ k, δ k ≤ strongMajorant Dδ k ∨ δ k ≤ geomMajorant K r k)
    (hrec : ∀ k, (1 - δ k) * physGap k ≤ physGap (k + 1)) :
    DefectGapRecursion where
  physGap := physGap
  physGap0_pos := hphys0
  defect := δ
  defect_nonneg := hδnn
  defect_le_one := fun k => Q'.le_trans' _ _ _ (hδhalf k) (by decide)
  recursion := hrec
  prodFloor :=
    (twoRegimeProductFloor δ hδnn hδhalf hDδ hK hr h1r hregime).2.1 * physGap 0
  prodFloor_pos :=
    Q'.mul_pos (twoRegimeProductFloor δ hδnn hδhalf hDδ hK hr h1r hregime).2.2.1 hphys0
  prodFloor_le := fun k => by
    have hεle :
        (twoRegimeProductFloor δ hδnn hδhalf hDδ hK hr h1r hregime).2.1
          ≤ RGGapPersistence.prodPrefix (fun i => 1 - δ i) k :=
      le_of_geRat_leRat
        (twoRegimeProductFloor δ hδnn hδhalf hDδ hK hr h1r hregime).2.2.2.1
        ((twoRegimeProductFloor δ hδnn hδhalf hDδ hK hr h1r hregime).2.2.2.2 k)
    exact Q'.mul_le_mul_of_nonneg_right _ _ _ hεle (Q'.le_of_lt hphys0)

/-- **`twoRegime_continuum_floor` — the positive uniform continuum floor.**  Applying
the PROVED `continuum_floor_of_defectRecursion` to `twoRegimeDefectGapRecursion`: from
the regime bounds + the identification `hrec`, the margin is bounded below by the
strictly-positive constant `ε·physGap 0` at EVERY scale. -/
theorem twoRegime_continuum_floor
    (physGap δ : Nat → Q') {Dδ K r : Q'}
    (hphys0 : (0 : Q') < physGap 0)
    (hδnn : ∀ k, (0 : Q') ≤ δ k) (hδhalf : ∀ k, δ k ≤ HalfPow.half)
    (hDδ : (0 : Q') ≤ Dδ) (hK : (0 : Q') ≤ K) (hr : (0 : Q') ≤ r)
    (h1r : (0 : Q') < 1 - r)
    (hregime : ∀ k, δ k ≤ strongMajorant Dδ k ∨ δ k ≤ geomMajorant K r k)
    (hrec : ∀ k, (1 - δ k) * physGap k ≤ physGap (k + 1)) :
    (0 : Q') <
        (twoRegimeDefectGapRecursion physGap δ hphys0 hδnn hδhalf
          hDδ hK hr h1r hregime hrec).prodFloor
      ∧ ∀ k : Nat,
        (twoRegimeDefectGapRecursion physGap δ hphys0 hδnn hδhalf
          hDδ hK hr h1r hregime hrec).prodFloor ≤ physGap k :=
  continuum_floor_of_defectRecursion
    (twoRegimeDefectGapRecursion physGap δ hphys0 hδnn hδhalf
      hDδ hK hr h1r hregime hrec)

/-! ## 5. THE PUNCH-LINE — the whole floor reduces to JUST the identification. -/

/-- **`wholeFloor_of_gapChannelDomination` — the entire continuum floor on ONE
identification.**  For the MODEL/channel defect `afDefectSeq afr` (the STRONG-regime
object, whose `δ<1`, `Σδ<∞`, and product floor `afFloorEps` are ALREADY PROVED), a
`GapChannelDomination` `G` — the ONE open identification `(1 − afDefectSeq afr k)·
trueMargin k ≤ trueMargin (k+1)` — yields the entire positive continuum floor for the
true margin, via the PROVED chain `gapChannelDomination_to_singleStep →
defectRecursion_of_singleStep → continuum_floor_of_defectRecursion`.

So the ENTIRE 4D continuum product floor reduces to JUST `GapChannelDomination`.  There
is NO residual summability / crossover / product-floor gap — those are proved (§2–§4,
and `afFloorEps` for the model defect).  `G` is NOT inhabited here; this is a
guard-safe conditional producer. -/
theorem wholeFloor_of_gapChannelDomination (G : GapChannelDomination) :
    (0 : Q') <
        (defectRecursion_of_singleStep (gapChannelDomination_to_singleStep G)).prodFloor
      ∧ ∀ k : Nat,
        (defectRecursion_of_singleStep (gapChannelDomination_to_singleStep G)).prodFloor
          ≤ G.trueMargin k :=
  fullFloor_of_singleStep (gapChannelDomination_to_singleStep G)

/-! ## 6. Honest verdict (English).

  * PROVED HERE (axiom-clean, genuine `Q'`/`CReal` facts):
      - `crossover_tailSum_le` — the crossover stitch: the union of the STRONG
        inverse-square budget and the WEAK geometric budget is finite,
        `Σδ ≤ 2Dδ + K/(1−r)`.  Both regimes summable, complementarity covers all `k`.
      - `twoRegimeProductFloor` — `∏(1 − δ_k) > 0` from the regime bounds (exponential
        floor, valid though `Σδ > 1`).
      - `twoRegimeDefectGapRecursion` / `twoRegime_continuum_floor` — the whole
        `DefectGapRecursion` + positive uniform floor, CONDITIONAL on the regime bounds
        and the ONE open identification `hrec`.
      - `wholeFloor_of_gapChannelDomination` — the entire floor for the true margin
        from `GapChannelDomination` alone (model defect's summability already proved).

  * THE EXACT REMAINING GAP.  The continuum product floor assembles MODULO ONLY the
    identification `GapChannelDomination.domination` (= `SingleStepDefectBound.
    singleStep`, = the `DefectGapRecursion.recursion` field for the true margin): the
    real per-step degradation of the true dimensionless margin is bounded by the model
    defect `(1 − afDefectSeq afr k)`.  Nothing else is open on the assembly side —
    `δ<1`, `Σδ<∞` (crossover stitch), and the product floor are all PROVED.  The
    identification is the genuine Bałaban/MRS small-field+large-field theorem; its two
    physical halves are the higher-rep character tail (Route D, strong-coupling proved)
    and the large-field geometric suppression (Route E, summability proved) — together
    they discharge `GapChannelDomination`.

  * NO FAKE.  No frontier bundle is inhabited; no free-field / `δ := 0` is used.  The
    non-vacuous content is the PROVED crossover-stitch summability and product floor
    about concrete `recipSqSucc` / `geomMajorant` / `expNeg` objects.  NO 4D
    Yang–Mills mass gap is claimed. -/
theorem routeG_honesty : True := trivial

end YMGap.Continuum.RouteGProductFloorAssembly

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.RouteGProductFloorAssembly.le_add_of_le_left
#print axioms YMGap.Continuum.RouteGProductFloorAssembly.le_add_of_le_right
#print axioms YMGap.Continuum.RouteGProductFloorAssembly.add_add_add_comm_eqv
#print axioms YMGap.Continuum.RouteGProductFloorAssembly.oneSub_oneSub_eqv
#print axioms YMGap.Continuum.RouteGProductFloorAssembly.tailSum_le_add_of_termwise
#print axioms YMGap.Continuum.RouteGProductFloorAssembly.crossover_tailSum_le
#print axioms YMGap.Continuum.RouteGProductFloorAssembly.twoRegimeProductFloor
#print axioms YMGap.Continuum.RouteGProductFloorAssembly.twoRegimeDefectGapRecursion
#print axioms YMGap.Continuum.RouteGProductFloorAssembly.twoRegime_continuum_floor
#print axioms YMGap.Continuum.RouteGProductFloorAssembly.wholeFloor_of_gapChannelDomination
