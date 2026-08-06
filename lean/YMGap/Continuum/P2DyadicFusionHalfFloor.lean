/-
Track 11.7-fusion / R2t -- derive the dyadic physical half-floor.

`P2DyadicFusionGapBudget` still accepts a half-floor on every fine mode-one
square.  This file removes that all-scale field.  The proof has two pieces:

* the fixed base value at `N_0=4`, `w_0=11/12` is checked once;
* from scale one onward, the refined reference deficit is at most `4*u_k`,
  while `Cq <= 100` and the exact cutoff tail give a total physical deficit
  below one half.

The quotient sandwich already says `coarse <= fine^2`, so the resulting
coarse mode-one half-floor immediately supplies the fine-square half-floor
used by the additive-gap compiler.  No growing rational evaluation occurs.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2DyadicFusionGapBudget

namespace YMGap.Continuum.P2DyadicFusionHalfFloor

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.BlockingStepFrontier
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.CutoffTailRefinedCarrier
open YMGap.Continuum.EndpointCutoffTailClose
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.P2DyadicFusionGapBudget
open YMGap.Continuum.P2DyadicFusionGapEnvelope
open YMGap.Continuum.P2RetunedBlockingDictionary
open YMGap.Continuum.P2RetunedFusionDefectPower
open YMGap.Continuum.P2RetunedFusionPhysicalMode
open YMGap.Continuum.P2RetunedFusionPowerCertificate
open YMGap.Continuum.P2RetunedFusionReferenceGap
open YMGap.Continuum.P2RetunedRatioCompiler
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.RefinedRetune
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Scale-independent rational bounds -/

def q124 : Q' := Q'.mkPos 1 24 (by decide)
def q1576 : Q' := Q'.mkPos 1 576 (by decide)
def q17 : Q' := Q'.mkPos 1 7 (by decide)
def cutoffCoeffCap : Q' := Q'.ofNat 100

/-- Every dyadic margin after the anchor is at most `1/24`. -/
theorem dyadicMargin_le_q124 (k : Nat) (hk : 1 <= k) :
    dyadicMargin k <= q124 := by
  have hfirst : forall n, dyadicMargin (n + 1) <= dyadicMargin 1 := by
    intro n
    induction n with
    | zero => exact Q'.le_refl' _
    | succ n ih =>
        exact Q'.le_trans' _ _ _ (dyadicMargin_succ_le (n + 1)) ih
  cases k with
  | zero => omega
  | succ n =>
      exact Q'.le_trans' _ _ _ (hfirst n)
        (Q'.le_of_eqv (by decide : dyadicMargin 1 ≈ q124))

/-- Consequently the quadratic margin is at most `1/576`. -/
theorem dyadicMargin_square_le_q1576 (k : Nat) (hk : 1 <= k) :
    dyadicMargin k * dyadicMargin k <= q1576 := by
  have hsq := BondMovingQuadratic.sq_le_sq
    (dyadicMargin_nonneg k) (dyadicMargin_le_q124 k hk)
  exact Q'.le_trans' _ _ _ hsq
    (Q'.le_of_eqv (by decide : q124 * q124 ≈ q1576))

/-- The exact endpoint tail is at most `1/7` after the anchor. -/
theorem endpointTail_Ncut_le_q17 (k : Nat) (hk : 1 <= k) :
    endpointTail (Ncut k) <= q17 := by
  have h3 : 3 <= k + 2 := by omega
  have hN : 9 <= Ncut k := by
    unfold Ncut
    exact Nat.mul_le_mul h3 h3
  have hden : 21 <= 2 * Ncut k + 3 := by omega
  have hu :
      unit (2 * Ncut k + 3) (tailDenom_pos k) <=
        unit 21 (by decide) :=
    unit_antitone (by decide) (tailDenom_pos k) hden
  have ht : tailCut k <= Q'.ofNat 3 * unit 21 (by decide) :=
    Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 3) hu (by decide)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (endpointTail_Ncut k))
    (Q'.le_trans' _ _ _ ht
      (Q'.le_of_eqv (by decide : Q'.ofNat 3 * unit 21 (by decide) ≈ q17)))

/-! ## 2. Reference and physical deficit bounds -/

/-- The refined mode-one reference differs from one by at most `4*u_k`.
This combines the `3*u_k` unrefined Bernoulli deficit with the one-margin
refined displacement. -/
theorem refinedModeOne_deficit_le_four_margin (k : Nat) :
    (1 : Q') +
        -(retEig2 2 (by decide) (refineCoeff 2 (by decide))
          (dyadicWeight k) 1) <=
      Q'.ofNat 4 * dyadicMargin k := by
  let refined := retEig2 2 (by decide) (refineCoeff 2 (by decide))
    (dyadicWeight k) 1
  have hcoarse : unrefinedModeOneQ k + -refined <= dyadicMargin k := by
    exact Q'.le_trans' _ _ _ (le_absQ _)
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (absQ_sub_comm_eqv refined (unrefinedModeOneQ k)))
        (refined_unrefined_displacement_le k))
  have hgap := gap_le_reference_gap_add_errors
    (fine := (1 : Q')) (refFine := (1 : Q'))
    (coarse := refined) (refCoarse := unrefinedModeOneQ k)
    (fineError := (0 : Q')) (coarseError := dyadicMargin k)
    (Q'.le_of_eqv (Q'.add_neg_self_eqv 1)) hcoarse
  have hsum := Q'.add_le_add
    (one_sub_unrefinedModeOne_le_three_margin k)
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq (Q'.zero_add' (dyadicMargin k)))
      (Q'.eqv_symm (Q'.one_mul_eqv (dyadicMargin k)))))
  exact Q'.le_trans' _ _ _ hgap
    (Q'.le_trans' _ _ _ hsum
      (Q'.le_of_eqv (add_scaled_eqv 3 1 (dyadicMargin k))))

/-- Pointwise form of the corrected cutoff estimate on the dyadic mode. -/
theorem cutoffDefect_le_quadratic_add_tail
    {D : DyadicP2CoeffTailData} (R : DyadicP2RefinedCutoffData D) (k : Nat) :
    cutoffDefect R k <=
      R.Cq * (dyadicMargin k * dyadicMargin k) + endpointTail (Ncut k) := by
  rw [cutoffDefect_eq_moving R]
  unfold movingRefinedDefect
  exact defect_le_scaled_quadratic_add_tail
    (Ncut k) (dyadicWeight_nonneg k) (dyadicWeight_le_one k)
    R.Cq_nonneg (Q'.le_of_eqv (one_sub_dyadicWeight_eqv_margin k))
    1 (R.refinedBound k)

/-- With `Cq <= 100`, every post-anchor physical mode-one deficit is at most
one half.  The numerical comparison is a single fixed rational cell:
`4/24 + 100/576 + 1/7 <= 1/2`. -/
theorem physicalModeOne_deficit_le_half
    {D : DyadicP2CoeffTailData} (R : DyadicP2RefinedCutoffData D)
    (hCq : R.Cq <= cutoffCoeffCap) (k : Nat) (hk : 1 <= k) :
    (1 : Q') + -(fusionModeQ D.toControlFamily modeOne k) <= half := by
  have hphysical :
      (1 : Q') + -(fusionModeQ D.toControlFamily modeOne k) <=
        Q'.ofNat 4 * dyadicMargin k + cutoffDefect R k := by
    let refined := refinedModeOneQ D.toControlFamily k
    have hcoarse : refined + -(fusionModeQ D.toControlFamily modeOne k) <=
        cutoffDefect R k := by
      exact Q'.le_trans' _ _ _ (le_absQ _)
        (Q'.le_trans' _ _ _
          (Q'.le_of_eqv (absQ_sub_comm_eqv
            (fusionModeQ D.toControlFamily modeOne k) refined))
          (Q'.le_of_eqv
            (fusionModeOne_abs_refined_eqv_defect D.toControlFamily k)))
    have hgap := gap_le_reference_gap_add_errors
      (fine := (1 : Q')) (refFine := (1 : Q'))
      (coarse := fusionModeQ D.toControlFamily modeOne k)
      (refCoarse := refined) (fineError := (0 : Q'))
      (coarseError := cutoffDefect R k)
      (Q'.le_of_eqv (Q'.add_neg_self_eqv 1)) hcoarse
    have href : (1 : Q') + -refined <= Q'.ofNat 4 * dyadicMargin k := by
      simpa only [refined, refinedModeOneQ,
        DyadicP2CoeffTailData.toControlFamily,
        DyadicP2CoeffTailData.toCoeffControlFamily,
        P2RetunedCoeffControlFamily.toTailFamily] using
          refinedModeOne_deficit_le_four_margin k
    have hsum := Q'.add_le_add href
      (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.zero_add' (cutoffDefect R k))))
    exact Q'.le_trans' _ _ _ hgap hsum
  have hquad :
      R.Cq * (dyadicMargin k * dyadicMargin k) <=
        cutoffCoeffCap * q1576 :=
    Q'.mul_le_mul_of_nonneg hCq (dyadicMargin_square_le_q1576 k hk)
      (by decide) (Q'.mul_nonneg _ _
        (dyadicMargin_nonneg k) (dyadicMargin_nonneg k))
  have hcutoff : cutoffDefect R k <= cutoffCoeffCap * q1576 + q17 :=
    Q'.le_trans' _ _ _ (cutoffDefect_le_quadratic_add_tail R k)
      (Q'.add_le_add hquad (endpointTail_Ncut_le_q17 k hk))
  have href : Q'.ofNat 4 * dyadicMargin k <= Q'.ofNat 4 * q124 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (dyadicMargin_le_q124 k hk) (by decide)
  have htotal := Q'.add_le_add href hcutoff
  exact Q'.le_trans' _ _ _ hphysical
    (Q'.le_trans' _ _ _ htotal (by decide))

/-- Convert the post-anchor deficit bound into the desired mode-one floor. -/
theorem half_le_physicalModeOne
    {D : DyadicP2CoeffTailData} (R : DyadicP2RefinedCutoffData D)
    (hCq : R.Cq <= cutoffCoeffCap) (k : Nat) (hk : 1 <= k) :
    half <= fusionModeQ D.toControlFamily modeOne k := by
  have hdef := physicalModeOne_deficit_le_half R hCq k hk
  have hadd' : (1 : Q') <=
      half + fusionModeQ D.toControlFamily modeOne k :=
    YMGap.Continuum.EigenvalueShiftBridge.le_add_of_sub_le hdef
  have hsub : (1 : Q') + -half <=
      fusionModeQ D.toControlFamily modeOne k :=
    Q'.sub_le_of_le_add hadd'
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (by decide : half ≈ (1 : Q') + -half)) hsub

/-! ## 3. Remove the all-scale half-floor input -/

/-- The anchor is a single fixed small cell, independent of the coefficient-
tail proof stored in `D`. -/
theorem base_modeOne_half (D : DyadicP2CoeffTailData) :
    half <= fusionModeQ D.toControlFamily modeOne 0 := by
  have hclosed : half <= p2VacNorm (Ncut 0)
      (dyadicWeight_nonneg 0) (dyadicWeight_le_one 0) 1 := by
    decide
  exact Q'.le_trans' _ _ _ hclosed
    (Q'.ge_of_eqv (fusionModeOne_eqv_p2VacNorm D.toControlFamily 0))

/-- The preferred physical input after the half-floor reduction.  Besides the
already-honest quotient sandwich it retains only the scalar cutoff constant
cap; the entire half-floor family is derived. -/
structure DyadicP2PhysicalSandwichInput
    (D : DyadicP2CoeffTailData) (R : DyadicP2RefinedCutoffData D)
    (B : BlockingStep (fusionSeparator D.toControlFamily modeOne)) : Type where
  data : SpectrumPinnedP2QuotientDefectPowerData
    1 D.toControlFamily modeOne B
  cutoffCoeff_le : R.Cq <= cutoffCoeffCap

theorem DyadicP2PhysicalSandwichInput.modeOneHalf
    {D : DyadicP2CoeffTailData} {R : DyadicP2RefinedCutoffData D}
    {B : BlockingStep (fusionSeparator D.toControlFamily modeOne)}
    (P : DyadicP2PhysicalSandwichInput D R B) (k : Nat) :
    half <= fusionModeQ D.toControlFamily modeOne k := by
  cases k with
  | zero => exact base_modeOne_half D
  | succ k => exact half_le_physicalModeOne R P.cutoffCoeff_le (k + 1) (by omega)

/-- The coarse-to-fine square sandwich promotes the mode-one floor to the
fine-square floor expected by `P2DyadicFusionGapBudget`. -/
def DyadicP2PhysicalSandwichInput.toAdditiveInput
    {D : DyadicP2CoeffTailData} {R : DyadicP2RefinedCutoffData D}
    {B : BlockingStep (fusionSeparator D.toControlFamily modeOne)}
    (P : DyadicP2PhysicalSandwichInput D R B) :
    DyadicP2PhysicalAdditiveInput D R B where
  data := P.data
  fineSquareHalf := fun k =>
    Q'.le_trans' _ _ _ (P.modeOneHalf k) (P.data.coarseLeFinePower k)

/-- Hence the reduced input reaches the genuine `BlockingStep.Phi` defect
identity. -/
theorem DyadicP2PhysicalSandwichInput.blockDefectPowerOnTrajectory
    {D : DyadicP2CoeffTailData} {R : DyadicP2RefinedCutoffData D}
    {B : BlockingStep (fusionSeparator D.toControlFamily modeOne)}
    (P : DyadicP2PhysicalSandwichInput D R B) :
    IsBlockDefectPowerOnTrajectory 1
      (fusionSeparator D.toControlFamily modeOne) B.Φ
      P.data.toCrossMul.factor :=
  P.toAdditiveInput.blockDefectPowerOnTrajectory

/-- The same reduced input carries the positive rational product floor. -/
def DyadicP2PhysicalSandwichInput.factorProductFloorRat
    {D : DyadicP2CoeffTailData} {R : DyadicP2RefinedCutoffData D}
    {B : BlockingStep (fusionSeparator D.toControlFamily modeOne)}
    (P : DyadicP2PhysicalSandwichInput D R B) :
    Σ' (eps : Q'), (0 : Q') < eps ∧ forall n,
      eps <= RGGapPersistence.prodPrefix P.data.toCrossMul.factor n :=
  P.toAdditiveInput.factorProductFloorRat

end YMGap.Continuum.P2DyadicFusionHalfFloor

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2DyadicFusionHalfFloor.physicalModeOne_deficit_le_half
#print axioms YMGap.Continuum.P2DyadicFusionHalfFloor.half_le_physicalModeOne
#print axioms YMGap.Continuum.P2DyadicFusionHalfFloor.base_modeOne_half
#print axioms YMGap.Continuum.P2DyadicFusionHalfFloor.DyadicP2PhysicalSandwichInput.toAdditiveInput
#print axioms YMGap.Continuum.P2DyadicFusionHalfFloor.DyadicP2PhysicalSandwichInput.blockDefectPowerOnTrajectory
#print axioms YMGap.Continuum.P2DyadicFusionHalfFloor.DyadicP2PhysicalSandwichInput.factorProductFloorRat
