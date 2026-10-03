/-
# Division-free three-column Gram ceiling for the ORIGINAL last step

The actual positive step constructs M*Gram-J as the Gram determinant of
(a,c,1). Multiplication by the SAME M=T1 gives M^2*Gram-scoreBudget.
Both signed inputs are arbitrary; no source, conditional mass or variance
is inverted. Every output weight and reciprocal square remains inside Haar.
This is an alternative LARGER upper budget, not an improvement of the
original paired budget. A useful SAME surviving-norm/scaling bound is open.
-/

import YMGap.Continuum.SU2QuaternionMultiHeadThreeGram
import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRegression
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferOrder

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepThreeGramBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep transferStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepScoreVariance
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRegression
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition (partialHaarHeads_congr)
open YMGap.Continuum.SU2QuaternionMultiHeadThreeGram
open YMGap.Continuum.SU2QuaternionAngularDerivative (angularDerivative)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (sumBound)
open YMGap.Continuum.QuaternionHaarConditionalScoreGradient
  (conditionalScore reciprocalScoreCorrection)
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse (reciprocal reciprocal_supported)
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
  (relativeCutoff relativeCap headCutoff_le_relativeCutoff)

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight kineticWeight

/-- The signed two-input Gram retains its cross term and the SAME mass squared. -/
def lastStepThreeGramBudget (w : Q') (K width : Nat) (a c : RatPoly) : RatPoly :=
  let M := transferStep w K width polyOne
  polyMul (polyMul M M) (lastStepRegressionGram w K width a c)

private theorem support_mono {small large : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks small p) (h : small ≤ large) :
    SupportedQuaternionBlocks large p :=
  fun term ht => Nat.le_trans (hp term ht) (Nat.mul_le_mul_left 4 h)

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    Q'.eqv (quaternionHaar blocks (polyNeg p)) (-(quaternionHaar blocks p))
  | [] => by change Q'.eqv (0 : Q') (-0); decide
  | t::rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1))
        (haar_neg blocks rest))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

/-- An actual certificate for the budget difference, from the three-copy
producer. Neither signed input is required to be positive. -/
def lastStepThreeGramBudget_certificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) {a c : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a)
    (hc : SupportedQuaternionBlocks (N width) c) :
    Certificate (N width) (polyAdd (lastStepThreeGramBudget w K width a c)
      (polyNeg (lastStepScoreBudget w K width a c))) := by
  let W := stepWeight w K width
  have hW : SupportedQuaternionBlocks (N width+N width) W :=
    supported_polyMul (kineticWeight_supported w K width)
      (support_mono (spatialWeight_supported w K width) (by omega))
  have P := conditionalThreeGram_certificate (N width) (N width) W a c hW
    (support_mono ha (by omega)) (support_mono hc (by omega))
    (stepWeightCertificate hw0 hw1 K width hK)
  have pin (p : RatPoly) : RatPolyCoeffEqv
      (partialHaarHeads (N width) (polyMul W p)) (transferStep w K width p) :=
    (transferStep_kernelMap w K width p).symm
  have hM : RatPolyCoeffEqv (partialHaarHeads (N width) W)
      (transferStep w K width polyOne) :=
    (partialHaarHeads_congr (N width) (RatPolyCoeffEqv.mul_one W).symm).trans (pin polyOne)
  let A := transferStep w K width a
  let b := transferStep w K width c
  let U := transferStep w K width (polyMul a a)
  let H := transferStep w K width (polyMul c c)
  let C := transferStep w K width (polyMul a c)
  let M := transferStep w K width polyOne
  let D := polyAdd
    (polyAdd (polyMul (polyMul M U) H)
      (polyAdd (polyMul (polyMul A b) C) (polyMul (polyMul A b) C)))
    (polyNeg (polyAdd (polyAdd (polyMul (polyMul A A) H) (polyMul U (polyMul b b)))
      (polyMul M (polyMul C C))))
  have hD : RatPolyCoeffEqv (threeGramDifference (N width) W a c) D :=
    (threeGramDifference_expansion (N width) W a c).trans
      (RatPolyCoeffEqv.add
        (RatPolyCoeffEqv.add
          ((hM.mul (pin (polyMul a a))).mul (pin (polyMul c c)))
          (RatPolyCoeffEqv.add
            (((pin a).mul (pin c)).mul (pin (polyMul a c)))
            (((pin a).mul (pin c)).mul (pin (polyMul a c)))))
        (RatPolyCoeffEqv.neg
          (RatPolyCoeffEqv.add
            (RatPolyCoeffEqv.add
              (((pin a).mul (pin a)).mul (pin (polyMul c c)))
              ((pin (polyMul a a)).mul ((pin c).mul (pin c))))
            (hM.mul ((pin (polyMul a c)).mul (pin (polyMul a c)))))))
  have PD : Certificate (N width) D := Certificate.ofCoeff hD.symm P
  have PM := transferStep_certificate hw0 hw1 K width hK
    (supported_one (N width)) (Certificate.one (N width))
  have hJ := (lastStepPairedResidual_square_pin w K width a c).mul_left M
  have hid : RatPolyCoeffEqv
      (polyAdd (lastStepThreeGramBudget w K width a c)
        (polyNeg (lastStepScoreBudget w K width a c))) (polyMul M D) := by
    refine ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg hJ)).trans ?_
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.mul (.var 5) (.var 5))
          (.add (.mul (.var 2) (.var 4)) (.neg (.mul (.var 3) (.var 3)))))
        (.neg (.mul (.var 5)
          (.add (.mul (.mul (.var 0) (.var 0)) (.var 4))
            (.add (.neg (.add (.mul (.mul (.var 0) (.var 1)) (.var 3))
              (.mul (.mul (.var 0) (.var 1)) (.var 3))))
              (.mul (.mul (.var 1) (.var 1)) (.var 2)))))))
      (.mul (.var 5)
        (.add (.add (.mul (.mul (.var 5) (.var 2)) (.var 4))
            (.add (.mul (.mul (.var 0) (.var 1)) (.var 3))
              (.mul (.mul (.var 0) (.var 1)) (.var 3))))
          (.neg (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 4))
              (.mul (.var 2) (.mul (.var 1) (.var 1))))
            (.mul (.var 5) (.mul (.var 3) (.var 3)))))))
      (by decide) (fun | 0 => A | 1 => b | 2 => U | 3 => C | 4 => H | _ => M)
  exact Certificate.ofCoeff hid (PM.mul PD)

/-- Every certified SAME output weight and arbitrary square multiplier
preserves the bound, including zero masses and signed input sources. -/
theorem lastStep_threeGram_weighted_multiplier_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) {a c R G : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a)
    (hc : SupportedQuaternionBlocks (N width) c)
    (PR : Certificate (N width) R) (hG : SupportedQuaternionBlocks (N width) G) :
    quaternionHaar (N width) (polyMul (polyMul R (polyMul G G))
      (lastStepScoreBudget w K width a c)) ≤
    quaternionHaar (N width) (polyMul (polyMul R (polyMul G G))
      (lastStepThreeGramBudget w K width a c)) := by
  let F := polyMul R (polyMul G G)
  let old := lastStepScoreBudget w K width a c
  let new := lastStepThreeGramBudget w K width a c
  have hn := (((PR.mul (Certificate.square G hG)).mul
    (lastStepThreeGramBudget_certificate hw0 hw1 K width hK ha hc))).haar_nonnegative
  have hid : RatPolyCoeffEqv (polyMul F (polyAdd new (polyNeg old)))
      (polyAdd (polyMul F new) (polyNeg (polyMul F old))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
      (by decide) (fun | 0 => F | 1 => new | _ => old)
  have he := Q'.eqv_trans _ _ _ (haar_of_coeff hid)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append (N width) _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (haar_neg (N width) _)))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hn (Q'.le_of_eqv he))

/-- Actual angular score, with the Gram alternative and full output weight. -/
theorem lastStep_score_threeGram_weighted_multiplier_square_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (s : Nat) (hs : s ∈ activeBlocks width)
    {i j : Nat} (hi : i < 4) (hj : j < 4) {a c R G : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a) (hc : SupportedQuaternionBlocks (N width) c)
    (PR : Certificate (N width) R) (hG : SupportedQuaternionBlocks (N width) G) :
    let S := conditionalScore (4*s+i) (4*s+j) (transferStep w K width a) (transferStep w K width c)
    quaternionHaar (N width) (polyMul R (polyMul (polyMul G S) (polyMul G S))) ≤
      (relativeCap w 32*relativeCap w 32)*quaternionHaar (N width)
        (polyMul (polyMul R (polyMul G G)) (lastStepThreeGramBudget w K width a c)) := by
  dsimp only
  exact Q'.le_trans' _ _ _
    (lastStep_score_weighted_multiplier_square_le hw0 hw1 K width hK s hs hi hj ha hc PR hG)
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (lastStep_threeGram_weighted_multiplier_le hw0 hw1 K width
        (Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK) ha hc PR hG)
      (SumOfSquares.q_mul_self_nonneg _))

/-- Finite reciprocal derivative on the SAME output carrier; its exact
correction is unchanged and no reciprocal multiplier is discarded. -/
theorem lastStep_reciprocal_threeGram_gradient_square_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (s : Nat) (hs : s ∈ activeBlocks width)
    {i j : Nat} (hi : i < 4) (hj : j < 4) {a c R : RatPoly}
    (ha : SupportedQuaternionBlocks (N width) a) (hc : SupportedQuaternionBlocks (N width) c)
    (PR : Certificate (N width) R) (u : Q') (hu : (0 : Q') < u) (k : Nat) :
    let A := transferStep w K width a
    let b := transferStep w K width c
    let G := reciprocal A u hu k
    let d := polyMul A (angularDerivative (4*s+i) (4*s+j) (polyMul G b))
    let e := reciprocalScoreCorrection (4*s+i) (4*s+j) A b u hu k
    quaternionHaar (N width) (polyMul R (polyMul d d)) ≤
      sumBound
        ((relativeCap w 32*relativeCap w 32)*quaternionHaar (N width)
          (polyMul (polyMul R (polyMul G G)) (lastStepThreeGramBudget w K width a c)))
        (quaternionHaar (N width) (polyMul R (polyMul e e))) := by
  dsimp only
  have h := Q'.mul_le_mul_of_nonneg_left _ _ _
    (lastStep_threeGram_weighted_multiplier_le hw0 hw1 K width
      (Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK) ha hc PR
      (reciprocal_supported (transferStep_supported w K width ha) u hu k))
    (SumOfSquares.q_mul_self_nonneg (relativeCap w 32))
  exact Q'.le_trans' _ _ _
    (lastStep_reciprocal_gradient_square_le hw0 hw1 K width hK s hs hi hj ha hc PR u hu k)
    (Q'.add_le_add (Q'.add_le_add h h) (Q'.le_refl' _))

#print axioms lastStepThreeGramBudget
#print axioms lastStepThreeGramBudget_certificate
#print axioms lastStep_threeGram_weighted_multiplier_le
#print axioms lastStep_score_threeGram_weighted_multiplier_square_le
#print axioms lastStep_reciprocal_threeGram_gradient_square_le

end YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepThreeGramBound
