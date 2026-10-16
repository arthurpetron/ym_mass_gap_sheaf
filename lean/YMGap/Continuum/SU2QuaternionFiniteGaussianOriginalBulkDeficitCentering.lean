/-
# Exact OWN-centering of the bounded bulk plaquette deficit

The weighted fundamental plaquette deficit is the literal bounded ORIGINAL
observable

  2 * (sum of coefficients) - (weighted fundamental characters).

Its finite OWN mean is the same affine transform of the weighted-character
mean.  After subtracting those actual finite means, the deficit is exactly
the negative of the weighted-character source.  The two signs therefore
cancel in every finite centered two-time pair, and the corresponding existing
ORIGINAL centered time moments are constructively equivalent.

This is an exact same-action, same-partition identity.  It does not compare
the ORIGINAL law with the FREE Gaussian law, identify homogeneous Cayley
coefficients with bounded moments, remove a cutoff, or prove a continuum or
Clay mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkBoundedSource

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCentering

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleFunctionalLaws
  (middleRatio_one middleRatio_add middleRatio_smul)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws (windowRatio_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMovingCenterLagDifference (centeredPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOwnCenterLimit
  (expressionOwnMean expressionOwn_centeredPair_converges)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy (originalJointLimit)
open YMGap.Continuum.BF4WilsonAllNomeZeroRadiusIncrement (state)
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments (centeredTimeMoment)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule (spatialSpan)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted)
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkBoundedSource
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_smul lift_coeff)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap_mul_left)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

private theorem neg_eq_negOne_mul (value : Q') :
    (-value) ≈ (-1 : Q') * value := by
  exact poly_identity_of_normal_eq
    (.neg (.var 0)) (.mul (.const (-1)) (.var 0))
    (by decide) (fun _ => value)

private theorem neg_affine (constant center : Q') :
    (-(constant + (-center))) ≈ (-constant) + center := by
  exact poly_identity_of_normal_eq
    (.neg (.add (.var 0) (.neg (.var 1))))
    (.add (.neg (.var 0)) (.var 1))
    (by decide) (fun | 0 => constant | _ => center)

private theorem smul_neg (polynomial : RatPoly) :
    RatPolyCoeffEqv (polySmul (-1) polynomial) (polyNeg polynomial) :=
  (cap_mul_left (-1) polynomial).symm.trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
      (by decide) (fun _ => polynomial))

/-- Total coefficient multiplying the fundamental-character constant `2`. -/
def originalBulkCoefficientSum (s : Nat) (hs : 0 < s) : Q' :=
  listQSum (bulkSourceCoefficient s hs) (bulkSourceFaces s)

/-- The exact weighted bounded plaquette deficit `sum c_p (2 - chi_1(U_p))`. -/
def originalBulkDeficitExpression (s : Nat) (hs : 0 < s) :
    WindowExpression (s * s) :=
  .add
    (.smul (2 * originalBulkCoefficientSum s hs) .one)
    (.smul (-1) (originalBulkExpression s hs))

theorem originalBulkDeficitExpression_within (s : Nat) (hs : 0 < s) :
    Within 0 (originalBulkDeficitExpression s hs) :=
  ⟨True.intro, originalBulkExpression_within s hs⟩

/-- The deficit source is the exact affine transform of the already pinned
weighted fundamental-character span. -/
theorem originalBulkDeficitExpression_source_pin (s : Nat) (hs : 0 < s) :
    RatPolyCoeffEqv
      (sourcePolynomial (originalBulkDeficitExpression s hs))
      (polyAdd
        (polySmul (2 * originalBulkCoefficientSum s hs) polyOne)
        (polySmul (-1)
          (spatialSpan (s * s) (bulkSourceCoefficient s hs) (bulkSourceFaces s)))) := by
  exact (RatPolyCoeffEqv.refl _).add
    ((originalBulkExpression_source_pin s hs).smul (-1))

/-- Actual finite odd-window mean of the exact bounded deficit. -/
def originalBulkDeficitOwnMean {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n : Nat) : Q' :=
  expressionOwnMean hw0 hw1 (originalBulkDeficitExpression s hs) stage n

/-- The actual finite deficit mean is constant minus the actual finite
weighted-character mean, with the SAME action and partition. -/
theorem originalBulkDeficitOwnMean_affine_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n : Nat) :
    originalBulkDeficitOwnMean hw0 hw1 s hs stage n ≈
      2 * originalBulkCoefficientSum s hs +
        -(originalBulkOwnMean hw0 hw1 s hs stage n) := by
  unfold originalBulkDeficitOwnMean originalBulkOwnMean expressionOwnMean
  change middleRatio hw0 hw1 (headCutoff w + stage) (s * s) (Nat.le_add_right _ _)
      (n + 1) n
      (polyAdd
        (polySmul (2 * originalBulkCoefficientSum s hs) polyOne)
        (polySmul (-1) (sourcePolynomial (originalBulkExpression s hs)))) ≈ _
  refine Q'.eqv_trans _ _ _
    (middleRatio_add hw0 hw1 _ _ _ _ _ _ _) ?_
  apply Q'.add_eqv_congr'
  · refine Q'.eqv_trans _ _ _
      (middleRatio_smul hw0 hw1 _ _ _ _ _ _ _) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (middleRatio_one hw0 hw1 _ _ _ _ _)) ?_
    exact Q'.mul_one_eqv _
  · refine Q'.eqv_trans _ _ _
      (middleRatio_smul hw0 hw1 _ _ _ _ _ _ _) ?_
    exact Q'.eqv_symm (neg_eq_negOne_mul _)

private theorem shifted_affine_neg
    (constant center transformedCenter : Q') (polynomial : RatPoly)
    (hcenter : transformedCenter ≈ constant + (-center)) :
    RatPolyCoeffEqv
      (shifted
        (polyAdd (polySmul constant polyOne) (polySmul (-1) polynomial))
        transformedCenter)
      (polySmul (-1) (shifted polynomial center)) := by
  let constantPolynomial := polySmul constant polyOne
  let centerPolynomial := polySmul center polyOne
  have hnegCenter : (-transformedCenter) ≈ (-constant) + center :=
    Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ hcenter)
      (neg_affine constant center)
  have hnegConstant :
      RatPolyCoeffEqv (polySmul (-constant) polyOne)
        (polySmul (-1) constantPolynomial) :=
    (RatPolyCoeffEqv.smul_coefficient (neg_eq_negOne_mul constant) polyOne).trans
      (RatPolyCoeffEqv.smul_assoc (-1) constant polyOne).symm
  have hnegCenterPolynomial :
      RatPolyCoeffEqv (polySmul (-center) polyOne)
        (polySmul (-1) centerPolynomial) :=
    (RatPolyCoeffEqv.smul_coefficient (neg_eq_negOne_mul center) polyOne).trans
      (RatPolyCoeffEqv.smul_assoc (-1) center polyOne).symm
  have hconstantPart :
      RatPolyCoeffEqv (polySmul (-transformedCenter) polyOne)
        (polyAdd (polySmul (-1) constantPolynomial) centerPolynomial) :=
    (RatPolyCoeffEqv.smul_coefficient hnegCenter polyOne).trans
      ((RatPolyCoeffEqv.add_smul_same (-constant) center polyOne).symm.trans
        (hnegConstant.add (RatPolyCoeffEqv.refl _)))
  have hleft :
      RatPolyCoeffEqv
        (shifted
          (polyAdd constantPolynomial (polySmul (-1) polynomial))
          transformedCenter)
        (polyAdd
          (polyAdd constantPolynomial (polySmul (-1) polynomial))
          (polyAdd (polySmul (-1) constantPolynomial) centerPolynomial)) := by
    unfold shifted
    exact (RatPolyCoeffEqv.one_smul _).add hconstantPart
  have hright :
      RatPolyCoeffEqv (polySmul (-1) (shifted polynomial center))
        (polySmul (-1)
          (polyAdd polynomial (polySmul (-1) centerPolynomial))) := by
    unfold shifted
    exact ((RatPolyCoeffEqv.one_smul polynomial).add hnegCenterPolynomial).smul (-1)
  have hleftNeg :
      RatPolyCoeffEqv
        (shifted
          (polyAdd constantPolynomial (polySmul (-1) polynomial))
          transformedCenter)
        (polyAdd
          (polyAdd constantPolynomial (polyNeg polynomial))
          (polyAdd (polyNeg constantPolynomial) centerPolynomial)) :=
    hleft.trans
      (((RatPolyCoeffEqv.refl constantPolynomial).add (smul_neg polynomial)).add
        ((smul_neg constantPolynomial).add (RatPolyCoeffEqv.refl centerPolynomial)))
  have hrightNeg :
      RatPolyCoeffEqv (polySmul (-1) (shifted polynomial center))
        (polyNeg (polyAdd polynomial (polyNeg centerPolynomial))) :=
    hright.trans
      ((((RatPolyCoeffEqv.refl polynomial).add (smul_neg centerPolynomial)).smul (-1)).trans
        (smul_neg (polyAdd polynomial (polyNeg centerPolynomial))))
  have hcancel :
      RatPolyCoeffEqv
        (polyAdd
          (polyAdd constantPolynomial (polyNeg polynomial))
          (polyAdd (polyNeg constantPolynomial) centerPolynomial))
        (polyNeg (polyAdd polynomial (polyNeg centerPolynomial))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add
        (.add (.var 0) (.neg (.var 1)))
        (.add (.neg (.var 0)) (.var 2)))
      (.neg (.add (.var 1) (.neg (.var 2))))
      (by decide)
      (fun | 0 => constantPolynomial | 1 => polynomial | _ => centerPolynomial)
  exact hleftNeg.trans (hcancel.trans hrightNeg.symm)

/-- After their actual finite OWN means are removed, the exact deficit source
is coefficientwise the negative of the weighted-character source. -/
theorem originalBulkDeficitOwn_shifted_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n : Nat) :
    RatPolyCoeffEqv
      (shifted (sourcePolynomial (originalBulkDeficitExpression s hs))
        (originalBulkDeficitOwnMean hw0 hw1 s hs stage n))
      (polySmul (-1)
        (shifted (sourcePolynomial (originalBulkExpression s hs))
          (originalBulkOwnMean hw0 hw1 s hs stage n))) := by
  exact shifted_affine_neg
    (2 * originalBulkCoefficientSum s hs)
    (originalBulkOwnMean hw0 hw1 s hs stage n)
    (originalBulkDeficitOwnMean hw0 hw1 s hs stage n)
    (sourcePolynomial (originalBulkExpression s hs))
    (originalBulkDeficitOwnMean_affine_pin hw0 hw1 s hs stage n)

private theorem centeredPair_shifted_neg {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n L : Nat)
    {left right : RatPoly} {leftCenter rightCenter : Q'}
    (hshift : RatPolyCoeffEqv (shifted left leftCenter)
      (polySmul (-1) (shifted right rightCenter))) :
    centeredPair hw0 hw1 K width hK n L left leftCenter ≈
      centeredPair hw0 hw1 K width hK n L right rightCenter := by
  let rightShifted := shifted right rightCenter
  have hproduct := hshift.mul (lift_coeff (L * N width) hshift)
  simp only [lift_smul] at hproduct
  have hproductNeg : RatPolyCoeffEqv
      (polyMul (polySmul (-1) rightShifted)
        (polySmul (-1) (liftBoundary (L * N width) rightShifted)))
      (polyMul (polyNeg rightShifted)
        (polyNeg (liftBoundary (L * N width) rightShifted))) :=
    (smul_neg rightShifted).mul (smul_neg _)
  have hcancel : RatPolyCoeffEqv
      (polyMul (polyNeg rightShifted)
        (polyNeg (liftBoundary (L * N width) rightShifted)))
      (polyMul rightShifted (liftBoundary (L * N width) rightShifted)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.neg (.var 0)) (.neg (.var 1)))
      (.mul (.var 0) (.var 1))
      (by decide)
      (fun | 0 => rightShifted | _ => liftBoundary (L * N width) rightShifted)
  unfold centeredPair
  exact windowRatio_congr hw0 hw1 _ _ _ _ _ _
    (hproduct.trans (hproductNeg.trans hcancel))

/-- The two affine signs cancel at every finite stage and lag. -/
theorem originalBulkDeficitOwn_centeredPair_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    centeredPair hw0 hw1 (headCutoff w + stage) (s * s) (Nat.le_add_right _ _)
        n L (sourcePolynomial (originalBulkDeficitExpression s hs))
        (originalBulkDeficitOwnMean hw0 hw1 s hs stage n) ≈
      centeredPair hw0 hw1 (headCutoff w + stage) (s * s) (Nat.le_add_right _ _)
        n L (sourcePolynomial (originalBulkExpression s hs))
        (originalBulkOwnMean hw0 hw1 s hs stage n) := by
  exact centeredPair_shifted_neg hw0 hw1 _ _ _ _ _
    (originalBulkDeficitOwn_shifted_pin hw0 hw1 s hs stage n)

/-- The exact bounded deficit has its own generic SAME-ORIGINAL centered limit. -/
theorem originalBulkDeficitOwn_centeredPair_converges {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (L : Nat) :
    ConvergesTo (fun k => ofQ'
      (centeredPair hw0 hw1 (headCutoff w + k) (s * s) (Nat.le_add_right _ _)
        k L (sourcePolynomial (originalBulkDeficitExpression s hs))
        (originalBulkDeficitOwnMean hw0 hw1 s hs k k)))
      (centeredTimeMoment hw0 hw1 L
        (state (originalBulkDeficitExpression s hs)
          (originalBulkDeficitExpression_within s hs))
        (state (originalBulkDeficitExpression s hs)
          (originalBulkDeficitExpression_within s hs))) := by
  simpa only [originalBulkDeficitOwnMean] using
    expressionOwn_centeredPair_converges hw0 hw1
      (originalBulkDeficitExpression s hs)
      (originalBulkDeficitExpression_within s hs) L

/-- The exact physical deficit and compiled weighted-character source have
the same existing SAME-ORIGINAL centered time moment at every lag. -/
theorem originalBulkDeficit_centeredTimeMoment_equiv {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (L : Nat) :
    CReal.Equiv
      (centeredTimeMoment hw0 hw1 L
        (state (originalBulkDeficitExpression s hs)
          (originalBulkDeficitExpression_within s hs))
        (state (originalBulkDeficitExpression s hs)
          (originalBulkDeficitExpression_within s hs)))
      (centeredTimeMoment hw0 hw1 L
        (state (originalBulkExpression s hs) (originalBulkExpression_within s hs))
        (state (originalBulkExpression s hs) (originalBulkExpression_within s hs))) := by
  exact CReal.Equiv_of_limit_of_equal
    (fun k => YMGap.Constructive.TrigAdd.equiv_ofQ'_of_eqv
      (originalBulkDeficitOwn_centeredPair_pin hw0 hw1 s hs k k L))
    (originalBulkDeficitOwn_centeredPair_converges hw0 hw1 s hs L)
    (originalBulkOwn_centeredPair_converges hw0 hw1 s hs L)

#print axioms originalBulkDeficitExpression_source_pin
#print axioms originalBulkDeficitOwnMean_affine_pin
#print axioms originalBulkDeficitOwn_shifted_pin
#print axioms originalBulkDeficitOwn_centeredPair_pin
#print axioms originalBulkDeficitOwn_centeredPair_converges
#print axioms originalBulkDeficit_centeredTimeMoment_equiv

end YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCentering
