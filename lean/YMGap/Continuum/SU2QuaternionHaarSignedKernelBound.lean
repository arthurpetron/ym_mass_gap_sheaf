/-
# Ordinary-Haar bounds for a signed kernel difference

A certificate interval for W suffices to bound its actual partial-integration
map; W need not be positive. Square the interval, use ordinary Haar
Cauchy--Schwarz on W*f and the retained test, and cancel the output norm.
This supplies the norm estimate needed for cutoff differences of the original
transfer weights, without incorrectly treating their difference as positive.
-/

import YMGap.Continuum.SU2QuaternionHaarKernelBound

namespace YMGap.Continuum.SU2QuaternionHaarSignedKernelBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpoint
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarKernelBound
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap_mul_left)
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv

private theorem mul_congr {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem ordinary_pair (blocks : Nat) (p q : RatPoly) :
    weightedPair blocks polyOne p q ≈ quaternionHaar blocks (polyMul p q) :=
  haar_of_coeff (RatPolyCoeffEqv.mul_one _)

private theorem swap_kernel (blocks : Nat) (W f : RatPoly) :
    RatPolyCoeffEqv (kernelMap blocks W f) (kernelMap blocks f W) :=
  partialHaarHeads_congr blocks (RatPolyCoeffEqv.mul_comm W f)

private theorem smul_neg (p : RatPoly) : RatPolyCoeffEqv (polySmul (-1) p) (polyNeg p) :=
  (cap_mul_left (-1) p).symm.trans
    (coeffEvalExpr_eqv_of_normalize_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
      (by decide) (fun _ => p))

/-- The signed weight difference is exactly the difference of the original maps. -/
theorem kernelMap_weight_difference (blocks : Nat) (W Z f : RatPoly) :
    RatPolyCoeffEqv (kernelMap blocks (polyAdd W (polyNeg Z)) f)
      (polyAdd (kernelMap blocks W f) (polySmul (-1) (kernelMap blocks Z f))) :=
  (swap_kernel blocks _ f).trans
    ((kernelMap_congr blocks f ((RatPolyCoeffEqv.refl W).add (smul_neg Z).symm)).trans
      ((kernelMap_add blocks f W (polySmul (-1) Z)).trans
        ((swap_kernel blocks f W).add
          ((kernelMap_smul blocks f (-1) Z).trans ((swap_kernel blocks f Z).smul (-1))))))

/-- A signed interval gives the same bilinear cap, with no positivity premise on W. -/
theorem kernelMap_bilinear_bound {blocks : Nat} {W f g : RatPoly} {C : Q'}
    (IW : Interval (blocks+blocks) W C)
    (hf : SupportedQuaternionBlocks blocks f) (hg : SupportedQuaternionBlocks blocks g) :
    quaternionHaar blocks (polyMul (kernelMap blocks W f) g) *
        quaternionHaar blocks (polyMul (kernelMap blocks W f) g) ≤
      (C*C) * (quaternionHaar blocks (polyMul f f) * quaternionHaar blocks (polyMul g g)) := by
  have hf' : SupportedQuaternionBlocks (blocks+blocks) f :=
    fun t ht => Nat.le_trans (hf t ht) (Nat.mul_le_mul_left 4 (by omega))
  have hWf := supported_polyMul IW.support hf'
  have hg' := lift_supported hg blocks
  have hcs := weighted_cauchySchwarz (blocks+blocks) polyOne
    (polyMul W f) (liftBoundary blocks g) (Certificate.one _) hWf hg'
  have hp : weightedPair (blocks+blocks) polyOne (polyMul W f) (liftBoundary blocks g) ≈
      quaternionHaar blocks (polyMul (kernelMap blocks W f) g) :=
    Q'.eqv_trans _ _ _ (ordinary_pair _ _ _)
      (Q'.eqv_trans _ _ _ (haar_of_coeff
        ((RatPolyCoeffEqv.mul_assoc W f _).trans (RatPolyCoeffEqv.mul_comm W _)))
        (kernelMap_pairing blocks W f g))
  have hfirst : weightedPair (blocks+blocks) polyOne (polyMul W f) (polyMul W f) ≤
      (C*C) * quaternionHaar blocks (polyMul f f) := by
    have he : weightedPair (blocks+blocks) polyOne (polyMul W f) (polyMul W f) ≈
        quaternionHaar (blocks+blocks) (polyMul (polyMul f f) (polyMul W W)) :=
      Q'.eqv_trans _ _ _ (ordinary_pair _ _ _)
        (haar_of_coeff ((RatPolyCoeffEqv.mul_four_swap W f W f).trans
          (RatPolyCoeffEqv.mul_comm _ _)))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.le_trans' _ _ _ (Q'.le_abs_self _)
        (Q'.le_trans' _ _ _ ((IW.mul IW).weighted_haar_bound (.square f hf'))
          (Q'.le_of_eqv (Q'.mul_eqv_congr_left (C*C) _ _
            (quaternionHaar_extend_supported_endpoint (by omega) _ (supported_polyMul hf hf))))))
  have hsecond : weightedPair (blocks+blocks) polyOne
      (liftBoundary blocks g) (liftBoundary blocks g) ≈
      quaternionHaar blocks (polyMul g g) := by
    refine Q'.eqv_trans _ _ _ (ordinary_pair _ _ _) ?_
    rw [← lift_product]
    exact haar_liftBoundary blocks blocks (polyMul g g)
  have hupper_nonneg : (0 : Q') ≤ (C*C) * quaternionHaar blocks (polyMul f f) :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ IW.nonnegative IW.nonnegative)
      (Certificate.haar_nonnegative (.square f hf))
  have hsecond_nonneg : (0 : Q') ≤ weightedPair (blocks+blocks) polyOne
      (liftBoundary blocks g) (liftBoundary blocks g) :=
    (Certificate.one _).square_insertion_nonnegative _ hg'
  have hproduct := Q'.mul_le_mul_of_nonneg hfirst (Q'.le_of_eqv hsecond)
    hupper_nonneg hsecond_nonneg
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (mul_congr hp hp))
    (Q'.le_trans' _ _ _ hcs (Q'.le_trans' _ _ _ hproduct
      (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))))

/-- The actual signed-kernel map has squared norm at most C*C. -/
theorem kernelMap_square_bound {blocks : Nat} {W f : RatPoly} {C : Q'}
    (IW : Interval (blocks+blocks) W C) (hf : SupportedQuaternionBlocks blocks f) :
    quaternionHaar blocks
        (polyMul (kernelMap blocks W f) (kernelMap blocks W f)) ≤
      (C*C) * quaternionHaar blocks (polyMul f f) := by
  let A := quaternionHaar blocks (polyMul (kernelMap blocks W f) (kernelMap blocks W f))
  let F := quaternionHaar blocks (polyMul f f)
  have h := kernelMap_bilinear_bound IW hf (kernelMap_supported IW.support hf)
  change A*A ≤ (C*C)*(F*A) at h
  change A ≤ (C*C)*F
  by_cases hpos : (0 : Q') < A
  · have hreorder : (C*C)*(F*A) ≈ A*((C*C)*F) :=
      Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) (Q'.mul_comm_eqv _ _)
    exact Q'.le_of_mul_le_mul_left
      (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hreorder)) hpos
  · have hzero : A ≤ (0 : Q') := by
      change ¬ ((0 : Int) * (A.den : Int) < A.num * 1) at hpos
      have hn : A.num ≤ 0 := by simpa only [Int.zero_mul, Int.mul_one] using Int.not_lt.mp hpos
      change A.num * 1 ≤ (0 : Int) * (A.den : Int)
      simpa only [Int.zero_mul, Int.mul_one] using hn
    exact Q'.le_trans' _ _ _ hzero
      (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ IW.nonnegative IW.nonnegative)
        (Certificate.haar_nonnegative (.square f hf)))

/-- Squared-norm difference estimate for the SAME two kernel maps. -/
theorem kernelMap_difference_bound {blocks : Nat} {W Z f : RatPoly} {C : Q'}
    (I : Interval (blocks+blocks) (polyAdd W (polyNeg Z)) C)
    (hf : SupportedQuaternionBlocks blocks f) :
    quaternionHaar blocks (polyMul
      (polyAdd (kernelMap blocks W f) (polySmul (-1) (kernelMap blocks Z f)))
      (polyAdd (kernelMap blocks W f) (polySmul (-1) (kernelMap blocks Z f)))) ≤
      (C*C) * quaternionHaar blocks (polyMul f f) := by
  have he := kernelMap_weight_difference blocks W Z f
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (haar_of_coeff (he.mul he)))
    (kernelMap_square_bound I hf)

end YMGap.Continuum.SU2QuaternionHaarSignedKernelBound

#print axioms YMGap.Continuum.SU2QuaternionHaarSignedKernelBound.kernelMap_bilinear_bound
#print axioms YMGap.Continuum.SU2QuaternionHaarSignedKernelBound.kernelMap_square_bound
#print axioms YMGap.Continuum.SU2QuaternionHaarSignedKernelBound.kernelMap_weight_difference
#print axioms YMGap.Continuum.SU2QuaternionHaarSignedKernelBound.kernelMap_difference_bound
