/-
# Source-increment invariance under a constant observable shift

Both copies of a constant have the same value on the padded two-slice Haar
carrier. Thus the source/observable jump square keeps its exact value when
the observable is centered. The source and product heat remain unchanged.
-/

import YMGap.Continuum.SU2QuaternionProductHeatSourceYoung
import YMGap.Continuum.QuaternionHaarDensityVariance

namespace YMGap.Continuum.SU2QuaternionProductHeatSourceCentering

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_add lift_smul lift_one)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productHeat productHeat_supported)
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy (jump jump_supported)
open YMGap.Continuum.SU2QuaternionProductHeatSourceYoung (sourceIncrementCost)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted shifted_supported)
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz (weightedPair)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)

local infix:50 " ≈ " => Q'.eqv

private theorem padded_neg {blocks : Nat} {p q : RatPoly}
    (h : PaddedPolynomialCoeffEqv blocks p q) :
    PaddedPolynomialCoeffEqv blocks (polyNeg p) (polyNeg q) :=
  (PaddedPolynomialCoeffEqv.of_coeff
      (YMGap.Continuum.QuaternionHaarAngularCarrier.neg_smul p)).trans
    ((h.smul (-1)).trans (PaddedPolynomialCoeffEqv.of_coeff
      (YMGap.Continuum.QuaternionHaarAngularCarrier.neg_smul q).symm))

/-- A rational shift cancels between the two copies, including the padded
upper copy of one. No heat or source premise is needed. -/
theorem jump_shifted (n : Nat) (f : RatPoly) (c : Q') :
    PaddedPolynomialCoeffEqv (n+n) (jump n (shifted f c)) (jump n f) := by
  have hu : PaddedPolynomialCoeffEqv (n+n)
      (liftBoundary n (shifted f c)) (shifted (liftBoundary n f) c) := by
    unfold shifted
    rw [lift_add, lift_smul, lift_smul]
    exact ((PaddedPolynomialCoeffEqv.refl _ _).smul 1).add
      ((lift_one (n+n) n).smul (-c))
  have hfirst : PaddedPolynomialCoeffEqv (n+n)
      (jump n (shifted f c))
      (polyAdd (shifted f c) (polyNeg (shifted (liftBoundary n f) c))) := by
    unfold jump
    exact (PaddedPolynomialCoeffEqv.refl _ _).add (padded_neg hu)
  let k := polySmul (-c) polyOne
  have hl : RatPolyCoeffEqv (shifted f c) (polyAdd f k) :=
    (RatPolyCoeffEqv.one_smul f).add (RatPolyCoeffEqv.refl k)
  have hr : RatPolyCoeffEqv (shifted (liftBoundary n f) c)
      (polyAdd (liftBoundary n f) k) :=
    (RatPolyCoeffEqv.one_smul (liftBoundary n f)).add (RatPolyCoeffEqv.refl k)
  have hcancel : RatPolyCoeffEqv
      (polyAdd (polyAdd f k) (polyNeg (polyAdd (liftBoundary n f) k)))
      (jump n f) := by
    unfold jump
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.var 2)) (.neg (.add (.var 1) (.var 2))))
      (.add (.var 0) (.neg (.var 1)))
      (by decide) (fun | 0 => f | 1 => liftBoundary n f | _ => k)
  exact hfirst.trans (PaddedPolynomialCoeffEqv.of_coeff
    (((hl.add (YMGap.Continuum.QuaternionHaarAngularCarrier.neg_smul
      (shifted (liftBoundary n f) c))).trans
      ((RatPolyCoeffEqv.refl _).add (hr.smul (-1)))).trans
      (((RatPolyCoeffEqv.refl _).add
        (YMGap.Continuum.QuaternionHaarAngularCarrier.neg_smul
          (polyAdd (liftBoundary n f) k)).symm).trans hcancel)))

/-- The same exact source-increment cost survives rational centering of the
observable. The original product heat and source are retained. -/
theorem sourceIncrementCost_shifted (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n)
    {q f : RatPoly} (hq : SupportedQuaternionBlocks n q)
    (hf : SupportedQuaternionBlocks n f) (c : Q') :
    sourceIncrementCost n w K ids q (shifted f c) ≈
      sourceIncrementCost n w K ids q f := by
  let W := productHeat n w K ids
  let a := polyMul (jump n q) (jump n (shifted f c))
  let b := polyMul (jump n q) (jump n f)
  have hs := shifted_supported hf c
  have ha : SupportedQuaternionBlocks (n+n) a :=
    supported_polyMul (jump_supported hq) (jump_supported hs)
  have hb : SupportedQuaternionBlocks (n+n) b :=
    supported_polyMul (jump_supported hq) (jump_supported hf)
  have hW := productHeat_supported n w K ids hids
  have hpair : PaddedPolynomialCoeffEqv (n+n) a b :=
    (PaddedPolynomialCoeffEqv.refl _ _).mul (jump_shifted n f c)
  have hboth : PaddedPolynomialCoeffEqv (n+n) (polyMul a a) (polyMul b b) :=
    hpair.mul hpair
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff (RatPolyCoeffEqv.mul_comm (polyMul a a) W))
    (Q'.eqv_trans _ _ _
      (hboth.haar_insert (supported_polyMul ha ha) (supported_polyMul hb hb) W hW)
      (haar_of_coeff (RatPolyCoeffEqv.mul_comm W (polyMul b b))))

#print axioms jump_shifted
#print axioms sourceIncrementCost_shifted

end YMGap.Continuum.SU2QuaternionProductHeatSourceCentering
