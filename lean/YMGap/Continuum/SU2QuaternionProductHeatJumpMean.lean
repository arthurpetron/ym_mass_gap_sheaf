/-
# Mean of the two-slice jump product under normalized product heat

These are exact finite Haar identities.  They do not bound the source
increment square or compare a raw source moment with an interacting variance.
-/

import YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy
import YMGap.Continuum.SU2QuaternionProductHeatConstant
import YMGap.Continuum.QPolyHaarPositiveSubstitution

namespace YMGap.Continuum.SU2QuaternionProductHeatJumpMean

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatConstant
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (edgeWeight)
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff supported_one)
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz (weightedPair)

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private theorem support_pair {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) :
    SupportedQuaternionBlocks (n+n) p :=
  fun t ht => Nat.le_trans (hp t ht) (Nat.mul_le_mul_left 4 (Nat.le_add_right _ _))

private theorem edgeWeight_one (n : Nat) (w : Q') (K : Nat) (ids : List Nat) :
    PaddedPolynomialCoeffEqv (n+n)
      (edgeWeight n w K ids polyOne) (productHeat n w K ids) := by
  unfold edgeWeight
  exact ((PaddedPolynomialCoeffEqv.refl _ (polyMul (productHeat n w K ids) polyOne)).mul
      (lift_one (n+n) n)).trans
    ((PaddedPolynomialCoeffEqv.of_coeff
      (RatPolyCoeffEqv.mul_one (polyMul (productHeat n w K ids) polyOne))).trans
      (PaddedPolynomialCoeffEqv.of_coeff
        (RatPolyCoeffEqv.mul_one (productHeat n w K ids))))

/-- The product heat has total mass one, with no nome or cutoff positivity
guard needed for this algebraic normalization. -/
theorem productHeat_mass_one (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n) :
    weightedPair (n+n) (productHeat n w K ids) polyOne polyOne ≈ 1 := by
  have hfirst : weightedPair (n+n) (productHeat n w K ids) polyOne polyOne ≈
      H (n+n) (polyMul (productHeat n w K ids) polyOne) := by
    unfold weightedPair
    exact haar_of_coeff
      (((RatPolyCoeffEqv.one_mul polyOne).mul_right
        (productHeat n w K ids)).trans
        ((RatPolyCoeffEqv.one_mul (productHeat n w K ids)).trans
          (RatPolyCoeffEqv.mul_one (productHeat n w K ids)).symm))
  exact Q'.eqv_trans _ _ _ hfirst
    (Q'.eqv_trans _ _ _
      (productHeat_lower_marginal n w K ids hnd hids polyOne (supported_one n))
      (YMGap.Continuum.QPolyHaarPositiveSubstitution.haar_one n))

/-- Mean of the product of two source/observable jumps.  The full source is
untouched and the only remaining one-slice moment is linear in that source. -/
theorem jump_mean (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    {q f : RatPoly} (hq : SupportedQuaternionBlocks n q)
    (hf : SupportedQuaternionBlocks n f) :
    weightedPair (n+n) (productHeat n w K ids)
        (polyMul (jump n q) (jump n f)) polyOne ≈
      (2 : Q') * (H n (polyMul q f) +
        -(H n (polyMul q (productMap n w K ids f)))) := by
  let r := polyMul (jump n q) (jump n f)
  have hr : SupportedQuaternionBlocks (n+n) r :=
    supported_polyMul (jump_supported hq) (jump_supported hf)
  have hweight := edgeWeight_one n w K ids
  have hW : SupportedQuaternionBlocks (n+n) (edgeWeight n w K ids polyOne) :=
    supported_polyMul
      (supported_polyMul (productHeat_supported n w K ids hids) (supported_one (n+n)))
      (lift_supported (supported_one n) n)
  have hK : SupportedQuaternionBlocks (n+n) (productHeat n w K ids) :=
    productHeat_supported n w K ids hids
  have hreplace : weightedPair (n+n) (productHeat n w K ids) r polyOne ≈
      weightedPair (n+n) (edgeWeight n w K ids polyOne) (jump n q) (jump n f) := by
    unfold weightedPair
    have hleft := haar_of_coeff (blocks := n+n) ((RatPolyCoeffEqv.mul_one r).mul_right
      (productHeat n w K ids))
    have hmid := (hweight.symm).haar_insert hK hW r hr
    exact Q'.eqv_trans _ _ _ hleft hmid
  have hfull := full_jump_pairing n w K ids hids
    (supported_one n) hq hf
  have hmoment : marginalPair n w K ids polyOne q f ≈ H n (polyMul q f) := by
    unfold marginalPair
    have hp := (productMap_one n w K ids hnd hids)
      (polyMul q f) (supported_polyMul hq hf)
    exact Q'.eqv_trans _ _ _
      (haar_of_coeff
        (((RatPolyCoeffEqv.one_mul (productMap n w K ids polyOne)).mul
          (RatPolyCoeffEqv.refl (polyMul q f))).trans
          (RatPolyCoeffEqv.mul_comm (productMap n w K ids polyOne) (polyMul q f))))
      (Q'.eqv_trans _ _ _ hp
        (haar_of_coeff (RatPolyCoeffEqv.mul_one (polyMul q f))))
  have hpair : H n (polyMul (polyMul polyOne q)
      (productMap n w K ids (polyMul polyOne f))) ≈
      H n (polyMul q (productMap n w K ids f)) :=
    haar_of_coeff ((RatPolyCoeffEqv.one_mul q).mul
      (productMap_congr n w K ids (RatPolyCoeffEqv.one_mul f)))
  exact Q'.eqv_trans _ _ _ hreplace
    (Q'.eqv_trans _ _ _ hfull
      (Q'.mul_eqv_congr_left 2 _ _
        (Q'.add_eqv_congr' hmoment (Q'.neg_eqv_congr _ _ hpair))))

end YMGap.Continuum.SU2QuaternionProductHeatJumpMean

#print axioms YMGap.Continuum.SU2QuaternionProductHeatJumpMean.productHeat_mass_one
#print axioms YMGap.Continuum.SU2QuaternionProductHeatJumpMean.jump_mean
