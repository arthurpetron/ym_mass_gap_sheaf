/-
# Same-carrier heat transmission at any two distinct link blocks

The exposing swaps act on the whole original integrand. Support guards
exclude truncation, and block degree zero is required only in the replaced
link. No independence among the other variables is assumed.
-/

import YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry

namespace YMGap.Continuum.SU2QuaternionSelectedPairHeatTransmission

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionFourBlockSelection
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionRelativeHeatInsertion
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry

local infix:50 " ≈ " => Q'.eqv

/-- All packet spins, arbitrary distinct original links, arbitrary other
variables, and exactly the same full Haar carrier on both sides. -/
theorem coordinate_transmission (tailBlocks : Nat) (hb : 0 < tailBlocks)
    (a b : Fin (tailBlocks+1)) (hab : a.val ≠ b.val)
    (w : Q') (K : Nat) (hK : 1 ≤ K) (i : Fin 4) (r : RatPoly)
    (hr : SupportedQuaternionBlocks (tailBlocks+1) r)
    (hd : HasQuaternionBlockDegree a.val 0 r) :
    quaternionHaar (tailBlocks+1) (polyMul
      (polyMul (heatAt a.val b.val w K) (polyVar (4*a.val+i.val))) r) ≈
      qpow w 3 * quaternionHaar (tailBlocks+1) (polyMul (polyVar (4*b.val+i.val)) r) := by
  let steps := pairSteps (show 1 < tailBlocks+1 by omega) a b
  let tr := applyQuaternionBlockSwapChain steps r
  have htr : SupportedQuaternionBlocks (tailBlocks+1) tr := applyQuaternionBlockSwapChain_supported steps r hr
  have hk := heat_supported a.isLt b.isLt w K
  have ha := coordinate_supported a.isLt i
  have hv := coordinate_supported b.isLt i
  have hz := coordinate_supported (show 0 < tailBlocks+1 by omega) i
  have ho := coordinate_supported (show 1 < tailBlocks+1 by omega) i
  have hkh := heat_supported (show 0 < tailBlocks+1 by omega) (show 1 < tailBlocks+1 by omega) w K
  have hd0 : HasQuaternionBlockDegree 0 0 tr := by
    apply chain_degree steps (by omega)
    rw [pair_zero (by omega) a b hab]
    exact hd
  have hindependent : HeadQuaternionIndependent tr := hd0
  have hleft := quaternionHaar_applyQuaternionBlockSwapChain steps _ (supported_polyMul (supported_polyMul hk ha) hr)
  rw [chain_mul, chain_mul] at hleft
  have hpin := ((heat_exposed (by omega) a b hab w K).mul
    (PaddedPolynomialCoeffEqv.of_prefix (coordinate_exposed steps (by omega) (pair_zero (by omega) a b hab) i))).mul
      (PaddedPolynomialCoeffEqv.refl (tailBlocks+1) tr)
  have hleftPin := hpin.haar
    (supported_polyMul (supported_polyMul (applyQuaternionBlockSwapChain_supported steps _ hk)
      (applyQuaternionBlockSwapChain_supported steps _ ha)) htr)
    (supported_polyMul (supported_polyMul hkh hz) htr)
  have hright := quaternionHaar_applyQuaternionBlockSwapChain steps _ (supported_polyMul hv hr)
  rw [chain_mul] at hright
  have hrightPin := quaternionHaar_prefixPolynomialEqv (tailBlocks+1)
    ((coordinate_exposed steps (by omega) (pair_one (by omega) a b) i).mul
      (QuaternionPrefixPolynomialEqv.refl (tailBlocks+1) tr))
    (supported_polyMul (applyQuaternionBlockSwapChain_supported steps _ hv) htr)
    (supported_polyMul ho htr)
  simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one] at hleftPin hrightPin
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hleft)
    (Q'.eqv_trans _ _ _ hleftPin
      (Q'.eqv_trans _ _ _ (coordinate_transmission_same_carrier tailBlocks hb w K hK i tr hindependent)
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ (Q'.eqv_symm hrightPin) hright))))

end YMGap.Continuum.SU2QuaternionSelectedPairHeatTransmission

#print axioms YMGap.Continuum.SU2QuaternionSelectedPairHeatTransmission.coordinate_transmission
