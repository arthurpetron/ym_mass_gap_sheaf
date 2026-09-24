/-
# Same-carrier quadratic heat transmission at selected blocks

The exact trace and trace-free channels of a coordinate pair are retained
while exposing any two distinct quaternion blocks.  An arbitrary supported
spectator may use every block except the source block.  This is a finite Haar
identity, not an assumption about an interacting action.
-/

import YMGap.Continuum.SU2QuaternionQuadraticHeatProduct
import YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry

namespace YMGap.Continuum.SU2QuaternionSelectedPairQuadraticHeat

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionFourBlockSelection
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionRelativeHeatInsertion
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission (relativeHeat)
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionQuadraticHeatProduct
  (coordinatePair_transmission)
open YMGap.Continuum.SU2QuaternionQuadraticHeatTransmission
  (coordinatePair)
open YMGap.Continuum.SU2QuaternionHeadLinearHaar (coordinateMoment)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)

local infix:50 " ≈ " => Q'.eqv

private def retainedPair (i j : Fin 4) : RatPoly :=
  polyMul (polyVar (4+i.val)) (polyVar (4+j.val))

private theorem retainedPair_partial (i j : Fin 4) :
    RatPolyCoeffEqv (partialHaarHead (retainedPair i j)) (coordinatePair i j) := by
  apply RatPolyCoeffEqv.of_canon_termwise
  have h : ∀ a b : Fin 4, RatPolyTermwiseEqv
      (canonRat (partialHaarHead (retainedPair a b)))
      (canonRat (coordinatePair a b)) := by decide +kernel
  exact h i j

private theorem one_partial :
    RatPolyCoeffEqv (partialHaarHead polyOne) polyOne := by
  apply RatPolyCoeffEqv.of_canon_termwise
  decide +kernel

private theorem retainedPair_haar (tailBlocks : Nat) (i j : Fin 4) (r : RatPoly)
    (hr : HeadQuaternionIndependent r) :
    quaternionHaar (tailBlocks+1) (polyMul (retainedPair i j) r) ≈
      quaternionHaar tailBlocks
        (polyMul (coordinatePair i j) (dropHeadPolynomial r)) :=
  Q'.eqv_trans _ _ _
    (quaternionHaar_polyMul_headIndependent tailBlocks _ r hr)
    (haar_of_coeff ((retainedPair_partial i j).mul_right _))

private theorem independent_haar (tailBlocks : Nat) (r : RatPoly)
    (hr : HeadQuaternionIndependent r) :
    quaternionHaar (tailBlocks+1) r ≈
      quaternionHaar tailBlocks (dropHeadPolynomial r) := by
  have h := quaternionHaar_polyMul_headIndependent tailBlocks polyOne r hr
  have hl := haar_of_coeff (blocks := tailBlocks+1) (RatPolyCoeffEqv.one_mul r)
  have ht := haar_of_coeff (blocks := tailBlocks)
    ((one_partial.mul_right (dropHeadPolynomial r)).trans
      (RatPolyCoeffEqv.one_mul (dropHeadPolynomial r)))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hl) (Q'.eqv_trans _ _ _ h ht)

/-- Quadratic relative heat transmission with the independent insertion kept
on the same full Haar carrier. -/
theorem coordinatePair_transmission_same_carrier
    (tailBlocks : Nat) (hb : 0 < tailBlocks)
    (w : Q') (K : Nat) (hK : 2 ≤ K) (i j : Fin 4) (r : RatPoly)
    (hr : HeadQuaternionIndependent r) :
    quaternionHaar (tailBlocks+1) (polyMul
      (polyMul (relativeHeat w K) (coordinatePair i j)) r) ≈
      qpow w 8 * quaternionHaar (tailBlocks+1)
        (polyMul (retainedPair i j) r) +
      (1 + -(qpow w 8)) *
        (coordinateMoment i j * quaternionHaar (tailBlocks+1) r) := by
  have h := Q'.eqv_trans _ _ _ (independent_to_lift tailBlocks _ r hr)
    (coordinatePair_transmission tailBlocks hb w K hK i j
      (dropHeadPolynomial r))
  exact Q'.eqv_trans _ _ _ h
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_symm (retainedPair_haar tailBlocks i j r hr)))
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.eqv_symm (independent_haar tailBlocks r hr)))))

/-- The selected-block form: the source pair at `a` is transmitted to `b`,
and the exact Haar trace channel remains on the unchanged spectator. -/
theorem coordinatePair_selected_transmission
    (tailBlocks : Nat) (hb : 0 < tailBlocks)
    (a b : Fin (tailBlocks+1)) (hab : a.val ≠ b.val)
    (w : Q') (K : Nat) (hK : 2 ≤ K) (i j : Fin 4) (r : RatPoly)
    (hr : SupportedQuaternionBlocks (tailBlocks+1) r)
    (hd : HasQuaternionBlockDegree a.val 0 r) :
    quaternionHaar (tailBlocks+1) (polyMul
      (polyMul (heatAt a.val b.val w K)
        (polyMul (polyVar (4*a.val+i.val)) (polyVar (4*a.val+j.val)))) r) ≈
      qpow w 8 * quaternionHaar (tailBlocks+1)
        (polyMul (polyMul (polyVar (4*b.val+i.val))
          (polyVar (4*b.val+j.val))) r) +
      (1 + -(qpow w 8)) *
        (coordinateMoment i j * quaternionHaar (tailBlocks+1) r) := by
  let steps := pairSteps (show 1 < tailBlocks+1 by omega) a b
  let tr := applyQuaternionBlockSwapChain steps r
  have htr : SupportedQuaternionBlocks (tailBlocks+1) tr :=
    applyQuaternionBlockSwapChain_supported steps r hr
  have hk := heat_supported a.isLt b.isLt w K
  have hai := coordinate_supported a.isLt i
  have haj := coordinate_supported a.isLt j
  have hbi := coordinate_supported b.isLt i
  have hbj := coordinate_supported b.isLt j
  have h0i := coordinate_supported (show 0 < tailBlocks+1 by omega) i
  have h0j := coordinate_supported (show 0 < tailBlocks+1 by omega) j
  have h1i := coordinate_supported (show 1 < tailBlocks+1 by omega) i
  have h1j := coordinate_supported (show 1 < tailBlocks+1 by omega) j
  have hkh := heat_supported (show 0 < tailBlocks+1 by omega)
    (show 1 < tailBlocks+1 by omega) w K
  have hd0 : HasQuaternionBlockDegree 0 0 tr := by
    apply chain_degree steps (by omega)
    rw [pair_zero (by omega) a b hab]
    exact hd
  have hindependent : HeadQuaternionIndependent tr := hd0
  have hleft := quaternionHaar_applyQuaternionBlockSwapChain steps _
    (supported_polyMul (supported_polyMul hk (supported_polyMul hai haj)) hr)
  rw [chain_mul, chain_mul, chain_mul] at hleft
  have hpair0 := (coordinate_exposed steps (by omega)
    (pair_zero (by omega) a b hab) i).mul
      (coordinate_exposed steps (by omega)
        (pair_zero (by omega) a b hab) j)
  have hpin := ((heat_exposed (by omega) a b hab w K).mul
    (PaddedPolynomialCoeffEqv.of_prefix hpair0)).mul
    (PaddedPolynomialCoeffEqv.refl (tailBlocks+1) tr)
  have hleftPin := hpin.haar
    (supported_polyMul
      (supported_polyMul (applyQuaternionBlockSwapChain_supported steps _ hk)
        (supported_polyMul
          (applyQuaternionBlockSwapChain_supported steps _ hai)
          (applyQuaternionBlockSwapChain_supported steps _ haj))) htr)
    (supported_polyMul (supported_polyMul hkh (supported_polyMul h0i h0j)) htr)
  have hright := quaternionHaar_applyQuaternionBlockSwapChain steps _
    (supported_polyMul (supported_polyMul hbi hbj) hr)
  rw [chain_mul, chain_mul] at hright
  have hpair1 := (coordinate_exposed steps (by omega)
    (pair_one (by omega) a b) i).mul
      (coordinate_exposed steps (by omega) (pair_one (by omega) a b) j)
  have hrightPin := quaternionHaar_prefixPolynomialEqv (tailBlocks+1)
    (hpair1.mul (QuaternionPrefixPolynomialEqv.refl (tailBlocks+1) tr))
    (supported_polyMul
      (supported_polyMul
        (applyQuaternionBlockSwapChain_supported steps _ hbi)
        (applyQuaternionBlockSwapChain_supported steps _ hbj)) htr)
    (supported_polyMul (supported_polyMul h1i h1j) htr)
  have htrace := quaternionHaar_applyQuaternionBlockSwapChain steps r hr
  simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one] at hleftPin hrightPin
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hleft)
    (Q'.eqv_trans _ _ _ hleftPin
      (Q'.eqv_trans _ _ _
        (coordinatePair_transmission_same_carrier tailBlocks hb w K hK i j tr hindependent)
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.eqv_trans _ _ _ (Q'.eqv_symm hrightPin) hright))
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.mul_eqv_congr_left _ _ _ htrace)))))

#print axioms coordinatePair_transmission_same_carrier
#print axioms coordinatePair_selected_transmission

end YMGap.Continuum.SU2QuaternionSelectedPairQuadraticHeat
