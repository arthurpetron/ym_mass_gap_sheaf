/-
# Full-carrier relative heat transmission under independent insertions

Keep the original block count throughout. The unused head coordinate is
integrated, not deleted from the observable carrier. The arbitrary insertion
can depend on every other link, including the retained partner. This form
can replace one coordinate inside a multilinear plaquette while keeping all
other kernels and boundary variables in the same Haar calculation.
-/

import YMGap.Continuum.SU2QuaternionRelativeHeatTransmission

namespace YMGap.Continuum.SU2QuaternionRelativeHeatInsertion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

theorem lifted_independent (p : RatPoly) : HeadQuaternionIndependent (liftHead p) := by
  intro t ht
  obtain ⟨s,_,rfl⟩ := List.mem_map.mp ht
  rfl

/-- Fubini changes only the representation of the same independent factor. -/
theorem independent_to_lift (tailBlocks : Nat) (p r : RatPoly)
    (hr : HeadQuaternionIndependent r) :
    quaternionHaar (tailBlocks+1) (polyMul p r) ≈
      quaternionHaar (tailBlocks+1) (polyMul p (liftHead (dropHeadPolynomial r))) := by
  have h := quaternionHaar_polyMul_headIndependent tailBlocks p
    (liftHead (dropHeadPolynomial r)) (lifted_independent _)
  rw [drop_liftHead] at h
  exact Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_headIndependent tailBlocks p r hr) (Q'.eqv_symm h)

theorem retained_coordinate_partial (i : Fin 4) :
    RatPolyCoeffEqv (partialHaarHead (polyVar (4+i.val))) (polyVar i.val) := by
  apply RatPolyCoeffEqv.of_canon_termwise
  have h : ∀ j : Fin 4, RatPolyTermwiseEqv
      (canonRat (partialHaarHead (polyVar (4+j.val)))) (canonRat (polyVar j.val)) := by decide +kernel
  exact h i

theorem retained_coordinate_haar (tailBlocks : Nat) (i : Fin 4) (r : RatPoly)
    (hr : HeadQuaternionIndependent r) :
    quaternionHaar (tailBlocks+1) (polyMul (polyVar (4+i.val)) r) ≈
      quaternionHaar tailBlocks (polyMul (polyVar i.val) (dropHeadPolynomial r)) :=
  Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_headIndependent tailBlocks _ r hr)
    (haar_of_coeff ((retained_coordinate_partial i).mul_right _))

/-- Arbitrary head-independent insertion, with the SAME full carrier on both sides. -/
theorem coordinate_transmission_same_carrier (tailBlocks : Nat) (hb : 0 < tailBlocks)
    (w : Q') (K : Nat) (hK : 1 ≤ K) (i : Fin 4) (r : RatPoly)
    (hr : HeadQuaternionIndependent r) :
    quaternionHaar (tailBlocks+1) (polyMul
      (polyMul (relativeHeat w K) (polyVar i.val)) r) ≈
      qpow w 3 * quaternionHaar (tailBlocks+1) (polyMul (polyVar (4+i.val)) r) :=
  Q'.eqv_trans _ _ _ (independent_to_lift tailBlocks _ r hr)
    (Q'.eqv_trans _ _ _ (coordinate_transmission tailBlocks hb w K hK i (dropHeadPolynomial r))
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (retained_coordinate_haar tailBlocks i r hr))))

end YMGap.Continuum.SU2QuaternionRelativeHeatInsertion

#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatInsertion.lifted_independent
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatInsertion.independent_to_lift
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatInsertion.retained_coordinate_partial
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatInsertion.retained_coordinate_haar
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatInsertion.coordinate_transmission_same_carrier
