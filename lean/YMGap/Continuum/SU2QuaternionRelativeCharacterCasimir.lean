/-
# Casimir eigenvalue of the relative two-link character

The solid representative of the relative character remains homogeneous after
the auxiliary variables are specialized.  Its harmonicity therefore gives
the exact head Casimir eigenvalue, and the proved solid-to-character Haar
carrier transports that identity to the ordinary character used by the heat
kernel.  The final theorem includes the dimension normalization appearing in
`normalizedCharacterAt`.
-/

import YMGap.Continuum.SU2QuaternionRelativeHarmonicSelection
import YMGap.Continuum.SU2QuaternionCyclicHeadCasimir
import YMGap.Continuum.SU2QuaternionCharacterProductPositive

namespace YMGap.Continuum.SU2QuaternionRelativeCharacterCasimir

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.SU2QuaternionTailEvaluationDifferential
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection
open YMGap.Continuum.SU2QuaternionRelativeHarmonicSelection
open YMGap.Continuum.QuaternionHaarAngularCasimir
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarExposedHeatCasimir
open YMGap.Continuum.SU2QuaternionCharacterProductPositive
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry

/-- Auxiliary specialization preserves the exact head degree of the relative
solid character. -/
theorem relativeSolid_blockDegree (spin : Nat) :
    HasQuaternionBlockDegree 0 spin (relativeSolid spin) := by
  unfold relativeSolid
  apply solidZonalCharacterPolynomial_blockDegree
  · exact evaluate_headDegree 8 auxiliaryUnits (by decide)
      (exposedFourWord_scalar_blockDegree false true false false 0 (by decide))
  · exact evaluate_headDegree 8 auxiliaryUnits (by decide)
      (fourQuaternionRadiusProduct_blockDegree 0 (by decide))

/-- Every ordinary relative character has its exact head Casimir eigenvalue
on any Haar carrier containing its two quaternion blocks. -/
theorem relativeCharacter_angularCasimir (blocks spin : Nat) (hb : 1 < blocks) :
    HaarCarrierEqv blocks
      (angularLaplacian (relativeCharacter spin))
      (polySmul (-(Q'.ofNat spin * (Q'.ofNat spin + 2)))
        (relativeCharacter spin)) := by
  let eigenvalue := -(Q'.ofNat spin * (Q'.ofNat spin + 2))
  have hc : HaarCarrierEqv blocks (relativeSolid spin) (relativeCharacter spin) :=
    solid_character_pin blocks hb spin
  have hl := angularLaplacian_carrier (by omega : 0 < blocks) hc
  have he : HaarCarrierEqv blocks (angularLaplacian (relativeSolid spin))
      (polySmul eigenvalue (relativeSolid spin)) :=
    harmonic_angularLaplacian (by omega) (relativeSolid spin)
      (relativeSolid_blockDegree spin) (relativeSolid_harmonic spin)
  exact HaarCarrierEqv.trans (HaarCarrierEqv.symm hl)
    (HaarCarrierEqv.trans he (HaarCarrierEqv.smul eigenvalue hc))

/-- The dimension-normalized relative character used by one cyclic heat step
has the same head Casimir eigenvalue. -/
theorem normalizedCharacterAt_zero_one_angularCasimir
    (blocks degree : Nat) (hb : 1 < blocks) :
    HaarCarrierEqv blocks
      (angularLaplacian (normalizedCharacterAt 0 1 degree))
      (polySmul (-(Q'.ofNat degree * (Q'.ofNat degree + 2)))
        (normalizedCharacterAt 0 1 degree)) := by
  let dimension := Q'.ofNat (degree+1)
  let eigenvalue := -(Q'.ofNat degree * (Q'.ofNat degree + 2))
  have hchar := relativeCharacter_angularCasimir blocks degree hb
  have hscalar : scalarAt 0 1 = relativeScalar := rfl
  rw [normalizedCharacterAt, hscalar]
  have hlin : HaarCarrierEqv blocks
      (angularLaplacian (polySmul dimension (relativeCharacter degree)))
      (polySmul dimension (angularLaplacian (relativeCharacter degree))) :=
    RatPolyCoeffEqv.haarCarrier
      (SU2QuaternionCyclicHeadCasimir.angularLaplacian_smul
        dimension (relativeCharacter degree))
  refine hlin.trans ((HaarCarrierEqv.smul dimension hchar).trans ?_)
  exact RatPolyCoeffEqv.haarCarrier
    ((RatPolyCoeffEqv.smul_assoc dimension eigenvalue (relativeCharacter degree)).trans
      ((RatPolyCoeffEqv.smul_coefficient
        (Q'.mul_comm_eqv dimension eigenvalue) (relativeCharacter degree)).trans
        (RatPolyCoeffEqv.smul_assoc eigenvalue dimension
          (relativeCharacter degree)).symm))

end YMGap.Continuum.SU2QuaternionRelativeCharacterCasimir

#print axioms YMGap.Continuum.SU2QuaternionRelativeCharacterCasimir.relativeSolid_blockDegree
#print axioms YMGap.Continuum.SU2QuaternionRelativeCharacterCasimir.relativeCharacter_angularCasimir
#print axioms YMGap.Continuum.SU2QuaternionRelativeCharacterCasimir.normalizedCharacterAt_zero_one_angularCasimir
