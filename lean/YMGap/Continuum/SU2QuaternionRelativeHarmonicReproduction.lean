/-
# All-degree reproduction by the original relative SU(2) heat packet

The explicit harmonic lowering, substitution, radial normalization and
ordinary-character leading term join to give the exact dimension factor.
Combined with the proved off-diagonal selection, the original finite heat
packet acts on every head-homogeneous harmonic by its Casimir nome power,
with the original retained-link substitution and arbitrary boundary insertion.
This is a local kinetic identity, not an interacting-transfer bound.
-/

import YMGap.Continuum.SU2QuaternionHarmonicPowerSubstitution
import YMGap.Continuum.SU2QuaternionHarmonicCharacterLeading
import YMGap.Continuum.SU2QuaternionRelativeHarmonicSelection

namespace YMGap.Continuum.SU2QuaternionRelativeHarmonicReproduction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission
open YMGap.Continuum.SU2QuaternionRelativeHarmonicSelection
open YMGap.Continuum.SU2QuaternionDroppedHeadSubstitution
open YMGap.Continuum.SU2QuaternionHarmonicPowerSubstitution
open YMGap.Continuum.SU2QuaternionHarmonicCharacterLeading
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.RGTransport (qpow c4 dimQ)

local infix:50 " ≈ " => Q'.eqv

/-- Exact dimension-normalized ordinary-character reproduction, before
any retained-variable integration. No division or tail sphere premise. -/
theorem character_harmonic_reproduction (n : Nat) (p : RatPoly)
    (hp : HasQuaternionBlockDegree 0 n p)
    (hh : RatPolyCoeffEqv (headLaplacian p) polyZero) :
    RatPolyCoeffEqv
      (polySmul (Q'.ofNat (n+1))
        (partialHaarHead (polyMul (relativeCharacter n) p)))
      (substituteRetained p) := by
  have hscale : (Q'.ofNat (n+1) * Q'.ofNat (2^n)) ≈ Q'.ofNat (2^n*(n+1)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
      (SU3CharFactor.ofNat_mul_eqv _ _)
  exact ((partialHaarHead_congr (RatPolyCoeffEqv.mul_comm _ _)).smul _).trans
    (((harmonic_character_leading n p hp hh).smul _).trans
      ((RatPolyCoeffEqv.smul_assoc _ _ _).trans
        ((RatPolyCoeffEqv.smul_coefficient hscale _).trans
          (harmonic_power_substitution n p hp hh))))

private theorem lifted_independent (r : RatPoly) :
    HeadQuaternionIndependent (liftHead r) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  rfl

/-- The normalized diagonal identity in the actual full Haar integral,
retaining an arbitrary boundary polynomial and every coefficient of p. -/
theorem character_harmonic_boundary_reproduction (tailBlocks n : Nat) (p : RatPoly)
    (hp : HasQuaternionBlockDegree 0 n p)
    (hh : RatPolyCoeffEqv (headLaplacian p) polyZero) (boundary : RatPoly) :
    Q'.ofNat (n+1) * quaternionHaar (tailBlocks+1)
      (polyMul (polyMul (relativeCharacter n) p) (liftHead boundary)) ≈
      quaternionHaar tailBlocks (polyMul (substituteRetained p) boundary) := by
  have hf := quaternionHaar_polyMul_headIndependent tailBlocks
    (polyMul (relativeCharacter n) p) (liftHead boundary) (lifted_independent boundary)
  rw [drop_liftHead] at hf
  have hc := (RatPolyCoeffEqv.polyMul_smul_left (Q'.ofNat (n+1))
      (partialHaarHead (polyMul (relativeCharacter n) p)) boundary).symm.trans
    ((character_harmonic_reproduction n p hp hh).mul_right boundary)
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hf)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_polySmul _ _ _))
      (haar_of_coeff hc))

/-- The FULL original finite heat packet has its actual Casimir multiplier
on every homogeneous harmonic. The cutoff guard remains explicit, and the
substitution output is computed rather than a supplied diagonal premise. -/
theorem heat_harmonic_reproduction (tailBlocks : Nat) (hb : 0 < tailBlocks)
    (w : Q') (K n : Nat) (p : RatPoly)
    (hp : HasQuaternionBlockDegree 0 n p)
    (hh : RatPolyCoeffEqv (headLaplacian p) polyZero) (boundary : RatPoly) :
    quaternionHaar (tailBlocks+1)
      (polyMul (polyMul (relativeHeat w K) p) (liftHead boundary)) ≈
      if n ≤ K then qpow w (n*(n+2)) *
        quaternionHaar tailBlocks (polyMul (substituteRetained p) boundary) else 0 := by
  have hs := heat_harmonic_diagonal tailBlocks hb w K n hp hh boundary
  by_cases hK : n ≤ K
  · rw [if_pos hK] at hs ⊢
    refine Q'.eqv_trans _ _ _ hs ?_
    change (dimQ n * qpow w (c4 n)) * _ ≈ _
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _))
        (Q'.mul_assoc_eqv _ _ _))
      (Q'.mul_eqv_congr_left _ _ _
        (character_harmonic_boundary_reproduction tailBlocks n p hp hh boundary))
  · rw [if_neg hK] at hs ⊢
    exact hs

end YMGap.Continuum.SU2QuaternionRelativeHarmonicReproduction

#print axioms YMGap.Continuum.SU2QuaternionRelativeHarmonicReproduction.character_harmonic_reproduction
#print axioms YMGap.Continuum.SU2QuaternionRelativeHarmonicReproduction.character_harmonic_boundary_reproduction
#print axioms YMGap.Continuum.SU2QuaternionRelativeHarmonicReproduction.heat_harmonic_reproduction
