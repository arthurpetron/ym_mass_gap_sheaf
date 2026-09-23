/-
# Padded-equivalence transport through a conditional quaternion projection

The translation layer uses `PaddedPolynomialCoeffEqv` because block reindexing
may introduce trailing zero padding.  This file proves that the relation is
still compatible with one conditional projection inside a supported Haar
pairing.  It is a finite carrier lemma only; it does not identify the
selected-link heat operator or assert a spectral/continuum result.
-/

import YMGap.Continuum.SU2QuaternionSelectedProjectionReindex
import YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra

namespace YMGap.Continuum.SU2QuaternionPaddedProjectionPairing

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionSelectedProjectionReindex
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslation
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

/-- A padded coefficient equivalence remains valid after conditional
integration, and therefore after insertion into the supported Haar pairing. -/
theorem project_padded_pairing
    {blocks block : Nat} (hblock : block < blocks)
    {p q r : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p)
    (hq : SupportedQuaternionBlocks blocks q)
    (hr : SupportedQuaternionBlocks blocks r)
    (h : PaddedPolynomialCoeffEqv blocks p q) :
    quaternionHaar blocks (polyMul (project block p) r) ≈
      quaternionHaar blocks (polyMul (project block q) r) := by
  let identity := identityQuaternionBlockInvolution blocks
  have hproject : RatPolyCoeffEqv
      (project block (reindexQuaternionPolynomial identity p))
      (project block (reindexQuaternionPolynomial identity q)) := by
    exact project_congr block h
  have hleft := reindex_integrateQuaternionBlock identity block hblock p
  have hright := reindex_integrateQuaternionBlock identity block hblock q
  have hmap : identity.map block = block := rfl
  have hpadded : PaddedPolynomialCoeffEqv blocks (project block p) (project block q) := by
    unfold PaddedPolynomialCoeffEqv
    exact hleft.trans (hproject.trans hright.symm)
  have hp' := project_supported block hp
  have hq' := project_supported block hq
  have hins := PaddedPolynomialCoeffEqv.haar_insert hpadded hp' hq' r hr
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff (RatPolyCoeffEqv.mul_comm (project block p) r))
    (Q'.eqv_trans _ _ _ hins
      (haar_of_coeff (RatPolyCoeffEqv.mul_comm r (project block q))))

/-! The generic transport now has a direct selected-heat instance.  This
wrapper stops exactly at the projected exposed kernel; it does not identify
that kernel with `heatPair` or `headMap`. -/
theorem exposed_heat_projected_pairing
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (w : Q') (K : Nat)
    (insertion : RatPoly)
    (hinsertion : SupportedQuaternionBlocks (tailBlocks + 1) insertion) :
    quaternionHaar (tailBlocks + 1)
        (polyMul
          (project 0
            (exposeTranslationPairPolynomial (tailBlocks + 1)
              selected multiplier (by omega) hselected hmultiplier
              (heatAt selected multiplier w K))) insertion) ≈
      quaternionHaar (tailBlocks + 1)
        (polyMul (project 0 (relativeHeat w K)) insertion) := by
  have hkernel := exposeTranslationPair_heat
    (tailBlocks + 1) selected multiplier (by omega)
      hselected hmultiplier hdistinct w K
  have hexposed := exposeTranslationPairPolynomial_supported
    (tailBlocks + 1) selected multiplier (by omega)
      hselected hmultiplier (heatAt selected multiplier w K)
  have hrelative : SupportedQuaternionBlocks (tailBlocks + 1)
      (relativeHeat w K) := by
    exact heat_supported (a := 0) (b := 1) (by omega) (by omega) w K
  exact project_padded_pairing (blocks := tailBlocks + 1) (block := 0)
    (by omega) hexposed hrelative hinsertion hkernel

/-! Multiplying the exposed heat equivalence by an arbitrary supported state
and then projecting gives a concrete relative-heat conditional form.  This
is the strongest product reduction available before identifying that form
with `heatPair` for arbitrary shared spectators. -/
theorem exposed_heat_product_projected_pairing
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (w : Q') (K : Nat)
    (polynomial test : RatPoly) :
    quaternionHaar (tailBlocks + 1)
        (polyMul
          (project 0
            (exposeTranslationPairPolynomial (tailBlocks + 1)
              selected multiplier (by omega) hselected hmultiplier
              (polyMul (heatAt selected multiplier w K) polynomial)))
          (exposeTranslationPairPolynomial (tailBlocks + 1)
            selected multiplier (by omega) hselected hmultiplier test)) ≈
      quaternionHaar (tailBlocks + 1)
        (polyMul
          (project 0
            (polyMul (relativeHeat w K)
              (exposeTranslationPairPolynomial (tailBlocks + 1)
                selected multiplier (by omega) hselected hmultiplier
                polynomial)))
          (exposeTranslationPairPolynomial (tailBlocks + 1)
            selected multiplier (by omega) hselected hmultiplier test)) := by
  let blocks := tailBlocks + 1
  let head := translationPairHeadPermutation blocks selected hselected
  let tail := translationPairTailPermutation blocks selected multiplier
    (by omega) hselected hmultiplier
  let exposed (p : RatPoly) := reindexQuaternionPolynomial tail
    (reindexQuaternionPolynomial head p)
  have hheat := exposeTranslationPair_heat blocks selected multiplier
    (by omega) hselected hmultiplier hdistinct w K
  have hexposedPoly : SupportedQuaternionBlocks blocks (exposed polynomial) := by
    exact exposeTranslationPairPolynomial_supported blocks selected multiplier
      (by omega) hselected hmultiplier polynomial
  have hexposedTest : SupportedQuaternionBlocks blocks (exposed test) := by
    exact exposeTranslationPairPolynomial_supported blocks selected multiplier
      (by omega) hselected hmultiplier test
  have hrelative : SupportedQuaternionBlocks blocks (relativeHeat w K) := by
    exact heat_supported (a := 0) (b := 1) (by omega) (by omega) w K
  have hprod : PaddedPolynomialCoeffEqv blocks
      (exposed (polyMul (heatAt selected multiplier w K) polynomial))
      (polyMul (relativeHeat w K) (exposed polynomial)) := by
    have hmul := PaddedPolynomialCoeffEqv.mul hheat
      (PaddedPolynomialCoeffEqv.refl blocks (exposed polynomial))
    simpa only [exposed, exposeTranslationPairPolynomial,
      reindexQuaternionPolynomial_mul] using hmul
  have hleft : SupportedQuaternionBlocks blocks
      (exposed (polyMul (heatAt selected multiplier w K) polynomial)) := by
    exact exposeTranslationPairPolynomial_supported blocks selected multiplier
      (by omega) hselected hmultiplier
      (polyMul (heatAt selected multiplier w K) polynomial)
  have hright : SupportedQuaternionBlocks blocks
      (polyMul (relativeHeat w K) (exposed polynomial)) :=
    supported_polyMul hrelative hexposedPoly
  have hpair := project_padded_pairing (blocks := blocks) (block := 0)
    (by omega) hleft hright hexposedTest hprod
  simpa only [blocks, exposed] using hpair

end YMGap.Continuum.SU2QuaternionPaddedProjectionPairing

#print axioms YMGap.Continuum.SU2QuaternionPaddedProjectionPairing.project_padded_pairing
#print axioms YMGap.Continuum.SU2QuaternionPaddedProjectionPairing.exposed_heat_projected_pairing
#print axioms YMGap.Continuum.SU2QuaternionPaddedProjectionPairing.exposed_heat_product_projected_pairing
