/-
# Supported Haar equalities survive selected translation ledgers

An original selected shear preserves supported Haar equality because it is a
polynomial algebra map and preserves the full Haar integral. The positive
finite-Haar form converts the translated difference's square-nullity back to
equality against every supported insertion. Finite ledgers compose on the
same supported carrier; this is an ordinary Haar statement, not a weighted
action or completed-sector invariance theorem.
-/

import YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslationChain
import YMGap.Continuum.SU2QuaternionHaarBlockEmbeddingSupportedEquality
import YMGap.Continuum.SU2QuaternionHaarCertificateReindex

namespace YMGap.Continuum.SU2QuaternionSelectedTranslationCarrier

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslationChain
open YMGap.Continuum.SU2QuaternionHaarBlockEmbeddingSupportedEquality
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

private theorem step_difference_coeffEqv {tailBlocks : Nat}
    (hblocks : 0 < tailBlocks) (step : SelectedTranslationStep tailBlocks)
    (p q : RatPoly) :
    RatPolyCoeffEqv
      (applySelectedTranslationStep hblocks step (polyAdd p (polySmul (-1) q)))
      (polyAdd (applySelectedTranslationStep hblocks step p)
        (polySmul (-1) (applySelectedTranslationStep hblocks step q))) := by
  rw [applySelectedTranslationStep_add]
  exact (RatPolyCoeffEqv.refl _).add
    (applySelectedTranslationStep_smul hblocks step (-1) q)

private theorem step_difference_square_haar_zero {tailBlocks : Nat}
    (hblocks : 0 < tailBlocks) (step : SelectedTranslationStep tailBlocks)
    {p q : RatPoly} (hp : SupportedQuaternionBlocks (tailBlocks+1) p)
    (hq : SupportedQuaternionBlocks (tailBlocks+1) q)
    (hzero : quaternionHaar (tailBlocks+1)
      (polyMul (polyAdd p (polySmul (-1) q))
        (polyAdd p (polySmul (-1) q))) ≈ 0) :
    quaternionHaar (tailBlocks+1)
      (polyMul
        (polyAdd (applySelectedTranslationStep hblocks step p)
          (polySmul (-1) (applySelectedTranslationStep hblocks step q)))
        (polyAdd (applySelectedTranslationStep hblocks step p)
          (polySmul (-1) (applySelectedTranslationStep hblocks step q)))) ≈ 0 := by
  let d := polyAdd p (polySmul (-1) q)
  let d' := polyAdd (applySelectedTranslationStep hblocks step p)
    (polySmul (-1) (applySelectedTranslationStep hblocks step q))
  have hd : SupportedQuaternionBlocks (tailBlocks+1) d := by
    apply supported_add hp
    intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact hq s hs
  have hmul := applySelectedTranslationStep_mul hblocks step d d
  have hdiff : RatPolyCoeffEqv
      (applySelectedTranslationStep hblocks step d) d' := by
    change RatPolyCoeffEqv
      (applySelectedTranslationStep hblocks step (polyAdd p (polySmul (-1) q))) d'
    exact step_difference_coeffEqv hblocks step p q
  have hsquare : RatPolyCoeffEqv
      (applySelectedTranslationStep hblocks step (polyMul d d))
      (polyMul d' d') := by
    exact hmul.trans (hdiff.mul hdiff)
  have hhaar := applySelectedTranslationStep_haar hblocks step (polyMul d d)
    (supported_polyMul hd hd)
  have htranslated : quaternionHaar (tailBlocks+1)
      (polyMul d' d') ≈ quaternionHaar (tailBlocks+1) (polyMul d d) := by
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_of_coeff hsquare)) hhaar
  change quaternionHaar (tailBlocks+1) (polyMul d' d') ≈ 0
  exact Q'.eqv_trans _ _ _ htranslated hzero

/-- An elementary direct/inverse left/right selected translation preserves
supported Haar equality, using the actual selected-link substitution. -/
theorem applySelectedTranslationStep_preserves_supportedHaarEqv
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks)
    (step : SelectedTranslationStep tailBlocks) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks (tailBlocks+1) p)
    (hq : SupportedQuaternionBlocks (tailBlocks+1) q)
    (h : SupportedHaarEqv (tailBlocks+1) p q) :
    SupportedHaarEqv (tailBlocks+1)
      (applySelectedTranslationStep hblocks step p)
      (applySelectedTranslationStep hblocks step q) := by
  apply supportedHaarEqv_of_difference_square_zero
    (applySelectedTranslationStep_supported hblocks step p)
    (applySelectedTranslationStep_supported hblocks step q)
  have hzero := difference_square_zero hp hq h
  exact step_difference_square_haar_zero hblocks step hp hq hzero

/-- Any finite selected translation list preserves supported Haar equality;
each intermediate polynomial stays in the unchanged finite carrier. -/
theorem applySelectedTranslationSteps_preserves_supportedHaarEqv
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks) :
    ∀ (steps : List (SelectedTranslationStep tailBlocks)) {p q : RatPoly},
      SupportedQuaternionBlocks (tailBlocks+1) p →
      SupportedQuaternionBlocks (tailBlocks+1) q →
      SupportedHaarEqv (tailBlocks+1) p q →
      SupportedHaarEqv (tailBlocks+1)
        (applySelectedTranslationSteps hblocks steps p)
        (applySelectedTranslationSteps hblocks steps q)
  | [], _, _, hp, hq, h => h
  | step :: rest, p, q, hp, hq, h => by
      apply applySelectedTranslationSteps_preserves_supportedHaarEqv
        hblocks rest
        (applySelectedTranslationStep_supported hblocks step p)
        (applySelectedTranslationStep_supported hblocks step q)
      exact applySelectedTranslationStep_preserves_supportedHaarEqv
        hblocks step hp hq h

/-- Supported equality upgraded to arbitrary Haar insertions after one step. -/
theorem applySelectedTranslationStep_preserves_haarCarrierEqv
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks)
    (step : SelectedTranslationStep tailBlocks) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks (tailBlocks+1) p)
    (hq : SupportedQuaternionBlocks (tailBlocks+1) q)
    (h : HaarCarrierEqv (tailBlocks+1) p q) :
    HaarCarrierEqv (tailBlocks+1)
      (applySelectedTranslationStep hblocks step p)
      (applySelectedTranslationStep hblocks step q) := by
  apply carrier_of_supported
    (applySelectedTranslationStep_supported hblocks step p)
    (applySelectedTranslationStep_supported hblocks step q)
  exact applySelectedTranslationStep_preserves_supportedHaarEqv hblocks step hp hq
    (SupportedHaarEqv.of_carrier h)

/-- Arbitrary-insertion carrier equality survives any finite selected ledger,
with the initial polynomials supported on that finite carrier. -/
theorem applySelectedTranslationSteps_preserves_haarCarrierEqv
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks)
    (steps : List (SelectedTranslationStep tailBlocks)) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks (tailBlocks+1) p)
    (hq : SupportedQuaternionBlocks (tailBlocks+1) q)
    (h : HaarCarrierEqv (tailBlocks+1) p q) :
    HaarCarrierEqv (tailBlocks+1)
      (applySelectedTranslationSteps hblocks steps p)
      (applySelectedTranslationSteps hblocks steps q) := by
  apply carrier_of_supported
    (applySelectedTranslationSteps_supported hblocks steps p hp)
    (applySelectedTranslationSteps_supported hblocks steps q hq)
  exact applySelectedTranslationSteps_preserves_supportedHaarEqv hblocks steps hp hq
    (SupportedHaarEqv.of_carrier h)

#print axioms applySelectedTranslationStep_preserves_supportedHaarEqv
#print axioms applySelectedTranslationSteps_preserves_supportedHaarEqv
#print axioms applySelectedTranslationStep_preserves_haarCarrierEqv
#print axioms applySelectedTranslationSteps_preserves_haarCarrierEqv

end YMGap.Continuum.SU2QuaternionSelectedTranslationCarrier
