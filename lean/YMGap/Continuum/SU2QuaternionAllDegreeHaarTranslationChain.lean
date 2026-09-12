/-
# Scan-free Haar translation chains and the literal BF4 tree ledger

Direct and inverse multiplier shears preserve the original full Haar value
at every polynomial degree. They compose on the unchanged supported carrier.
In particular the existing literal 139-step BF4 tree-gauge ledger no longer
requires successive polynomial scans or a degree-five restriction.

This theorem identifies the integral of the existing ledger substitution;
it does not by itself prove a new word-semantic pin or reflected-slab gluing.
-/

import YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslation
import YMGap.Continuum.BF4ExactSpatialTreeGaugeTranslationLedger

namespace YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslationChain

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslation
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslation
open YMGap.Continuum.BF4ExactSpatialTreeGaugeTranslationLedger

local infix:50 " ≈ " => Q'.eqv

theorem selectedLeftInverseTranslatedPolynomial_haar
    (tailBlocks selected multiplier : Nat) (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1) (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier) (p : RatPoly)
    (hsupport : SupportedQuaternionBlocks (tailBlocks + 1) p) :
    quaternionHaar (tailBlocks + 1) (selectedLeftInverseTranslatedPolynomial tailBlocks selected multiplier
      hblocks hselected hmultiplier hdistinct p) ≈ quaternionHaar (tailBlocks + 1) p :=
  Q'.eqv_trans _ _ _ (quaternionHaar_conjugateQuaternionBlock (tailBlocks + 1) multiplier _)
    (Q'.eqv_trans _ _ _
      (selectedLeftTranslatedPolynomial_haar tailBlocks selected multiplier hblocks hselected hmultiplier
        hdistinct _ (conjugateQuaternionBlockPolynomial_supported (tailBlocks + 1) multiplier p hsupport))
      (quaternionHaar_conjugateQuaternionBlock (tailBlocks + 1) multiplier p))

theorem selectedRightInverseTranslatedPolynomial_haar
    (tailBlocks selected multiplier : Nat) (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1) (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier) (p : RatPoly)
    (hsupport : SupportedQuaternionBlocks (tailBlocks + 1) p) :
    quaternionHaar (tailBlocks + 1) (selectedRightInverseTranslatedPolynomial tailBlocks selected multiplier
      hblocks hselected hmultiplier hdistinct p) ≈ quaternionHaar (tailBlocks + 1) p :=
  Q'.eqv_trans _ _ _ (quaternionHaar_conjugateQuaternionBlock (tailBlocks + 1) multiplier _)
    (Q'.eqv_trans _ _ _
      (selectedRightTranslatedPolynomial_haar tailBlocks selected multiplier hblocks hselected hmultiplier
        hdistinct _ (conjugateQuaternionBlockPolynomial_supported (tailBlocks + 1) multiplier p hsupport))
      (quaternionHaar_conjugateQuaternionBlock (tailBlocks + 1) multiplier p))

/-- Every existing direct/inverse left/right step preserves Haar, without
altering the step data or its index/distinctness guards. -/
theorem applySelectedTranslationStep_haar {tailBlocks : Nat} (hb : 0 < tailBlocks)
    (step : SelectedTranslationStep tailBlocks) (p : RatPoly)
    (hs : SupportedQuaternionBlocks (tailBlocks + 1) p) :
    quaternionHaar (tailBlocks + 1) (applySelectedTranslationStep hb step p) ≈
      quaternionHaar (tailBlocks + 1) p := by
  cases hside : step.side <;> cases horientation : step.multiplierOrientation
  · simpa only [applySelectedTranslationStep, hside, horientation] using
      selectedLeftTranslatedPolynomial_haar tailBlocks step.selected step.multiplier hb
        step.selected_lt step.multiplier_lt step.distinct p hs
  · simpa only [applySelectedTranslationStep, hside, horientation] using
      selectedLeftInverseTranslatedPolynomial_haar tailBlocks step.selected step.multiplier hb
        step.selected_lt step.multiplier_lt step.distinct p hs
  · simpa only [applySelectedTranslationStep, hside, horientation] using
      selectedRightTranslatedPolynomial_haar tailBlocks step.selected step.multiplier hb
        step.selected_lt step.multiplier_lt step.distinct p hs
  · simpa only [applySelectedTranslationStep, hside, horientation] using
      selectedRightInverseTranslatedPolynomial_haar tailBlocks step.selected step.multiplier hb
        step.selected_lt step.multiplier_lt step.distinct p hs

/-- Arbitrary finite chains on the SAME supported carrier. Intermediate
polynomials are covered by the theorem, not rechecked by an executable scan. -/
theorem applySelectedTranslationSteps_haar {tailBlocks : Nat} (hb : 0 < tailBlocks) :
    ∀ (steps : List (SelectedTranslationStep tailBlocks)) (p : RatPoly),
      SupportedQuaternionBlocks (tailBlocks + 1) p →
      quaternionHaar (tailBlocks + 1) (applySelectedTranslationSteps hb steps p) ≈
        quaternionHaar (tailBlocks + 1) p
  | [], _, _ => Q'.eqv_refl _
  | step :: rest, p, hs =>
      Q'.eqv_trans _ _ _
        (applySelectedTranslationSteps_haar hb rest (applySelectedTranslationStep hb step p)
          (applySelectedTranslationStep_supported hb step p))
        (applySelectedTranslationStep_haar hb step p hs)

/-- Concrete consumer: the ORIGINAL literal BF4 139-step tree-gauge ledger
preserves Haar_48 for every supported polynomial, without a degree bound. -/
theorem applyBF4TreeGaugeTranslationLedger_haar (p : RatPoly)
    (hs : SupportedQuaternionBlocks 48 p) :
    quaternionHaar 48 (applyBF4TreeGaugeTranslationLedger p) ≈ quaternionHaar 48 p :=
  applySelectedTranslationSteps_haar (by decide : 0 < bf4TreeGaugeTailBlocks)
    bf4TreeGaugeTranslationSteps p hs

end YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslationChain

#print axioms YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslationChain.selectedLeftInverseTranslatedPolynomial_haar
#print axioms YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslationChain.selectedRightInverseTranslatedPolynomial_haar
#print axioms YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslationChain.applySelectedTranslationStep_haar
#print axioms YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslationChain.applySelectedTranslationSteps_haar
#print axioms YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslationChain.applyBF4TreeGaugeTranslationLedger_haar
