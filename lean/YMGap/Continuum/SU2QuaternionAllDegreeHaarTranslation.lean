/-
# Unconditional all-degree polynomial Haar translation

The original head substitution preserves the full product-Haar functional.
The exact all-degree moment theorem removes the former moment-check premise;
the original sphere ideal removes the explicit multiplier-radius power.
Exposing and restoring an arbitrary distinct block pair then yields genuine
left/right shears on the SAME supported polynomial carrier, without scans.

This supplies changes of variables, not reflection positivity of the shared
slab network or a physical spectral gap.
-/

import YMGap.Continuum.SU2QuaternionTranslationHaarMoments
import YMGap.Continuum.SU2QuaternionSelectedHaarTranslation

namespace YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslation
open YMGap.Continuum.SU2QuaternionTranslationHaarMoments

local infix:50 " ≈ " => Q'.eqv

/-- All exponent quadruples, with an arbitrary untouched tail insertion. -/
theorem translatedMoment_tail_haar (right : Bool) (blocks : Nat) (hb : 0 < blocks)
    (e0 e1 e2 e3 : Nat) (tail : RatPoly) :
    quaternionHaar blocks (polyMul
      (partialHaarHead (translatedHeadMonomial
        (if right then rightTranslatedHeadQuaternion else leftTranslatedHeadQuaternion) e0 e1 e2 e3)) tail) ≈
      headQuaternionMoment (headExponentLedger e0 e1 e2 e3) * quaternionHaar blocks tail := by
  have h := RatPolyCoeffEqv.haarCarrier (blocks := blocks)
    (translatedHeadMonomial_haar_expected right e0 e1 e2 e3) tail
  exact Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_comm blocks _ tail)
    (Q'.eqv_trans _ _ _ h
      (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_comm blocks tail _)
        (expectedTranslatedHeadMoment_mul_haar blocks hb e0 e1 e2 e3 tail)))

private theorem headTailLift_independent (term : RatTerm) :
    HeadQuaternionIndependent (headTailLiftTerm term) := by
  intro source hs
  simp only [headTailLiftTerm, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst source
  simp [headQuaternionDegree, exponentAt]

/-- One original substituted source term, before any integration. -/
theorem translatedHeadTerm_haar (right : Bool) (blocks : Nat) (hb : 0 < blocks) (term : RatTerm) :
    quaternionHaar (blocks + 1) (translatedHeadTerm
      (if right then rightTranslatedHeadQuaternion else leftTranslatedHeadQuaternion) term) ≈
      term.2 * quaternionHaarMono (blocks + 1) term.1 := by
  have hp := quaternionHaar_polyMul_headIndependent blocks
    (translatedHeadMonomial
      (if right then rightTranslatedHeadQuaternion else leftTranslatedHeadQuaternion)
      (exponentAt term.1 0) (exponentAt term.1 1) (exponentAt term.1 2) (exponentAt term.1 3))
    (headTailLiftTerm term) (headTailLift_independent term)
  have hdrop : dropHeadPolynomial (headTailLiftTerm term) = [(term.1.drop 4, term.2)] := by
    simp [dropHeadPolynomial, headTailLiftTerm]
  rw [hdrop] at hp
  refine Q'.eqv_trans _ _ _ hp ?_
  refine Q'.eqv_trans _ _ _ (translatedMoment_tail_haar right blocks hb
    (exponentAt term.1 0) (exponentAt term.1 1) (exponentAt term.1 2) (exponentAt term.1 3)
    [(term.1.drop 4, term.2)]) ?_
  change headQuaternionMoment term.1 *
      (term.2 * quaternionHaarMono blocks (term.1.drop 4) + 0) ≈ _
  rw [Q'.add_zero']
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _) ?_
  exact Q'.mul_eqv_congr_left _ _ _ (headMoment_mul_tailHaarMono blocks term.1)

/-- The actual head-substitution polynomial preserves the full product-Haar
functional, at every degree. No scan or moment premise is present. -/
theorem translatedHeadPolynomial_haar (right : Bool) (blocks : Nat) (hb : 0 < blocks) :
    ∀ p : RatPoly, quaternionHaar (blocks + 1) (translatedHeadPolynomial
      (if right then rightTranslatedHeadQuaternion else leftTranslatedHeadQuaternion) p) ≈
      quaternionHaar (blocks + 1) p
  | [] => Q'.eqv_refl 0
  | term :: rest =>
      Q'.eqv_trans _ _ _ (quaternionHaar_append (blocks + 1) _ _)
        (Q'.add_eqv_congr' (translatedHeadTerm_haar right blocks hb term)
          (translatedHeadPolynomial_haar right blocks hb rest))

/-- Unconditional all-degree invariance of the original selected left shear.
The support and distinct-block guards are unchanged; only hcheck is removed. -/
theorem selectedLeftTranslatedPolynomial_haar
    (tailBlocks selected multiplier : Nat) (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1) (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier) (p : RatPoly)
    (hsupport : SupportedQuaternionBlocks (tailBlocks + 1) p) :
    quaternionHaar (tailBlocks + 1) (selectedLeftTranslatedPolynomial tailBlocks selected multiplier
      hblocks hselected hmultiplier hdistinct p) ≈ quaternionHaar (tailBlocks + 1) p := by
  unfold selectedLeftTranslatedPolynomial
  let exposed := exposeTranslationPairPolynomial (tailBlocks + 1) selected multiplier
    (by omega) hselected hmultiplier p
  have he : SupportedQuaternionBlocks (tailBlocks + 1) exposed :=
    exposeTranslationPairPolynomial_supported (tailBlocks + 1) selected multiplier
      (by omega) hselected hmultiplier p
  exact Q'.eqv_trans _ _ _
    (quaternionHaar_restoreTranslationPair (tailBlocks + 1) selected multiplier (by omega)
      hselected hmultiplier _ (leftTranslatedHeadPolynomial_supported tailBlocks hblocks exposed he))
    (Q'.eqv_trans _ _ _ (translatedHeadPolynomial_haar false tailBlocks hblocks exposed)
      (quaternionHaar_exposeTranslationPair (tailBlocks + 1) selected multiplier
        (by omega) hselected hmultiplier p hsupport))

/-- Unconditional all-degree invariance of the original selected right shear. -/
theorem selectedRightTranslatedPolynomial_haar
    (tailBlocks selected multiplier : Nat) (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1) (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier) (p : RatPoly)
    (hsupport : SupportedQuaternionBlocks (tailBlocks + 1) p) :
    quaternionHaar (tailBlocks + 1) (selectedRightTranslatedPolynomial tailBlocks selected multiplier
      hblocks hselected hmultiplier hdistinct p) ≈ quaternionHaar (tailBlocks + 1) p := by
  unfold selectedRightTranslatedPolynomial
  let exposed := exposeTranslationPairPolynomial (tailBlocks + 1) selected multiplier
    (by omega) hselected hmultiplier p
  have he : SupportedQuaternionBlocks (tailBlocks + 1) exposed :=
    exposeTranslationPairPolynomial_supported (tailBlocks + 1) selected multiplier
      (by omega) hselected hmultiplier p
  exact Q'.eqv_trans _ _ _
    (quaternionHaar_restoreTranslationPair (tailBlocks + 1) selected multiplier (by omega)
      hselected hmultiplier _ (rightTranslatedHeadPolynomial_supported tailBlocks hblocks exposed he))
    (Q'.eqv_trans _ _ _ (translatedHeadPolynomial_haar true tailBlocks hblocks exposed)
      (quaternionHaar_exposeTranslationPair (tailBlocks + 1) selected multiplier
        (by omega) hselected hmultiplier p hsupport))

end YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslation

#print axioms YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslation.translatedMoment_tail_haar
#print axioms YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslation.translatedHeadTerm_haar
#print axioms YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslation.translatedHeadPolynomial_haar
#print axioms YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslation.selectedLeftTranslatedPolynomial_haar
#print axioms YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslation.selectedRightTranslatedPolynomial_haar
