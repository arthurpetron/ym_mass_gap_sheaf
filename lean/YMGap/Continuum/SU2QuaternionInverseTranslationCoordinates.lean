/-
# Literal coordinate images for all four selected Haar shears

The original inverse shear is conjugate--translate--conjugate on the
multiplier block. The coordinate sign identities and direct shear pin prove
its ordered inverse-multiplier product image, with every other link fixed.
These are arbitrary-index polynomial-prefix identities, not finite scans.
Global temporal-ledger composition and reflected-slab gluing remain open.
-/

import YMGap.Continuum.SU2QuaternionCoordinateConjugation

namespace YMGap.Continuum.SU2QuaternionInverseTranslationCoordinates

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslation
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2QuaternionSelectedTranslationCoordinates
open YMGap.Continuum.SU2QuaternionCoordinateConjugation
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

private theorem row_neg_prefix (blocks : Nat) (t : RatTerm) : ∀ q : RatPoly,
    QuaternionPrefixPolynomialEqv blocks
      (q.map fun s => (monoMul t.1 s.1, t.2 * -s.2))
      (q.map fun s => (monoMul t.1 s.1, -(t.2 * s.2)))
  | [] => .nil
  | s :: rest => .cons ⟨Q'.mul_neg_eqv t.2 s.2, fun _ _ => rfl⟩ (row_neg_prefix blocks t rest)

private theorem mul_neg_prefix (blocks : Nat) : ∀ p q : RatPoly,
    QuaternionPrefixPolynomialEqv blocks (polyMul p (polyNeg q)) (polyNeg (polyMul p q))
  | [], _ => .nil
  | t :: rest, q => by
      simpa only [polyMul, polyNeg, List.flatMap_cons, List.map_append, List.map_map,
        Function.comp_apply] using (row_neg_prefix blocks t q).append (mul_neg_prefix blocks rest q)

theorem translatedHeadPolynomial_neg_prefix (blocks : Nat) (translated : PolyQuaternion) :
    ∀ p : RatPoly, QuaternionPrefixPolynomialEqv blocks
      (translatedHeadPolynomial translated (polyNeg p))
      (polyNeg (translatedHeadPolynomial translated p))
  | [] => .nil
  | t :: rest => by
      have ht := mul_neg_prefix blocks
        (translatedHeadMonomial translated (exponentAt t.1 0) (exponentAt t.1 1)
          (exponentAt t.1 2) (exponentAt t.1 3)) (headTailLiftTerm t)
      simpa only [polyNeg, List.map_cons, List.map_nil, List.map_append, translatedHeadPolynomial,
        translatedHeadTerm, headTailLiftTerm, polyAdd] using
        ht.append (translatedHeadPolynomial_neg_prefix blocks translated rest)

theorem applySelectedTranslationStep_neg_prefix {tailBlocks : Nat} (hb : 0 < tailBlocks)
    (step : SelectedTranslationStep tailBlocks) (p : RatPoly) :
    QuaternionPrefixPolynomialEqv (tailBlocks + 1)
      (applySelectedTranslationStep hb step (polyNeg p)) (polyNeg (applySelectedTranslationStep hb step p)) := by
  let head := translationPairHeadPermutation (tailBlocks + 1) step.selected step.selected_lt
  let tail := translationPairTailPermutation (tailBlocks + 1) step.selected step.multiplier
    (by omega) step.selected_lt step.multiplier_lt
  have direct (translated : PolyQuaternion) (q : RatPoly) :
      QuaternionPrefixPolynomialEqv (tailBlocks + 1)
        (restoreTranslationPairPolynomial (tailBlocks + 1) step.selected step.multiplier
          (by omega) step.selected_lt step.multiplier_lt
          (translatedHeadPolynomial translated
            (exposeTranslationPairPolynomial (tailBlocks + 1) step.selected step.multiplier
              (by omega) step.selected_lt step.multiplier_lt (polyNeg q))))
        (polyNeg (restoreTranslationPairPolynomial (tailBlocks + 1) step.selected step.multiplier
          (by omega) step.selected_lt step.multiplier_lt
          (translatedHeadPolynomial translated
            (exposeTranslationPairPolynomial (tailBlocks + 1) step.selected step.multiplier
              (by omega) step.selected_lt step.multiplier_lt q)))) := by
    have h := QuaternionPrefixPolynomialEqv.reindex head (QuaternionPrefixPolynomialEqv.reindex tail
      (translatedHeadPolynomial_neg_prefix (tailBlocks + 1) translated
        (exposeTranslationPairPolynomial (tailBlocks + 1) step.selected step.multiplier
          (by omega) step.selected_lt step.multiplier_lt q)))
    simpa only [exposeTranslationPairPolynomial, restoreTranslationPairPolynomial,
      head, tail, reindexQuaternionPolynomial_neg] using h
  cases hside : step.side <;> cases horientation : step.multiplierOrientation <;>
    simp only [applySelectedTranslationStep, hside, horientation]
  · exact direct leftTranslatedHeadQuaternion p
  · have h := (direct leftTranslatedHeadQuaternion
        (conjugateQuaternionBlockPolynomial (tailBlocks + 1) step.multiplier p)).signSelected
        (quaternionConjugateCoordinateSelector step.multiplier)
    simpa only [selectedLeftInverseTranslatedPolynomial, selectedLeftTranslatedPolynomial,
      conjugateQuaternionBlockPolynomial, signSelectedPolynomial_neg] using h
  · exact direct rightTranslatedHeadQuaternion p
  · have h := (direct rightTranslatedHeadQuaternion
        (conjugateQuaternionBlockPolynomial (tailBlocks + 1) step.multiplier p)).signSelected
        (quaternionConjugateCoordinateSelector step.multiplier)
    simpa only [selectedRightInverseTranslatedPolynomial, selectedRightTranslatedPolynomial,
      conjugateQuaternionBlockPolynomial, signSelectedPolynomial_neg] using h

theorem applySelectedTranslationStep_conj_prefix {tailBlocks : Nat} (hb : 0 < tailBlocks)
    (step : SelectedTranslationStep tailBlocks) (q : PolyQuaternion) :
    QuaternionPrefixPolyQuaternionEqv (tailBlocks + 1)
      (applySelectedTranslationStepsQuaternion hb [step] (PolyQuaternion.conj q))
      (PolyQuaternion.conj (applySelectedTranslationStepsQuaternion hb [step] q)) :=
  ⟨QuaternionPrefixPolynomialEqv.refl _ _,
    applySelectedTranslationStep_neg_prefix hb step q.iPart,
    applySelectedTranslationStep_neg_prefix hb step q.jPart,
    applySelectedTranslationStep_neg_prefix hb step q.kPart⟩

def directStep {tailBlocks : Nat} (step : SelectedTranslationStep tailBlocks) :
    SelectedTranslationStep tailBlocks := { step with multiplierOrientation := .direct }

def coordinateImage {tailBlocks : Nat} (step : SelectedTranslationStep tailBlocks)
    (block : Nat) : PolyQuaternion :=
  if block = step.selected then
    let multiplier := match step.multiplierOrientation with
      | .direct => PolyQuaternion.coordinateVariable step.multiplier
      | .inverse => PolyQuaternion.conj (PolyQuaternion.coordinateVariable step.multiplier)
    match step.side with
    | .left => PolyQuaternion.mul multiplier (PolyQuaternion.coordinateVariable step.selected)
    | .right => PolyQuaternion.mul (PolyQuaternion.coordinateVariable step.selected) multiplier
  else PolyQuaternion.coordinateVariable block

theorem inverse_step_eq_conjugate_direct {tailBlocks : Nat} (hb : 0 < tailBlocks)
    (step : SelectedTranslationStep tailBlocks) (hi : step.multiplierOrientation = .inverse)
    (q : PolyQuaternion) :
    applySelectedTranslationStepsQuaternion hb [step] q =
      conjugateBlockQuaternion (tailBlocks + 1) step.multiplier
        (applySelectedTranslationStepsQuaternion hb [directStep step]
          (conjugateBlockQuaternion (tailBlocks + 1) step.multiplier q)) := by
  cases hs : step.side <;>
    simp only [applySelectedTranslationStepsQuaternion, applySelectedTranslationSteps,
      applySelectedTranslationStep, hi, hs, directStep, selectedLeftInverseTranslatedPolynomial,
      selectedRightInverseTranslatedPolynomial, conjugateBlockQuaternion]

/-- All four ORIGINAL shear cases have their literal coordinate images,
including the unchanged multiplier and every spectator link. -/
theorem applySelectedTranslationStep_coordinate {tailBlocks : Nat} (hb : 0 < tailBlocks)
    (step : SelectedTranslationStep tailBlocks) (block : Nat) (hblock : block < tailBlocks + 1) :
    QuaternionPrefixPolyQuaternionEqv (tailBlocks + 1)
      (applySelectedTranslationStepsQuaternion hb [step] (PolyQuaternion.coordinateVariable block))
      (coordinateImage step block) := by
  cases hi : step.multiplierOrientation with
  | direct =>
      simpa only [coordinateImage, hi, directCoordinateImage] using
        applySelectedTranslationStep_direct_coordinate hb step hi block hblock
  | inverse =>
      rw [inverse_step_eq_conjugate_direct hb step hi]
      have hd := applySelectedTranslationStep_direct_coordinate hb (directStep step) rfl block hblock
      have hc := conjugateBlockQuaternion_coordinate (tailBlocks + 1) step.multiplier block hblock
      by_cases heq : block = step.selected
      · have hne : block ≠ step.multiplier := by
          rw [heq]
          exact step.distinct
        rw [if_neg hne] at hc
        rw [hc]
        have h := conjugateBlockQuaternion_prefix step.multiplier hd
        simp only [directCoordinateImage, directStep, if_pos heq] at h
        have hm := conjugateBlockQuaternion_coordinate (tailBlocks + 1)
          step.multiplier step.multiplier step.multiplier_lt
        have hs := conjugateBlockQuaternion_coordinate (tailBlocks + 1)
          step.multiplier step.selected step.selected_lt
        rw [if_pos rfl] at hm
        rw [if_neg step.distinct] at hs
        cases hside : step.side with
        | left =>
            simp only [hside] at h
            have hp := conjugateBlockQuaternion_mul (tailBlocks + 1) step.multiplier
              (PolyQuaternion.coordinateVariable step.multiplier) (PolyQuaternion.coordinateVariable step.selected)
            rw [hm, hs] at hp
            simpa only [coordinateImage, if_pos heq, hi, directStep, hside] using h.trans hp
        | right =>
            simp only [hside] at h
            have hp := conjugateBlockQuaternion_mul (tailBlocks + 1) step.multiplier
              (PolyQuaternion.coordinateVariable step.selected) (PolyQuaternion.coordinateVariable step.multiplier)
            rw [hs, hm] at hp
            simpa only [coordinateImage, if_pos heq, hi, directStep, hside] using h.trans hp
      · simp only [directCoordinateImage, directStep, if_neg heq] at hd
        by_cases hm : block = step.multiplier
        · rw [if_pos hm] at hc
          rw [hc]
          have hconj := (applySelectedTranslationStep_conj_prefix hb (directStep step)
            (PolyQuaternion.coordinateVariable block)).trans hd.conj
          have h := conjugateBlockQuaternion_prefix step.multiplier hconj
          rw [← hc] at h
          have hfinal := h.trans (conjugateBlockQuaternion_involutive (tailBlocks + 1)
            step.multiplier (PolyQuaternion.coordinateVariable block))
          simpa only [coordinateImage, if_neg heq, hc] using hfinal
        · rw [if_neg hm] at hc
          rw [hc]
          have h := conjugateBlockQuaternion_prefix step.multiplier hd
          rw [hc] at h
          simpa only [coordinateImage, if_neg heq] using h

end YMGap.Continuum.SU2QuaternionInverseTranslationCoordinates

#print axioms YMGap.Continuum.SU2QuaternionInverseTranslationCoordinates.translatedHeadPolynomial_neg_prefix
#print axioms YMGap.Continuum.SU2QuaternionInverseTranslationCoordinates.applySelectedTranslationStep_neg_prefix
#print axioms YMGap.Continuum.SU2QuaternionInverseTranslationCoordinates.applySelectedTranslationStep_conj_prefix
#print axioms YMGap.Continuum.SU2QuaternionInverseTranslationCoordinates.directStep
#print axioms YMGap.Continuum.SU2QuaternionInverseTranslationCoordinates.coordinateImage
#print axioms YMGap.Continuum.SU2QuaternionInverseTranslationCoordinates.inverse_step_eq_conjugate_direct
#print axioms YMGap.Continuum.SU2QuaternionInverseTranslationCoordinates.applySelectedTranslationStep_coordinate
