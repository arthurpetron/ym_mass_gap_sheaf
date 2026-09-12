/-
# Scan-free selected-link coordinate semantics

Expose a selected quaternion, substitute at the head, and restore the original
block order. The resulting direct left/right shear has its literal ordered
quaternion-product image on the selected link and fixes every other link.
The proof works for arbitrary carrier size and selected/multiplier indices.

This is a coordinate pin, not yet the inverse-multiplier pin or the global
temporal-gauge assignment. Those are required before reflected-slab gluing.
-/

import YMGap.Continuum.SU2QuaternionHeadSubstitutionPrefix
import YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslationChain

namespace YMGap.Continuum.SU2QuaternionSelectedTranslationCoordinates

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
open YMGap.Continuum.SU2QuaternionHeadSubstitutionPrefix
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

def headSubstituteQuaternion (translated q : PolyQuaternion) : PolyQuaternion where
  scalar := translatedHeadPolynomial translated q.scalar
  iPart := translatedHeadPolynomial translated q.iPart
  jPart := translatedHeadPolynomial translated q.jPart
  kPart := translatedHeadPolynomial translated q.kPart

theorem headSubstituteQuaternion_prefix {blocks : Nat} (hb : 0 < blocks)
    (translated : PolyQuaternion) {p q : PolyQuaternion}
    (h : QuaternionPrefixPolyQuaternionEqv blocks p q) :
    QuaternionPrefixPolyQuaternionEqv blocks
      (headSubstituteQuaternion translated p) (headSubstituteQuaternion translated q) :=
  ⟨translatedHeadPolynomial_prefix hb translated h.scalar,
    translatedHeadPolynomial_prefix hb translated h.iPart,
    translatedHeadPolynomial_prefix hb translated h.jPart,
    translatedHeadPolynomial_prefix hb translated h.kPart⟩

theorem headSubstituteQuaternion_head (blocks : Nat) (translated : PolyQuaternion) :
    QuaternionPrefixPolyQuaternionEqv blocks
      (headSubstituteQuaternion translated (PolyQuaternion.coordinateVariable 0)) translated := by
  constructor
  · simpa only [headSubstituteQuaternion, PolyQuaternion.coordinateVariable, component, Nat.mul_zero]
      using translatedHeadPolynomial_head_coordinate blocks translated ⟨0, by decide⟩
  · simpa only [headSubstituteQuaternion, PolyQuaternion.coordinateVariable, component, Nat.mul_zero, Nat.zero_add]
      using translatedHeadPolynomial_head_coordinate blocks translated ⟨1, by decide⟩
  · simpa only [headSubstituteQuaternion, PolyQuaternion.coordinateVariable, component, Nat.mul_zero, Nat.zero_add]
      using translatedHeadPolynomial_head_coordinate blocks translated ⟨2, by decide⟩
  · simpa only [headSubstituteQuaternion, PolyQuaternion.coordinateVariable, component, Nat.mul_zero, Nat.zero_add]
      using translatedHeadPolynomial_head_coordinate blocks translated ⟨3, by decide⟩

theorem headSubstituteQuaternion_tail (translated : PolyQuaternion) (block : Nat)
    (hb : block ≠ 0) :
    headSubstituteQuaternion translated (PolyQuaternion.coordinateVariable block) =
      PolyQuaternion.coordinateVariable block := by
  simp only [headSubstituteQuaternion, PolyQuaternion.coordinateVariable,
    translatedHeadPolynomial_tail_coordinate translated (4 * block) (by omega),
    translatedHeadPolynomial_tail_coordinate translated (4 * block + 1) (by omega),
    translatedHeadPolynomial_tail_coordinate translated (4 * block + 2) (by omega),
    translatedHeadPolynomial_tail_coordinate translated (4 * block + 3) (by omega)]

/-- Exact permutation inverse calculation, with no enumerated coordinates. -/
theorem pair_source_inverse {blocks target source : Nat}
    (head tail : QuaternionBlockInvolution blocks) (ht : target < blocks)
    (h : head.map (tail.map target) = source) :
    tail.map (head.map source) = target := by
  rw [← h, head.involutive _ (tail.map_lt target ht), tail.involutive target ht]

def exposedSubstituteRestore {blocks : Nat}
    (head tail : QuaternionBlockInvolution blocks) (translated q : PolyQuaternion) : PolyQuaternion :=
  reindexPolyQuaternion head (reindexPolyQuaternion tail
    (headSubstituteQuaternion translated
      (reindexPolyQuaternion tail (reindexPolyQuaternion head q))))

/-- The selected coordinate is replaced by the supplied quaternion in the
restored block order. This is stronger than equality after integration. -/
theorem exposedSubstituteRestore_selected {blocks selected : Nat} (hb : 0 < blocks)
    (head tail : QuaternionBlockInvolution blocks)
    (hsource : head.map (tail.map 0) = selected) (translated : PolyQuaternion) :
    QuaternionPrefixPolyQuaternionEqv blocks
      (exposedSubstituteRestore head tail translated (PolyQuaternion.coordinateVariable selected))
      (reindexPolyQuaternion head (reindexPolyQuaternion tail translated)) := by
  have he := reindexTwice_coordinateVariable_prefix head tail hb hsource
  have ht := (headSubstituteQuaternion_prefix hb translated he).trans
    (headSubstituteQuaternion_head blocks translated)
  exact reindex_prefix_polyQuaternion head (reindex_prefix_polyQuaternion tail ht)

/-- All other coordinates survive an arbitrary head substitution unchanged. -/
theorem exposedSubstituteRestore_other {blocks selected block : Nat} (hb : 0 < blocks)
    (head tail : QuaternionBlockInvolution blocks)
    (hsource : head.map (tail.map 0) = selected) (hblock : block < blocks)
    (hne : block ≠ selected) (translated : PolyQuaternion) :
    QuaternionPrefixPolyQuaternionEqv blocks
      (exposedSubstituteRestore head tail translated (PolyQuaternion.coordinateVariable block))
      (PolyQuaternion.coordinateVariable block) := by
  let target := tail.map (head.map block)
  have ht : target < blocks := tail.map_lt _ (head.map_lt block hblock)
  have hmap : head.map (tail.map target) = block := by
    dsimp [target]
    rw [tail.involutive _ (head.map_lt block hblock), head.involutive block hblock]
  have htne : target ≠ 0 := by
    intro heq
    rw [heq, hsource] at hmap
    exact hne hmap.symm
  have he := reindexTwice_coordinateVariable_prefix head tail ht hmap
  have hs := headSubstituteQuaternion_prefix hb translated he
  rw [headSubstituteQuaternion_tail translated target htne] at hs
  exact (reindex_prefix_polyQuaternion head (reindex_prefix_polyQuaternion tail hs)).trans
    (reindexTwice_coordinateVariable_prefix tail head hblock (show tail.map (head.map block) = target from rfl))

def directCoordinateImage {tailBlocks : Nat} (step : SelectedTranslationStep tailBlocks)
    (block : Nat) : PolyQuaternion :=
  if block = step.selected then
    match step.side with
    | .left => PolyQuaternion.mul (PolyQuaternion.coordinateVariable step.multiplier)
        (PolyQuaternion.coordinateVariable step.selected)
    | .right => PolyQuaternion.mul (PolyQuaternion.coordinateVariable step.selected)
        (PolyQuaternion.coordinateVariable step.multiplier)
  else PolyQuaternion.coordinateVariable block

/-- The ORIGINAL direct shear, at arbitrary valid indices, has exactly its
ordered left/right product image. No finite coordinate check is a premise. -/
theorem applySelectedTranslationStep_direct_coordinate {tailBlocks : Nat}
    (hb : 0 < tailBlocks) (step : SelectedTranslationStep tailBlocks)
    (hd : step.multiplierOrientation = .direct) (block : Nat) (hblock : block < tailBlocks + 1) :
    QuaternionPrefixPolyQuaternionEqv (tailBlocks + 1)
      (applySelectedTranslationStepsQuaternion hb [step] (PolyQuaternion.coordinateVariable block))
      (directCoordinateImage step block) := by
  let head := translationPairHeadPermutation (tailBlocks + 1) step.selected step.selected_lt
  let tail := translationPairTailPermutation (tailBlocks + 1) step.selected step.multiplier
    (by omega) step.selected_lt step.multiplier_lt
  have hz : head.map (tail.map 0) = step.selected :=
    exposedTranslationPair_source_zero _ _ _ (by omega) step.selected_lt step.multiplier_lt step.distinct
  have ho : head.map (tail.map 1) = step.multiplier :=
    exposedTranslationPair_source_one _ _ _ (by omega) step.selected_lt step.multiplier_lt
  by_cases heq : block = step.selected
  · subst block
    have hzback := pair_source_inverse head tail (by omega : 0 < tailBlocks + 1) hz
    have hoback := pair_source_inverse head tail (by omega : 1 < tailBlocks + 1) ho
    have hselected := reindexTwice_coordinateVariable_prefix tail head step.selected_lt hzback
    have hmultiplier := reindexTwice_coordinateVariable_prefix tail head step.multiplier_lt hoback
    cases hside : step.side with
    | left =>
        have h := exposedSubstituteRestore_selected (by omega : 0 < tailBlocks + 1)
          head tail hz leftTranslatedHeadQuaternion
        have hm := hmultiplier.mul hselected
        simp only [leftTranslatedHeadQuaternion, reindexPolyQuaternion_mul] at h
        have hfinal := h.trans hm
        simpa only [applySelectedTranslationStepsQuaternion, applySelectedTranslationSteps,
          applySelectedTranslationStep, hd, hside, selectedLeftTranslatedPolynomial,
          exposeTranslationPairPolynomial, restoreTranslationPairPolynomial,
          exposedSubstituteRestore, headSubstituteQuaternion, reindexPolyQuaternion,
          head, tail, directCoordinateImage, if_pos rfl] using hfinal
    | right =>
        have h := exposedSubstituteRestore_selected (by omega : 0 < tailBlocks + 1)
          head tail hz rightTranslatedHeadQuaternion
        have hm := hselected.mul hmultiplier
        simp only [rightTranslatedHeadQuaternion, reindexPolyQuaternion_mul] at h
        have hfinal := h.trans hm
        simpa only [applySelectedTranslationStepsQuaternion, applySelectedTranslationSteps,
          applySelectedTranslationStep, hd, hside, selectedRightTranslatedPolynomial,
          exposeTranslationPairPolynomial, restoreTranslationPairPolynomial,
          exposedSubstituteRestore, headSubstituteQuaternion, reindexPolyQuaternion,
          head, tail, directCoordinateImage, if_pos rfl] using hfinal
  · cases hside : step.side with
    | left =>
        have h := exposedSubstituteRestore_other (by omega : 0 < tailBlocks + 1)
          head tail hz hblock heq leftTranslatedHeadQuaternion
        simpa only [applySelectedTranslationStepsQuaternion, applySelectedTranslationSteps,
          applySelectedTranslationStep, hd, hside, selectedLeftTranslatedPolynomial,
          exposeTranslationPairPolynomial, restoreTranslationPairPolynomial,
          exposedSubstituteRestore, headSubstituteQuaternion, reindexPolyQuaternion,
          head, tail, directCoordinateImage, if_neg heq] using h
    | right =>
        have h := exposedSubstituteRestore_other (by omega : 0 < tailBlocks + 1)
          head tail hz hblock heq rightTranslatedHeadQuaternion
        simpa only [applySelectedTranslationStepsQuaternion, applySelectedTranslationSteps,
          applySelectedTranslationStep, hd, hside, selectedRightTranslatedPolynomial,
          exposeTranslationPairPolynomial, restoreTranslationPairPolynomial,
          exposedSubstituteRestore, headSubstituteQuaternion, reindexPolyQuaternion,
          head, tail, directCoordinateImage, if_neg heq] using h

/-- Prefix transport for every original shear, including inverse multipliers.
This is a congruence theorem; the inverse coordinate IMAGE still needs a pin. -/
theorem applySelectedTranslationStep_prefix {tailBlocks : Nat} (hb : 0 < tailBlocks)
    (step : SelectedTranslationStep tailBlocks) {p q : RatPoly}
    (h : QuaternionPrefixPolynomialEqv (tailBlocks + 1) p q) :
    QuaternionPrefixPolynomialEqv (tailBlocks + 1)
      (applySelectedTranslationStep hb step p) (applySelectedTranslationStep hb step q) := by
  let head := translationPairHeadPermutation (tailBlocks + 1) step.selected step.selected_lt
  let tail := translationPairTailPermutation (tailBlocks + 1) step.selected step.multiplier
    (by omega) step.selected_lt step.multiplier_lt
  have direct {r s : RatPoly} (he : QuaternionPrefixPolynomialEqv (tailBlocks + 1) r s)
      (translated : PolyQuaternion) :
      QuaternionPrefixPolynomialEqv (tailBlocks + 1)
        (restoreTranslationPairPolynomial (tailBlocks + 1) step.selected step.multiplier
          (by omega) step.selected_lt step.multiplier_lt
          (translatedHeadPolynomial translated
            (exposeTranslationPairPolynomial (tailBlocks + 1) step.selected step.multiplier
              (by omega) step.selected_lt step.multiplier_lt r)))
        (restoreTranslationPairPolynomial (tailBlocks + 1) step.selected step.multiplier
          (by omega) step.selected_lt step.multiplier_lt
          (translatedHeadPolynomial translated
            (exposeTranslationPairPolynomial (tailBlocks + 1) step.selected step.multiplier
              (by omega) step.selected_lt step.multiplier_lt s))) :=
    QuaternionPrefixPolynomialEqv.reindex head (QuaternionPrefixPolynomialEqv.reindex tail
      (translatedHeadPolynomial_prefix (by omega) translated
        (QuaternionPrefixPolynomialEqv.reindex tail (QuaternionPrefixPolynomialEqv.reindex head he))))
  have hi := h.signSelected (quaternionConjugateCoordinateSelector step.multiplier)
  cases hside : step.side <;> cases horientation : step.multiplierOrientation <;>
    simp only [applySelectedTranslationStep, hside, horientation]
  · exact direct h leftTranslatedHeadQuaternion
  · exact (direct hi leftTranslatedHeadQuaternion).signSelected
      (quaternionConjugateCoordinateSelector step.multiplier)
  · exact direct h rightTranslatedHeadQuaternion
  · exact (direct hi rightTranslatedHeadQuaternion).signSelected
      (quaternionConjugateCoordinateSelector step.multiplier)

/-- All subsequent shears preserve a proved coordinate/word pin, with no
assumption that their selected blocks are distinct from earlier ones. -/
theorem applySelectedTranslationSteps_prefix {tailBlocks : Nat} (hb : 0 < tailBlocks) :
    ∀ (steps : List (SelectedTranslationStep tailBlocks)) {p q : RatPoly},
      QuaternionPrefixPolynomialEqv (tailBlocks + 1) p q →
      QuaternionPrefixPolynomialEqv (tailBlocks + 1)
        (applySelectedTranslationSteps hb steps p) (applySelectedTranslationSteps hb steps q)
  | [], _, _, h => h
  | step :: rest, _, _, h => applySelectedTranslationSteps_prefix hb rest
      (applySelectedTranslationStep_prefix hb step h)

theorem applySelectedTranslationStepsQuaternion_prefix {tailBlocks : Nat} (hb : 0 < tailBlocks)
    (steps : List (SelectedTranslationStep tailBlocks)) {p q : PolyQuaternion}
    (h : QuaternionPrefixPolyQuaternionEqv (tailBlocks + 1) p q) :
    QuaternionPrefixPolyQuaternionEqv (tailBlocks + 1)
      (applySelectedTranslationStepsQuaternion hb steps p) (applySelectedTranslationStepsQuaternion hb steps q) :=
  ⟨applySelectedTranslationSteps_prefix hb steps h.scalar,
    applySelectedTranslationSteps_prefix hb steps h.iPart,
    applySelectedTranslationSteps_prefix hb steps h.jPart,
    applySelectedTranslationSteps_prefix hb steps h.kPart⟩

end YMGap.Continuum.SU2QuaternionSelectedTranslationCoordinates

#print axioms YMGap.Continuum.SU2QuaternionSelectedTranslationCoordinates.headSubstituteQuaternion
#print axioms YMGap.Continuum.SU2QuaternionSelectedTranslationCoordinates.headSubstituteQuaternion_prefix
#print axioms YMGap.Continuum.SU2QuaternionSelectedTranslationCoordinates.headSubstituteQuaternion_head
#print axioms YMGap.Continuum.SU2QuaternionSelectedTranslationCoordinates.headSubstituteQuaternion_tail
#print axioms YMGap.Continuum.SU2QuaternionSelectedTranslationCoordinates.pair_source_inverse
#print axioms YMGap.Continuum.SU2QuaternionSelectedTranslationCoordinates.exposedSubstituteRestore
#print axioms YMGap.Continuum.SU2QuaternionSelectedTranslationCoordinates.exposedSubstituteRestore_selected
#print axioms YMGap.Continuum.SU2QuaternionSelectedTranslationCoordinates.exposedSubstituteRestore_other
#print axioms YMGap.Continuum.SU2QuaternionSelectedTranslationCoordinates.directCoordinateImage
#print axioms YMGap.Continuum.SU2QuaternionSelectedTranslationCoordinates.applySelectedTranslationStep_direct_coordinate
#print axioms YMGap.Continuum.SU2QuaternionSelectedTranslationCoordinates.applySelectedTranslationStep_prefix
#print axioms YMGap.Continuum.SU2QuaternionSelectedTranslationCoordinates.applySelectedTranslationSteps_prefix
#print axioms YMGap.Continuum.SU2QuaternionSelectedTranslationCoordinates.applySelectedTranslationStepsQuaternion_prefix
