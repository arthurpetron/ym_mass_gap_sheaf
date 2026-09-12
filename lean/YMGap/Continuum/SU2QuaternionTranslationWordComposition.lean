/-
# Coefficient-sensitive composition of the original shear chains

Identity reindexing gives one common carrier length, including empty chains.
The resulting relation retains every coefficient probe on that carrier and
is respected by the ORIGINAL chain action, ordered multiplication and star.
This is algebra for the temporal-ledger image proof, not a Haar-only equality
or an assumed change-of-variables certificate. No physical gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabTemporalGaugeFixedCoordinates

namespace YMGap.Continuum.SU2QuaternionTranslationWordComposition

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslation
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2QuaternionHeadSubstitutionPrefix
open YMGap.Continuum.SU2QuaternionSelectedTranslationCoordinates
open YMGap.Continuum.SU2QuaternionInverseTranslationCoordinates
open YMGap.Continuum.SU2QuaternionTranslationCoordinateCoefficients
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabTemporalGaugeFixedCoordinates

theorem reindex_coeffEqv {blocks : Nat} (permutation : QuaternionBlockInvolution blocks)
    {p q : PolyQuaternion} (h : PolyQuaternionCoeffEqv p q) :
    PolyQuaternionCoeffEqv (reindexPolyQuaternion permutation p) (reindexPolyQuaternion permutation q) :=
  ⟨RatPolyCoeffEqv.reindex permutation h.scalar, RatPolyCoeffEqv.reindex permutation h.iPart,
    RatPolyCoeffEqv.reindex permutation h.jPart, RatPolyCoeffEqv.reindex permutation h.kPart⟩

/-- All coefficient probes after common carrier padding. The carrier size
is explicit; this relation makes no assertion about variables outside it. -/
def PaddedQuaternionCoeffEqv (blocks : Nat) (p q : PolyQuaternion) : Prop :=
  PolyQuaternionCoeffEqv
    (reindexPolyQuaternion (identityQuaternionBlockInvolution blocks) p)
    (reindexPolyQuaternion (identityQuaternionBlockInvolution blocks) q)

namespace PaddedQuaternionCoeffEqv

theorem refl (blocks : Nat) (p : PolyQuaternion) : PaddedQuaternionCoeffEqv blocks p p :=
  PolyQuaternionCoeffEqv.refl _

theorem symm {blocks : Nat} {p q : PolyQuaternion} (h : PaddedQuaternionCoeffEqv blocks p q) :
    PaddedQuaternionCoeffEqv blocks q p := PolyQuaternionCoeffEqv.symm h

theorem trans {blocks : Nat} {p q r : PolyQuaternion}
    (hp : PaddedQuaternionCoeffEqv blocks p q) (hq : PaddedQuaternionCoeffEqv blocks q r) :
    PaddedQuaternionCoeffEqv blocks p r := PolyQuaternionCoeffEqv.trans hp hq

theorem of_coeff {blocks : Nat} {p q : PolyQuaternion} (h : PolyQuaternionCoeffEqv p q) :
    PaddedQuaternionCoeffEqv blocks p q := reindex_coeffEqv _ h

theorem of_prefix {blocks : Nat} {p q : PolyQuaternion}
    (h : QuaternionPrefixPolyQuaternionEqv blocks p q) : PaddedQuaternionCoeffEqv blocks p q :=
  reindex_prefix_coeffEqv _ h

theorem mul {blocks : Nat} {p p' q q' : PolyQuaternion}
    (hp : PaddedQuaternionCoeffEqv blocks p p') (hq : PaddedQuaternionCoeffEqv blocks q q') :
    PaddedQuaternionCoeffEqv blocks (PolyQuaternion.mul p q) (PolyQuaternion.mul p' q') := by
  unfold PaddedQuaternionCoeffEqv
  rw [reindexPolyQuaternion_mul, reindexPolyQuaternion_mul]
  exact PolyQuaternionCoeffEqv.mul hp hq

theorem conj {blocks : Nat} {p q : PolyQuaternion} (h : PaddedQuaternionCoeffEqv blocks p q) :
    PaddedQuaternionCoeffEqv blocks (PolyQuaternion.conj p) (PolyQuaternion.conj q) := by
  unfold PaddedQuaternionCoeffEqv
  rw [reindexPolyQuaternion_conj, reindexPolyQuaternion_conj]
  exact PolyQuaternionCoeffEqv.conj h

/-- The original chain respects common-carrier coefficient equality. Both
empty and nonempty chains are covered without erasing padding by fiat. -/
theorem applySteps {tailBlocks : Nat} (hb : 0 < tailBlocks)
    (steps : List (SelectedTranslationStep tailBlocks)) {p q : PolyQuaternion}
    (h : PaddedQuaternionCoeffEqv (tailBlocks + 1) p q) :
    PaddedQuaternionCoeffEqv (tailBlocks + 1)
      (applySelectedTranslationStepsQuaternion hb steps p)
      (applySelectedTranslationStepsQuaternion hb steps q) := by
  have hp := of_prefix (applySelectedTranslationStepsQuaternion_prefix hb steps
    (identityReindexPolyQuaternion_prefix (tailBlocks + 1) p))
  have hq := of_prefix (applySelectedTranslationStepsQuaternion_prefix hb steps
    (identityReindexPolyQuaternion_prefix (tailBlocks + 1) q))
  exact hp.symm.trans ((of_coeff (applySelectedTranslationStepsQuaternion_coeffEqv hb steps h)).trans hq)

end PaddedQuaternionCoeffEqv

theorem applySteps_mul {tailBlocks : Nat} (hb : 0 < tailBlocks)
    (steps : List (SelectedTranslationStep tailBlocks)) (p q : PolyQuaternion) :
    PaddedQuaternionCoeffEqv (tailBlocks + 1)
      (applySelectedTranslationStepsQuaternion hb steps (PolyQuaternion.mul p q))
      (PolyQuaternion.mul (applySelectedTranslationStepsQuaternion hb steps p)
        (applySelectedTranslationStepsQuaternion hb steps q)) :=
  .of_coeff (applySelectedTranslationStepsQuaternion_mul hb steps p q)

theorem applySteps_conj {tailBlocks : Nat} (hb : 0 < tailBlocks)
    (steps : List (SelectedTranslationStep tailBlocks)) (q : PolyQuaternion) :
    PaddedQuaternionCoeffEqv (tailBlocks + 1)
      (applySelectedTranslationStepsQuaternion hb steps (PolyQuaternion.conj q))
      (PolyQuaternion.conj (applySelectedTranslationStepsQuaternion hb steps q)) :=
  .of_coeff (applySelectedTranslationStepsQuaternion_conj hb steps q)

theorem applySteps_fixed_coordinate {tailBlocks : Nat} (hb : 0 < tailBlocks)
    (steps : List (SelectedTranslationStep tailBlocks)) (block : Nat) (hi : block < tailBlocks + 1)
    (hn : ∀ step, step ∈ steps → block ≠ step.selected) :
    PaddedQuaternionCoeffEqv (tailBlocks + 1)
      (applySelectedTranslationStepsQuaternion hb steps (PolyQuaternion.coordinateVariable block))
      (PolyQuaternion.coordinateVariable block) :=
  .of_prefix (applySteps_fixes_coordinate hb block hi steps hn)

theorem applyStep_coordinate {tailBlocks : Nat} (hb : 0 < tailBlocks)
    (step : SelectedTranslationStep tailBlocks) (block : Nat) (hi : block < tailBlocks + 1) :
    PaddedQuaternionCoeffEqv (tailBlocks + 1)
      (applySelectedTranslationStepsQuaternion hb [step] (PolyQuaternion.coordinateVariable block))
      (coordinateImage step block) :=
  (PaddedQuaternionCoeffEqv.of_coeff (applySelectedTranslationStep_coordinate_coeffEqv hb step block hi)).trans
    (.of_prefix (identityReindexPolyQuaternion_prefix _ _))

theorem applySteps_append_polynomial {tailBlocks : Nat} (hb : 0 < tailBlocks) :
    ∀ (first rest : List (SelectedTranslationStep tailBlocks)) (p : RatPoly),
      applySelectedTranslationSteps hb (first ++ rest) p =
        applySelectedTranslationSteps hb rest (applySelectedTranslationSteps hb first p)
  | [], _, _ => rfl
  | step :: first, rest, p => applySteps_append_polynomial hb first rest (applySelectedTranslationStep hb step p)

theorem applySteps_append {tailBlocks : Nat} (hb : 0 < tailBlocks)
    (first rest : List (SelectedTranslationStep tailBlocks)) (p : PolyQuaternion) :
    applySelectedTranslationStepsQuaternion hb (first ++ rest) p =
      applySelectedTranslationStepsQuaternion hb rest (applySelectedTranslationStepsQuaternion hb first p) := by
  cases p
  simp only [applySelectedTranslationStepsQuaternion, applySteps_append_polynomial]

private theorem reindex_one_prefix {blocks : Nat} (permutation : QuaternionBlockInvolution blocks) :
    QuaternionPrefixPolynomialEqv blocks (reindexQuaternionPolynomial permutation polyOne) polyOne := by
  apply QuaternionPrefixPolynomialEqv.cons
  · constructor
    · exact Q'.eqv_refl 1
    · intro i hi
      exact exponentAt_reindexQuaternionExponents permutation [] hi
  · exact .nil

private theorem head_one_prefix (blocks : Nat) (q : PolyQuaternion) :
    QuaternionPrefixPolynomialEqv blocks (translatedHeadPolynomial q polyOne) polyOne := by
  change QuaternionPrefixPolynomialEqv blocks [([0, 0, 0, 0], 1)] [([], 1)]
  apply QuaternionPrefixPolynomialEqv.cons
  · constructor
    · exact Q'.eqv_refl 1
    · intro i _
      cases i with
      | zero => rfl
      | succ i => cases i with
        | zero => rfl
        | succ i => cases i with
          | zero => rfl
          | succ i => cases i <;> rfl
  · exact .nil

private theorem sign_one (coordinates : Nat) (selected : Nat → Bool) :
    signSelectedPolynomial coordinates selected polyOne = polyOne := by
  have hp : selectedExponentParity coordinates selected [] = false := by
    induction coordinates with
    | zero => rfl
    | succ n ih =>
        simp only [selectedExponentParity, List.range_succ, List.foldl_append,
          List.foldl_cons, List.foldl_nil]
        change (if selected n then xor (selectedExponentParity n selected []) false
          else selectedExponentParity n selected []) = false
        rw [ih]
        cases selected n <;> rfl
  simp only [signSelectedPolynomial, polyOne, List.map_cons, List.map_nil, signSelectedTerm, hp,
    Bool.false_eq_true, if_false]

theorem applyStep_one_prefix {tailBlocks : Nat} (hb : 0 < tailBlocks)
    (step : SelectedTranslationStep tailBlocks) :
    QuaternionPrefixPolyQuaternionEqv (tailBlocks + 1)
      (applySelectedTranslationStepsQuaternion hb [step] PolyQuaternion.one) PolyQuaternion.one := by
  let head := translationPairHeadPermutation (tailBlocks + 1) step.selected step.selected_lt
  let tail := translationPairTailPermutation (tailBlocks + 1) step.selected step.multiplier
    (by omega) step.selected_lt step.multiplier_lt
  have direct (q : PolyQuaternion) : QuaternionPrefixPolynomialEqv (tailBlocks + 1)
      (restoreTranslationPairPolynomial (tailBlocks + 1) step.selected step.multiplier
        (by omega) step.selected_lt step.multiplier_lt
        (translatedHeadPolynomial q (exposeTranslationPairPolynomial (tailBlocks + 1)
          step.selected step.multiplier (by omega) step.selected_lt step.multiplier_lt polyOne))) polyOne := by
    have hi := (QuaternionPrefixPolynomialEqv.reindex tail (reindex_one_prefix head)).trans
      (reindex_one_prefix tail)
    have hh := (translatedHeadPolynomial_prefix (by omega) q hi).trans (head_one_prefix _ q)
    exact (QuaternionPrefixPolynomialEqv.reindex head
      ((QuaternionPrefixPolynomialEqv.reindex tail hh).trans (reindex_one_prefix tail))).trans
        (reindex_one_prefix head)
  have scalar : QuaternionPrefixPolynomialEqv (tailBlocks + 1)
      (applySelectedTranslationStep hb step polyOne) polyOne := by
    cases hs : step.side <;> cases ho : step.multiplierOrientation
    · simpa only [applySelectedTranslationStep, hs, ho, selectedLeftTranslatedPolynomial]
        using direct leftTranslatedHeadQuaternion
    · have h := (direct leftTranslatedHeadQuaternion).signSelected (quaternionConjugateCoordinateSelector step.multiplier)
      simpa only [applySelectedTranslationStep, hs, ho, selectedLeftInverseTranslatedPolynomial,
        conjugateQuaternionBlockPolynomial, sign_one] using h
    · simpa only [applySelectedTranslationStep, hs, ho, selectedRightTranslatedPolynomial]
        using direct rightTranslatedHeadQuaternion
    · have h := (direct rightTranslatedHeadQuaternion).signSelected (quaternionConjugateCoordinateSelector step.multiplier)
      simpa only [applySelectedTranslationStep, hs, ho, selectedRightInverseTranslatedPolynomial,
        conjugateQuaternionBlockPolynomial, sign_one] using h
  have zero : applySelectedTranslationStep hb step polyZero = polyZero := by
    cases hs : step.side <;> cases ho : step.multiplierOrientation <;>
      simp only [applySelectedTranslationStep, hs, ho] <;> rfl
  have hz : QuaternionPrefixPolynomialEqv (tailBlocks + 1)
      (applySelectedTranslationStep hb step polyZero) polyZero := by
    rw [zero]
    exact .nil
  exact ⟨scalar, hz, hz, hz⟩

/-- Constants, including missing-endpoint identity fallbacks, survive every
original shear chain. -/
theorem applySteps_one_prefix {tailBlocks : Nat} (hb : 0 < tailBlocks) :
    ∀ steps : List (SelectedTranslationStep tailBlocks),
      QuaternionPrefixPolyQuaternionEqv (tailBlocks + 1)
        (applySelectedTranslationStepsQuaternion hb steps PolyQuaternion.one) PolyQuaternion.one
  | [] => .refl _ _
  | step :: rest => (applySelectedTranslationStepsQuaternion_prefix hb rest
      (applyStep_one_prefix hb step)).trans (applySteps_one_prefix hb rest)

theorem applySteps_one {tailBlocks : Nat} (hb : 0 < tailBlocks)
    (steps : List (SelectedTranslationStep tailBlocks)) :
    PaddedQuaternionCoeffEqv (tailBlocks + 1)
      (applySelectedTranslationStepsQuaternion hb steps PolyQuaternion.one) PolyQuaternion.one :=
  .of_prefix (applySteps_one_prefix hb steps)

end YMGap.Continuum.SU2QuaternionTranslationWordComposition

#print axioms YMGap.Continuum.SU2QuaternionTranslationWordComposition.reindex_coeffEqv
#print axioms YMGap.Continuum.SU2QuaternionTranslationWordComposition.PaddedQuaternionCoeffEqv
#print axioms YMGap.Continuum.SU2QuaternionTranslationWordComposition.PaddedQuaternionCoeffEqv.refl
#print axioms YMGap.Continuum.SU2QuaternionTranslationWordComposition.PaddedQuaternionCoeffEqv.symm
#print axioms YMGap.Continuum.SU2QuaternionTranslationWordComposition.PaddedQuaternionCoeffEqv.trans
#print axioms YMGap.Continuum.SU2QuaternionTranslationWordComposition.PaddedQuaternionCoeffEqv.of_coeff
#print axioms YMGap.Continuum.SU2QuaternionTranslationWordComposition.PaddedQuaternionCoeffEqv.of_prefix
#print axioms YMGap.Continuum.SU2QuaternionTranslationWordComposition.PaddedQuaternionCoeffEqv.mul
#print axioms YMGap.Continuum.SU2QuaternionTranslationWordComposition.PaddedQuaternionCoeffEqv.conj
#print axioms YMGap.Continuum.SU2QuaternionTranslationWordComposition.PaddedQuaternionCoeffEqv.applySteps
#print axioms YMGap.Continuum.SU2QuaternionTranslationWordComposition.applySteps_mul
#print axioms YMGap.Continuum.SU2QuaternionTranslationWordComposition.applySteps_conj
#print axioms YMGap.Continuum.SU2QuaternionTranslationWordComposition.applySteps_fixed_coordinate
#print axioms YMGap.Continuum.SU2QuaternionTranslationWordComposition.applyStep_coordinate
#print axioms YMGap.Continuum.SU2QuaternionTranslationWordComposition.applySteps_append_polynomial
#print axioms YMGap.Continuum.SU2QuaternionTranslationWordComposition.applySteps_append
#print axioms YMGap.Continuum.SU2QuaternionTranslationWordComposition.applyStep_one_prefix
#print axioms YMGap.Continuum.SU2QuaternionTranslationWordComposition.applySteps_one_prefix
#print axioms YMGap.Continuum.SU2QuaternionTranslationWordComposition.applySteps_one
