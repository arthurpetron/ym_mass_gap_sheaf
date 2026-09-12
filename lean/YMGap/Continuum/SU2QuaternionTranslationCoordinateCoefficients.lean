/-
# Coefficient-sensitive coordinate pins for arbitrary selected shears

Every original shear returns monomials padded to the full carrier length.
Consequently its proved coordinate-prefix image becomes coefficient-probe
equality to the identity-reindexed literal product. This supplies the exact
relation consumed by the existing word/product composition theorems, with
no finite coordinate certificate or arbitrary-insertion information loss.
Temporal-ledger geometry, common-assignment composition and slab RP remain open.
-/

import YMGap.Continuum.SU2QuaternionInverseTranslationCoordinates

namespace YMGap.Continuum.SU2QuaternionTranslationCoordinateCoefficients

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslation
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2QuaternionHeadSubstitutionPrefix
open YMGap.Continuum.SU2QuaternionSelectedTranslationCoordinates
open YMGap.Continuum.SU2QuaternionInverseTranslationCoordinates
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

theorem prefix_coeffEqv_of_lengths {blocks : Nat} {p q : RatPoly}
    (h : QuaternionPrefixPolynomialEqv blocks p q)
    (hp : ∀ t, t ∈ p → t.1.length = 4 * blocks)
    (hq : ∀ t, t ∈ q → t.1.length = 4 * blocks) : RatPolyCoeffEqv p q := by
  induction h with
  | nil => exact RatPolyCoeffEqv.refl []
  | @cons s t restS restT ht _ ih =>
      have hm : s.1 = t.1 := by
        apply natList_eq_of_length_getD
        · exact (hp s List.mem_cons_self).trans (hq t List.mem_cons_self).symm
        · intro i hi
          exact ht.exponent i (by rw [hp s List.mem_cons_self] at hi; exact hi)
      intro weight
      change (s.2 * weight s.1 + ratWeightedSum weight restS).eqv
        (t.2 * weight t.1 + ratWeightedSum weight restT)
      rw [hm]
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ _ ht.coefficient)
        (ih (fun u hu => hp u (List.mem_cons_of_mem s hu))
          (fun u hu => hq u (List.mem_cons_of_mem t hu)) weight)

theorem reindex_term_length {blocks : Nat} (permutation : QuaternionBlockInvolution blocks)
    (p : RatPoly) (t : RatTerm) (ht : t ∈ reindexQuaternionPolynomial permutation p) :
    t.1.length = 4 * blocks := by
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp ht
  exact reindexQuaternionExponents_length permutation s.1

private theorem sign_term_length {n : Nat} (coordinates : Nat) (selected : Nat → Bool)
    {p : RatPoly} (hp : ∀ t, t ∈ p → t.1.length = n)
    (t : RatTerm) (ht : t ∈ signSelectedPolynomial coordinates selected p) : t.1.length = n := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

theorem applySelectedTranslationStep_term_length {tailBlocks : Nat} (hb : 0 < tailBlocks)
    (step : SelectedTranslationStep tailBlocks) (p : RatPoly) (t : RatTerm)
    (ht : t ∈ applySelectedTranslationStep hb step p) : t.1.length = 4 * (tailBlocks + 1) := by
  let head := translationPairHeadPermutation (tailBlocks + 1) step.selected step.selected_lt
  cases hs : step.side <;> cases ho : step.multiplierOrientation
  · simp only [applySelectedTranslationStep, hs, ho, selectedLeftTranslatedPolynomial,
      restoreTranslationPairPolynomial] at ht
    exact reindex_term_length head _ t ht
  · simp only [applySelectedTranslationStep, hs, ho, selectedLeftInverseTranslatedPolynomial,
      conjugateQuaternionBlockPolynomial] at ht
    exact sign_term_length _ _ (fun u hu => reindex_term_length head _ u hu) t ht
  · simp only [applySelectedTranslationStep, hs, ho, selectedRightTranslatedPolynomial,
      restoreTranslationPairPolynomial] at ht
    exact reindex_term_length head _ t ht
  · simp only [applySelectedTranslationStep, hs, ho, selectedRightInverseTranslatedPolynomial,
      conjugateQuaternionBlockPolynomial] at ht
    exact sign_term_length _ _ (fun u hu => reindex_term_length head _ u hu) t ht

/-- One actual shear absorbs padding differences into full coefficient
equality, including inverse cases. -/
theorem applySelectedTranslationStep_prefix_coeffEqv {tailBlocks : Nat} (hb : 0 < tailBlocks)
    (step : SelectedTranslationStep tailBlocks) {p q : RatPoly}
    (h : QuaternionPrefixPolynomialEqv (tailBlocks + 1) p q) :
    RatPolyCoeffEqv (applySelectedTranslationStep hb step p) (applySelectedTranslationStep hb step q) :=
  prefix_coeffEqv_of_lengths (applySelectedTranslationStep_prefix hb step h)
    (applySelectedTranslationStep_term_length hb step p) (applySelectedTranslationStep_term_length hb step q)

/-- Coefficient equality to the padded ORIGINAL ordered coordinate image,
for every left/right direct/inverse shear at arbitrary valid indices. -/
theorem applySelectedTranslationStep_coordinate_coeffEqv {tailBlocks : Nat} (hb : 0 < tailBlocks)
    (step : SelectedTranslationStep tailBlocks) (block : Nat) (hblock : block < tailBlocks + 1) :
    PolyQuaternionCoeffEqv
      (applySelectedTranslationStepsQuaternion hb [step] (PolyQuaternion.coordinateVariable block))
      (reindexPolyQuaternion (identityQuaternionBlockInvolution (tailBlocks + 1))
        (coordinateImage step block)) := by
  have h := applySelectedTranslationStep_coordinate hb step block hblock
  have lift {p q : RatPoly} (hp : QuaternionPrefixPolynomialEqv (tailBlocks + 1)
      (applySelectedTranslationStep hb step p) q) :
      RatPolyCoeffEqv (applySelectedTranslationStep hb step p)
        (reindexQuaternionPolynomial (identityQuaternionBlockInvolution (tailBlocks + 1)) q) :=
    prefix_coeffEqv_of_lengths
      (hp.trans (prefix_symm (identityReindexQuaternionPolynomial_prefix (tailBlocks + 1) q)))
      (applySelectedTranslationStep_term_length hb step p)
      (reindex_term_length (identityQuaternionBlockInvolution (tailBlocks + 1)) q)
  exact ⟨lift h.scalar, lift h.iPart, lift h.jPart, lift h.kPart⟩

end YMGap.Continuum.SU2QuaternionTranslationCoordinateCoefficients

#print axioms YMGap.Continuum.SU2QuaternionTranslationCoordinateCoefficients.prefix_coeffEqv_of_lengths
#print axioms YMGap.Continuum.SU2QuaternionTranslationCoordinateCoefficients.reindex_term_length
#print axioms YMGap.Continuum.SU2QuaternionTranslationCoordinateCoefficients.applySelectedTranslationStep_term_length
#print axioms YMGap.Continuum.SU2QuaternionTranslationCoordinateCoefficients.applySelectedTranslationStep_prefix_coeffEqv
#print axioms YMGap.Continuum.SU2QuaternionTranslationCoordinateCoefficients.applySelectedTranslationStep_coordinate_coeffEqv
