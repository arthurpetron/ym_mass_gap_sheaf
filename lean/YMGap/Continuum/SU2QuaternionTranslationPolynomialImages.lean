/-
# Original shear-chain images of character observables

Common-padding coefficient equality extends from quaternion words to every
spin character, finite signed sum and finite product. These are the actual
operations in the slab observable, not a replacement observable algebra.
The supported Haar corollary removes only the explicitly tracked padding.
No positivity, spectral estimate or continuum construction is asserted.
-/

import YMGap.Continuum.SU2QuaternionTranslationWordComposition
import YMGap.Continuum.BF4ExactSlabObservableHaarForm

namespace YMGap.Continuum.SU2QuaternionTranslationPolynomialImages

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2QuaternionHeadSubstitutionPrefix
open YMGap.Continuum.SU2QuaternionTranslationCoordinateCoefficients
open YMGap.Continuum.SU2QuaternionTranslationWordComposition
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation

def PaddedPolynomialCoeffEqv (blocks : Nat) (p q : RatPoly) : Prop :=
  RatPolyCoeffEqv
    (reindexQuaternionPolynomial (identityQuaternionBlockInvolution blocks) p)
    (reindexQuaternionPolynomial (identityQuaternionBlockInvolution blocks) q)

namespace PaddedPolynomialCoeffEqv

theorem refl (blocks : Nat) (p : RatPoly) : PaddedPolynomialCoeffEqv blocks p p := RatPolyCoeffEqv.refl _

theorem symm {blocks : Nat} {p q : RatPoly} (h : PaddedPolynomialCoeffEqv blocks p q) :
    PaddedPolynomialCoeffEqv blocks q p := RatPolyCoeffEqv.symm h

theorem trans {blocks : Nat} {p q r : RatPoly}
    (hp : PaddedPolynomialCoeffEqv blocks p q) (hq : PaddedPolynomialCoeffEqv blocks q r) :
    PaddedPolynomialCoeffEqv blocks p r := RatPolyCoeffEqv.trans hp hq

theorem of_coeff {blocks : Nat} {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    PaddedPolynomialCoeffEqv blocks p q := RatPolyCoeffEqv.reindex _ h

theorem of_prefix {blocks : Nat} {p q : RatPoly} (h : QuaternionPrefixPolynomialEqv blocks p q) :
    PaddedPolynomialCoeffEqv blocks p q :=
  prefix_coeffEqv_of_lengths (QuaternionPrefixPolynomialEqv.reindex _ h)
    (reindex_term_length _ p) (reindex_term_length _ q)

theorem add {blocks : Nat} {p p' q q' : RatPoly}
    (hp : PaddedPolynomialCoeffEqv blocks p p') (hq : PaddedPolynomialCoeffEqv blocks q q') :
    PaddedPolynomialCoeffEqv blocks (polyAdd p q) (polyAdd p' q') := by
  unfold PaddedPolynomialCoeffEqv
  rw [reindexQuaternionPolynomial_add, reindexQuaternionPolynomial_add]
  exact RatPolyCoeffEqv.add hp hq

theorem mul {blocks : Nat} {p p' q q' : RatPoly}
    (hp : PaddedPolynomialCoeffEqv blocks p p') (hq : PaddedPolynomialCoeffEqv blocks q q') :
    PaddedPolynomialCoeffEqv blocks (polyMul p q) (polyMul p' q') := by
  unfold PaddedPolynomialCoeffEqv
  rw [reindexQuaternionPolynomial_mul, reindexQuaternionPolynomial_mul]
  exact RatPolyCoeffEqv.mul hp hq

theorem smul {blocks : Nat} {p q : RatPoly} (h : PaddedPolynomialCoeffEqv blocks p q) (a : Q') :
    PaddedPolynomialCoeffEqv blocks (polySmul a p) (polySmul a q) := by
  unfold PaddedPolynomialCoeffEqv
  rw [reindexQuaternionPolynomial_smul, reindexQuaternionPolynomial_smul]
  exact RatPolyCoeffEqv.smul a h

theorem character {blocks : Nat} {p q : RatPoly} (h : PaddedPolynomialCoeffEqv blocks p q) :
    ∀ spin, PaddedPolynomialCoeffEqv blocks (characterPolynomial p spin) (characterPolynomial q spin)
  | 0 => .refl _ _
  | 1 => h.smul 2
  | n + 2 => ((h.smul 2).mul (h.character (n + 1))).add ((h.character n).smul (-1))

theorem finiteSum {A : Type} {blocks : Nat} (f g : A → RatPoly) :
    ∀ xs : List A, (∀ a, a ∈ xs → PaddedPolynomialCoeffEqv blocks (f a) (g a)) →
      PaddedPolynomialCoeffEqv blocks (finitePolySum f xs) (finitePolySum g xs)
  | [], _ => .refl _ _
  | a :: xs, h => (h a List.mem_cons_self).add
      (finiteSum f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

private theorem haar_weight (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks p = ratWeightedSum (quaternionHaarMono blocks) p
  | [] => rfl
  | _ :: rest => by unfold quaternionHaar ratWeightedSum; rw [haar_weight blocks rest]

private theorem padded_support (blocks : Nat) (p : RatPoly) :
    SupportedQuaternionBlocks blocks (reindexQuaternionPolynomial (identityQuaternionBlockInvolution blocks) p) :=
  fun t ht => Nat.le_of_eq (reindex_term_length _ p t ht)

/-- Remove common padding only when both original polynomials belong to
the stated carrier. No variables outside the carrier are silently dropped. -/
theorem haar {blocks : Nat} {p q : RatPoly} (h : PaddedPolynomialCoeffEqv blocks p q)
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q) :
    (quaternionHaar blocks p).eqv (quaternionHaar blocks q) := by
  have hc : (quaternionHaar blocks (reindexQuaternionPolynomial (identityQuaternionBlockInvolution blocks) p)).eqv
      (quaternionHaar blocks (reindexQuaternionPolynomial (identityQuaternionBlockInvolution blocks) q)) := by
    rw [haar_weight, haar_weight]
    exact h _
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (quaternionHaar_prefixPolynomialEqv blocks
      (identityReindexQuaternionPolynomial_prefix blocks p) (padded_support blocks p) hp))
    (Q'.eqv_trans _ _ _ hc (quaternionHaar_prefixPolynomialEqv blocks
      (identityReindexQuaternionPolynomial_prefix blocks q) (padded_support blocks q) hq))

theorem haar_insert {blocks : Nat} {p q : RatPoly} (h : PaddedPolynomialCoeffEqv blocks p q)
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q)
    (insertion : RatPoly) (hi : SupportedQuaternionBlocks blocks insertion) :
    (quaternionHaar blocks (polyMul insertion p)).eqv (quaternionHaar blocks (polyMul insertion q)) :=
  ((refl blocks insertion).mul h).haar (supported_polyMul hi hp) (supported_polyMul hi hq)

end PaddedPolynomialCoeffEqv

theorem applySteps_zero {tailBlocks : Nat} (hb : 0 < tailBlocks) :
    ∀ steps : List (SelectedTranslationStep tailBlocks),
      applySelectedTranslationSteps hb steps polyZero = polyZero
  | [] => rfl
  | step :: rest => by
      have hz : applySelectedTranslationStep hb step polyZero = polyZero := by
        cases hs : step.side <;> cases ho : step.multiplierOrientation <;>
          simp only [applySelectedTranslationStep, hs, ho] <;> rfl
      simp only [applySelectedTranslationSteps, hz, applySteps_zero hb rest]

theorem applySteps_character {tailBlocks : Nat} (hb : 0 < tailBlocks)
    (steps : List (SelectedTranslationStep tailBlocks)) (p : RatPoly) :
    ∀ spin, PaddedPolynomialCoeffEqv (tailBlocks + 1)
      (applySelectedTranslationSteps hb steps (characterPolynomial p spin))
      (characterPolynomial (applySelectedTranslationSteps hb steps p) spin)
  | 0 => .of_prefix (applySteps_one_prefix hb steps).scalar
  | 1 => .of_coeff (applySelectedTranslationSteps_smul hb steps 2 p)
  | n + 2 => by
      rw [characterPolynomial, applySelectedTranslationSteps_add]
      exact ((PaddedPolynomialCoeffEqv.of_coeff (applySelectedTranslationSteps_mul hb steps _ _)).trans
        ((PaddedPolynomialCoeffEqv.of_coeff (applySelectedTranslationSteps_smul hb steps _ _)).mul
          (applySteps_character hb steps p (n + 1)))).add
        ((PaddedPolynomialCoeffEqv.of_coeff (applySelectedTranslationSteps_smul hb steps _ _)).trans
          ((applySteps_character hb steps p n).smul (-1)))

theorem applySteps_finiteSum {A : Type} {tailBlocks : Nat} (hb : 0 < tailBlocks)
    (steps : List (SelectedTranslationStep tailBlocks)) (f : A → RatPoly) :
    ∀ xs : List A, applySelectedTranslationSteps hb steps (finitePolySum f xs) =
      finitePolySum (fun a => applySelectedTranslationSteps hb steps (f a)) xs
  | [] => applySteps_zero hb steps
  | a :: xs => by simp only [finitePolySum, applySelectedTranslationSteps_add, applySteps_finiteSum hb steps f xs]

theorem applySteps_sum_image {A : Type} {tailBlocks : Nat} (hb : 0 < tailBlocks)
    (steps : List (SelectedTranslationStep tailBlocks)) (f g : A → RatPoly) (xs : List A)
    (h : ∀ a, a ∈ xs → PaddedPolynomialCoeffEqv (tailBlocks + 1)
      (applySelectedTranslationSteps hb steps (f a)) (g a)) :
    PaddedPolynomialCoeffEqv (tailBlocks + 1)
      (applySelectedTranslationSteps hb steps (finitePolySum f xs)) (finitePolySum g xs) := by
  rw [applySteps_finiteSum]
  exact PaddedPolynomialCoeffEqv.finiteSum _ _ xs h

theorem applySteps_fold_image {A : Type} {tailBlocks : Nat} (hb : 0 < tailBlocks)
    (steps : List (SelectedTranslationStep tailBlocks)) (f g : A → RatPoly) :
    ∀ xs : List A, (∀ a, a ∈ xs → PaddedPolynomialCoeffEqv (tailBlocks + 1)
      (applySelectedTranslationSteps hb steps (f a)) (g a)) →
      PaddedPolynomialCoeffEqv (tailBlocks + 1)
        (applySelectedTranslationSteps hb steps (xs.foldr (fun a p => polyMul (f a) p) polyOne))
        (xs.foldr (fun a p => polyMul (g a) p) polyOne)
  | [], _ => .of_prefix (applySteps_one_prefix hb steps).scalar
  | a :: xs, h => (PaddedPolynomialCoeffEqv.of_coeff (applySelectedTranslationSteps_mul hb steps _ _)).trans
      ((h a List.mem_cons_self).mul (applySteps_fold_image hb steps f g xs
        (fun b hb => h b (List.mem_cons_of_mem a hb))))

end YMGap.Continuum.SU2QuaternionTranslationPolynomialImages

#print axioms YMGap.Continuum.SU2QuaternionTranslationPolynomialImages.PaddedPolynomialCoeffEqv
#print axioms YMGap.Continuum.SU2QuaternionTranslationPolynomialImages.PaddedPolynomialCoeffEqv.refl
#print axioms YMGap.Continuum.SU2QuaternionTranslationPolynomialImages.PaddedPolynomialCoeffEqv.symm
#print axioms YMGap.Continuum.SU2QuaternionTranslationPolynomialImages.PaddedPolynomialCoeffEqv.trans
#print axioms YMGap.Continuum.SU2QuaternionTranslationPolynomialImages.PaddedPolynomialCoeffEqv.of_coeff
#print axioms YMGap.Continuum.SU2QuaternionTranslationPolynomialImages.PaddedPolynomialCoeffEqv.of_prefix
#print axioms YMGap.Continuum.SU2QuaternionTranslationPolynomialImages.PaddedPolynomialCoeffEqv.add
#print axioms YMGap.Continuum.SU2QuaternionTranslationPolynomialImages.PaddedPolynomialCoeffEqv.mul
#print axioms YMGap.Continuum.SU2QuaternionTranslationPolynomialImages.PaddedPolynomialCoeffEqv.smul
#print axioms YMGap.Continuum.SU2QuaternionTranslationPolynomialImages.PaddedPolynomialCoeffEqv.character
#print axioms YMGap.Continuum.SU2QuaternionTranslationPolynomialImages.PaddedPolynomialCoeffEqv.finiteSum
#print axioms YMGap.Continuum.SU2QuaternionTranslationPolynomialImages.PaddedPolynomialCoeffEqv.haar
#print axioms YMGap.Continuum.SU2QuaternionTranslationPolynomialImages.PaddedPolynomialCoeffEqv.haar_insert
#print axioms YMGap.Continuum.SU2QuaternionTranslationPolynomialImages.applySteps_zero
#print axioms YMGap.Continuum.SU2QuaternionTranslationPolynomialImages.applySteps_character
#print axioms YMGap.Continuum.SU2QuaternionTranslationPolynomialImages.applySteps_finiteSum
#print axioms YMGap.Continuum.SU2QuaternionTranslationPolynomialImages.applySteps_sum_image
#print axioms YMGap.Continuum.SU2QuaternionTranslationPolynomialImages.applySteps_fold_image
