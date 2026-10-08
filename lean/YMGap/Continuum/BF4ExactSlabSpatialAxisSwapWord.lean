/-
# The original plaquette word under the spatial x1/x2 swap

The swap fixes physical time x3. Five planes retain the canonical boundary
order; p12 exchanges A with D and B with C. Its transformed word is the
CONJUGATE of the original word, not a commutation of its factors. Consequently
the scalar and every spin character agree coefficientwise, without a unit
norm, positivity, cutoff or small-coupling assumption.

This is the oriented-word input for reindexing every original heat factor.
The coordinate-block reindex, Haar/action invariance, original-window scalar
invariance and completed reflected-form isometry are subsequent obligations.
No continuum covariance or width-changing isometry is asserted.
-/

import YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry
import YMGap.Continuum.BF4ExactSlabAllExtentPlaquetteReflection

namespace YMGap.Continuum.BF4ExactSlabSpatialAxisSwapWord

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry
open YMGap.Continuum.SU2QuaternionHaarGaugeCancellation

private theorem double_conj (q : PolyQuaternion) :
    PolyQuaternionCoeffEqv (PolyQuaternion.conj (PolyQuaternion.conj q)) q := by
  have hn (p : RatPoly) : RatPolyCoeffEqv (polyNeg (polyNeg p)) p :=
    coeffEvalExpr_eqv_of_normalize_eq (.neg (.neg (.var 0))) (.var 0)
      (by decide) (fun _ => p)
  exact ⟨RatPolyCoeffEqv.refl q.scalar, hn q.iPart, hn q.jPart, hn q.kPart⟩

/-- Reversing the literal boundary gives its conjugate. This is a full
four-component coefficient identity, not just equality of traces. -/
theorem reverse_word_conjugate (a b c d : PolyQuaternion) :
    PolyQuaternionCoeffEqv (plaquetteWord d c b a)
      (PolyQuaternion.conj (plaquetteWord a b c d)) := by
  have hinner : PolyQuaternionCoeffEqv
      (PolyQuaternion.conj (PolyQuaternion.mul (PolyQuaternion.mul a b)
        (PolyQuaternion.conj c)))
      (PolyQuaternion.mul c
        (PolyQuaternion.mul (PolyQuaternion.conj b) (PolyQuaternion.conj a))) :=
    (BF4ExactSlabPlaquettePathGram.conjugate_product _ _).trans
      ((double_conj c).mul (BF4ExactSlabPlaquettePathGram.conjugate_product a b))
  have h := (BF4ExactSlabPlaquettePathGram.conjugate_product
    (PolyQuaternion.mul (PolyQuaternion.mul a b) (PolyQuaternion.conj c))
    (PolyQuaternion.conj d)).trans ((double_conj d).mul hinner)
  exact (h.trans ((PolyQuaternionCoeffEqv.mul_assoc d c
      (PolyQuaternion.mul (PolyQuaternion.conj b) (PolyQuaternion.conj a))).symm.trans
    (PolyQuaternionCoeffEqv.mul_assoc (PolyQuaternion.mul d c)
      (PolyQuaternion.conj b) (PolyQuaternion.conj a)).symm)).symm

theorem reverse_word_scalar (a b c d : PolyQuaternion) :
    RatPolyCoeffEqv (plaquetteWord d c b a).scalar
      (plaquetteWord a b c d).scalar :=
  (reverse_word_conjugate a b c d).scalar

/-- Evaluate the SAME ordered boundary with the link assignment pulled
back along the concrete spatial swap. All inverse flags are unchanged. -/
def swappedFaceWord (u : Z4Link → PolyQuaternion) (face : Z4Plaq) : PolyQuaternion :=
  plaquetteWord (u (swapLink (faceLinkA face))) (u (swapLink (faceLinkB face)))
    (u (swapLink (faceLinkC face))) (u (swapLink (faceLinkD face)))

def targetFaceWord (u : Z4Link → PolyQuaternion) (face : Z4Plaq) : PolyQuaternion :=
  plaquetteWord (u (faceLinkA (swapPlaquette face))) (u (faceLinkB (swapPlaquette face)))
    (u (faceLinkC (swapPlaquette face))) (u (faceLinkD (swapPlaquette face)))

/-- The ONLY reversal is p12; no quaternion product is commuted. -/
theorem swappedFaceWord_scalar (u : Z4Link → PolyQuaternion) (face : Z4Plaq) :
    RatPolyCoeffEqv (swappedFaceWord u face).scalar (targetFaceWord u face).scalar := by
  rcases face with ⟨⟨a, b, c, d⟩, plane⟩
  cases plane
  all_goals try exact RatPolyCoeffEqv.refl _
  exact reverse_word_scalar _ _ _ _

/-- Every spin character of the actual spatially swapped oriented word
equals the character on the swapped face, for an arbitrary link assignment. -/
theorem swappedFaceWord_character (u : Z4Link → PolyQuaternion) (face : Z4Plaq) (spin : Nat) :
    RatPolyCoeffEqv (characterPolynomial (swappedFaceWord u face).scalar spin)
      (characterPolynomial (targetFaceWord u face).scalar spin) :=
  characterPolynomial_coeffEqv (swappedFaceWord_scalar u face) spin

/-- Literal corrected-slab target, retaining the initial-unit fold through
its existing coefficient pin. The source still names the SWAPPED links. -/
theorem correctedSlab_swappedWord_character (extent : Nat) (face : Z4Plaq) (spin : Nat) :
    RatPolyCoeffEqv
      (characterPolynomial (swappedFaceWord (correctedSlabLinkPolynomial extent) face).scalar spin)
      (characterPolynomial (correctedSlabPlaquettePolynomial extent (swapPlaquette face)).scalar spin) := by
  have ht : PolyQuaternionCoeffEqv (correctedSlabPlaquettePolynomial extent (swapPlaquette face))
      (targetFaceWord (correctedSlabLinkPolynomial extent) face) := by
    exact YMGap.Continuum.BF4ExactSlabAllExtentPlaquetteReflection.plaquette_eq_word extent
      (swapPlaquette face)
  exact (swappedFaceWord_character (correctedSlabLinkPolynomial extent) face spin).trans
    (characterPolynomial_coeffEqv ht.scalar.symm spin)

end YMGap.Continuum.BF4ExactSlabSpatialAxisSwapWord

#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapWord.reverse_word_conjugate
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapWord.reverse_word_scalar
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapWord.swappedFaceWord_scalar
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapWord.swappedFaceWord_character
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapWord.correctedSlab_swappedWord_character
