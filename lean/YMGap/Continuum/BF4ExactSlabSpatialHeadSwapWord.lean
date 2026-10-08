/-
# The original plaquette word under the spatial x0/x1 swap

The swap fixes physical time x3. Five planes retain the canonical boundary
order; p01 exchanges A with D and B with C. Its transformed word is the
CONJUGATE of the original word, not a commutation of its factors. Consequently
the scalar and every spin character agree coefficientwise, without a unit
norm, positivity, cutoff or small-coupling assumption.

This is the oriented-word input for reindexing every original heat factor.
The coordinate-block reindex, Haar/action invariance, original-window scalar
invariance and completed reflected-form isometry are subsequent obligations.
No continuum covariance or width-changing isometry is asserted.
-/

import YMGap.Continuum.BF4ExactSlabSpatialHeadSwapGeometry
import YMGap.Continuum.BF4ExactSlabSpatialAxisSwapWord

namespace YMGap.Continuum.BF4ExactSlabSpatialHeadSwapWord

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabSpatialHeadSwapGeometry
open YMGap.Continuum.SU2QuaternionHaarGaugeCancellation

/-- Evaluate the SAME ordered boundary with the link assignment pulled
back along the concrete spatial swap. All inverse flags are unchanged. -/
def swappedFaceWord (u : Z4Link → PolyQuaternion) (face : Z4Plaq) : PolyQuaternion :=
  plaquetteWord (u (swapLink (faceLinkA face))) (u (swapLink (faceLinkB face)))
    (u (swapLink (faceLinkC face))) (u (swapLink (faceLinkD face)))

def targetFaceWord (u : Z4Link → PolyQuaternion) (face : Z4Plaq) : PolyQuaternion :=
  plaquetteWord (u (faceLinkA (swapPlaquette face))) (u (faceLinkB (swapPlaquette face)))
    (u (faceLinkC (swapPlaquette face))) (u (faceLinkD (swapPlaquette face)))

/-- The ONLY reversal is p01; no quaternion product is commuted. -/
theorem swappedFaceWord_scalar (u : Z4Link → PolyQuaternion) (face : Z4Plaq) :
    RatPolyCoeffEqv (swappedFaceWord u face).scalar (targetFaceWord u face).scalar := by
  rcases face with ⟨⟨a, b, c, d⟩, plane⟩
  cases plane
  all_goals try exact RatPolyCoeffEqv.refl _
  exact BF4ExactSlabSpatialAxisSwapWord.reverse_word_scalar _ _ _ _

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

end YMGap.Continuum.BF4ExactSlabSpatialHeadSwapWord

#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeadSwapWord.swappedFaceWord_scalar
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeadSwapWord.swappedFaceWord_character
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeadSwapWord.correctedSlab_swappedWord_character

#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeadSwapWord.swappedFaceWord
#print axioms YMGap.Continuum.BF4ExactSlabSpatialHeadSwapWord.targetFaceWord

