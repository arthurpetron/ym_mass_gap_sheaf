/-
# Canonical all-standard elementary-cube trace-expansion product

The genuine outward cube product has the audited orientation mask
`reversed, standard, reversed, standard, reversed, standard`.  The production
representative instead uses the standard plaquette word at all six faces.
This leaf defines that canonical product and transports the exact outward
Haar value through the contextual one-face orientation fence.

Only slots `0`, `2`, and `4` are changed.  Each replacement is performed
under the already accumulated left prefix and the unresolved right suffix;
no bare Haar equivalence is multiplied by another polynomial.  Neither the
depth-twenty-four Boolean sum nor any concrete assignment carrier is exposed.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionElementaryCubeOutwardTraceExpansionProduct
import YMGap.Continuum.SU2QuaternionPlaquetteOrientationHaarReindex

namespace YMGap.Continuum.SU2QuaternionElementaryCubeCanonicalTraceExpansionProduct

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexReordering
open YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTraceExpansion
open YMGap.Continuum.SU2QuaternionElementaryCubeOutwardFaceProductBridge
open YMGap.Continuum.SU2QuaternionElementaryCubeOutwardTraceExpansionProduct
open YMGap.Continuum.SU2QuaternionPlaquetteOrientationHaarReindex
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveLinkCarrier

/-! ## 1. A structural alternating-six replacement theorem -/

/-- Replace the three reversed slots in an alternating six-factor word.
Each supplied replacement law is contextual in an arbitrary polynomial
prefix and suffix.  The proof explicitly accumulates the prefixes before
using those laws and restores the original tail-first parenthesization
afterwards. -/
theorem finiteProductHaarComplex_alternatingSix_reversed_eq_standard
    (blockCount : Nat)
    (reversed0 standard0 standard1
      reversed2 standard2 standard3
      reversed4 standard4 standard5 : ComplexRatPoly)
    (h0 : forall spectator suffix,
      RationalComplexEqv
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul spectator
            (complexRatPolyMul reversed0 suffix)))
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul spectator
            (complexRatPolyMul standard0 suffix))))
    (h2 : forall spectator suffix,
      RationalComplexEqv
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul spectator
            (complexRatPolyMul reversed2 suffix)))
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul spectator
            (complexRatPolyMul standard2 suffix))))
    (h4 : forall spectator suffix,
      RationalComplexEqv
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul spectator
            (complexRatPolyMul reversed4 suffix)))
        (finiteProductHaarComplex blockCount
          (complexRatPolyMul spectator
            (complexRatPolyMul standard4 suffix)))) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyProduct
          [reversed0, standard1, reversed2,
           standard3, reversed4, standard5]))
      (finiteProductHaarComplex blockCount
        (complexRatPolyProduct
          [standard0, standard1, standard2,
           standard3, standard4, standard5])) := by
  refine rationalComplexEqv_trans
    (rationalComplexEqv_symm
      (finiteProductHaarComplex_one_mul blockCount
        (complexRatPolyProduct
          [reversed0, standard1, reversed2,
           standard3, reversed4, standard5]))) ?_
  refine rationalComplexEqv_trans
    (h0 complexRatPolyOne
      (complexRatPolyProduct
        [standard1, reversed2, standard3, reversed4, standard5])) ?_
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_one_mul blockCount
      (complexRatPolyProduct
        [standard0, standard1, reversed2,
         standard3, reversed4, standard5])) ?_
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_assoc_context blockCount
      standard0 standard1
      (complexRatPolyProduct
        [reversed2, standard3, reversed4, standard5])) ?_
  refine rationalComplexEqv_trans
    (h2 (complexRatPolyMul standard0 standard1)
      (complexRatPolyProduct [standard3, reversed4, standard5])) ?_
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_assoc blockCount
      standard0 standard1
      (complexRatPolyProduct
        [standard2, standard3, reversed4, standard5])) ?_
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_assoc_context blockCount
      standard0 standard1
      (complexRatPolyProduct
        [standard2, standard3, reversed4, standard5])) ?_
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_assoc_context blockCount
      (complexRatPolyMul standard0 standard1) standard2
      (complexRatPolyProduct [standard3, reversed4, standard5])) ?_
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_assoc_context blockCount
      (complexRatPolyMul
        (complexRatPolyMul standard0 standard1) standard2)
      standard3
      (complexRatPolyProduct [reversed4, standard5])) ?_
  refine rationalComplexEqv_trans
    (h4
      (complexRatPolyMul
        (complexRatPolyMul
          (complexRatPolyMul standard0 standard1) standard2)
        standard3)
      (complexRatPolyProduct [standard5])) ?_
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_assoc blockCount
      (complexRatPolyMul
        (complexRatPolyMul standard0 standard1) standard2)
      standard3
      (complexRatPolyProduct [standard4, standard5])) ?_
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_assoc blockCount
      (complexRatPolyMul standard0 standard1) standard2
      (complexRatPolyProduct [standard3, standard4, standard5])) ?_
  exact finiteProductHaarComplex_mul_assoc blockCount
    standard0 standard1
    (complexRatPolyProduct
      [standard2, standard3, standard4, standard5])

/-! ## 2. The literal all-standard six-face representative -/

/-- Six standard plaquette trace expansions in exactly the audited outward
face order.  Only the word orientation has been canonicalized. -/
def radiusZeroElementaryCubeCanonicalFaceTraceExpansions :
    List ComplexRatPoly :=
  [standardPlaquetteTraceExpansion
      radiusZeroElementaryCubeOutwardFaceRow0.block0
      radiusZeroElementaryCubeOutwardFaceRow0.block1
      radiusZeroElementaryCubeOutwardFaceRow0.block2
      radiusZeroElementaryCubeOutwardFaceRow0.block3,
   standardPlaquetteTraceExpansion
      radiusZeroElementaryCubeOutwardFaceRow1.block0
      radiusZeroElementaryCubeOutwardFaceRow1.block1
      radiusZeroElementaryCubeOutwardFaceRow1.block2
      radiusZeroElementaryCubeOutwardFaceRow1.block3,
   standardPlaquetteTraceExpansion
      radiusZeroElementaryCubeOutwardFaceRow2.block0
      radiusZeroElementaryCubeOutwardFaceRow2.block1
      radiusZeroElementaryCubeOutwardFaceRow2.block2
      radiusZeroElementaryCubeOutwardFaceRow2.block3,
   standardPlaquetteTraceExpansion
      radiusZeroElementaryCubeOutwardFaceRow3.block0
      radiusZeroElementaryCubeOutwardFaceRow3.block1
      radiusZeroElementaryCubeOutwardFaceRow3.block2
      radiusZeroElementaryCubeOutwardFaceRow3.block3,
   standardPlaquetteTraceExpansion
      radiusZeroElementaryCubeOutwardFaceRow4.block0
      radiusZeroElementaryCubeOutwardFaceRow4.block1
      radiusZeroElementaryCubeOutwardFaceRow4.block2
      radiusZeroElementaryCubeOutwardFaceRow4.block3,
   standardPlaquetteTraceExpansion
      radiusZeroElementaryCubeOutwardFaceRow5.block0
      radiusZeroElementaryCubeOutwardFaceRow5.block1
      radiusZeroElementaryCubeOutwardFaceRow5.block2
      radiusZeroElementaryCubeOutwardFaceRow5.block3]

/-- The canonical production representative: the tail-first product of the
six all-standard trace expansions. -/
def radiusZeroElementaryCubeCanonicalTraceExpansionProduct : ComplexRatPoly :=
  complexRatPolyProduct
    radiusZeroElementaryCubeCanonicalFaceTraceExpansions

/-- Literal audit: the canonical list has six factors, all with standard
orientation and in unchanged face order. -/
theorem radiusZeroElementaryCubeCanonicalFaceTraceExpansions_all_standard :
    radiusZeroElementaryCubeCanonicalFaceTraceExpansions =
      [standardPlaquetteTraceExpansion
          radiusZeroElementaryCubeOutwardFaceRow0.block0
          radiusZeroElementaryCubeOutwardFaceRow0.block1
          radiusZeroElementaryCubeOutwardFaceRow0.block2
          radiusZeroElementaryCubeOutwardFaceRow0.block3,
       standardPlaquetteTraceExpansion
          radiusZeroElementaryCubeOutwardFaceRow1.block0
          radiusZeroElementaryCubeOutwardFaceRow1.block1
          radiusZeroElementaryCubeOutwardFaceRow1.block2
          radiusZeroElementaryCubeOutwardFaceRow1.block3,
       standardPlaquetteTraceExpansion
          radiusZeroElementaryCubeOutwardFaceRow2.block0
          radiusZeroElementaryCubeOutwardFaceRow2.block1
          radiusZeroElementaryCubeOutwardFaceRow2.block2
          radiusZeroElementaryCubeOutwardFaceRow2.block3,
       standardPlaquetteTraceExpansion
          radiusZeroElementaryCubeOutwardFaceRow3.block0
          radiusZeroElementaryCubeOutwardFaceRow3.block1
          radiusZeroElementaryCubeOutwardFaceRow3.block2
          radiusZeroElementaryCubeOutwardFaceRow3.block3,
       standardPlaquetteTraceExpansion
          radiusZeroElementaryCubeOutwardFaceRow4.block0
          radiusZeroElementaryCubeOutwardFaceRow4.block1
          radiusZeroElementaryCubeOutwardFaceRow4.block2
          radiusZeroElementaryCubeOutwardFaceRow4.block3,
       standardPlaquetteTraceExpansion
          radiusZeroElementaryCubeOutwardFaceRow5.block0
          radiusZeroElementaryCubeOutwardFaceRow5.block1
          radiusZeroElementaryCubeOutwardFaceRow5.block2
          radiusZeroElementaryCubeOutwardFaceRow5.block3] := by
  rfl

/-! ## 3. Outward-to-canonical transport and exact value -/

/-- The orientation-faithful outward product and the canonical all-standard
product have the same finite-product Haar value.  The contextual orientation
theorem is used exactly for face slots `0`, `2`, and `4`. -/
theorem finiteProductHaarComplex_radiusZeroElementaryCubeOutward_eq_canonical :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        radiusZeroElementaryCubeOutwardTraceExpansionProduct)
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        radiusZeroElementaryCubeCanonicalTraceExpansionProduct) := by
  unfold radiusZeroElementaryCubeOutwardTraceExpansionProduct
    radiusZeroElementaryCubeCanonicalTraceExpansionProduct
  rw [radiusZeroElementaryCubeOutwardFaceTraceExpansions_orientation_mask,
      radiusZeroElementaryCubeCanonicalFaceTraceExpansions_all_standard]
  apply finiteProductHaarComplex_alternatingSix_reversed_eq_standard
  · intro spectator suffix
    exact finiteProductHaarComplex_mul_reversedPlaquetteTraceExpansion_eq_standard
      (adjacentEvenActiveLinks 0).length spectator suffix
      radiusZeroElementaryCubeOutwardFaceRow0.block0
      radiusZeroElementaryCubeOutwardFaceRow0.block1
      radiusZeroElementaryCubeOutwardFaceRow0.block2
      radiusZeroElementaryCubeOutwardFaceRow0.block3
  · intro spectator suffix
    exact finiteProductHaarComplex_mul_reversedPlaquetteTraceExpansion_eq_standard
      (adjacentEvenActiveLinks 0).length spectator suffix
      radiusZeroElementaryCubeOutwardFaceRow2.block0
      radiusZeroElementaryCubeOutwardFaceRow2.block1
      radiusZeroElementaryCubeOutwardFaceRow2.block2
      radiusZeroElementaryCubeOutwardFaceRow2.block3
  · intro spectator suffix
    exact finiteProductHaarComplex_mul_reversedPlaquetteTraceExpansion_eq_standard
      (adjacentEvenActiveLinks 0).length spectator suffix
      radiusZeroElementaryCubeOutwardFaceRow4.block0
      radiusZeroElementaryCubeOutwardFaceRow4.block1
      radiusZeroElementaryCubeOutwardFaceRow4.block2
      radiusZeroElementaryCubeOutwardFaceRow4.block3

/-- Reverse-direction form of the representative-level orientation fence. -/
theorem finiteProductHaarComplex_radiusZeroElementaryCubeCanonical_eq_outward :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        radiusZeroElementaryCubeCanonicalTraceExpansionProduct)
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        radiusZeroElementaryCubeOutwardTraceExpansionProduct) :=
  rationalComplexEqv_symm
    finiteProductHaarComplex_radiusZeroElementaryCubeOutward_eq_canonical

/-- **Exact canonical cube integral.**  The all-standard six-face production
representative has exact twelve-link Haar value `1/16`. -/
theorem finiteProductHaarComplex_radiusZeroElementaryCubeCanonicalTraceExpansionProduct_exact :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        radiusZeroElementaryCubeCanonicalTraceExpansionProduct)
      (Q'.mkPos 1 16 (by decide), 0) :=
  rationalComplexEqv_trans
    finiteProductHaarComplex_radiusZeroElementaryCubeCanonical_eq_outward
    finiteProductHaarComplex_radiusZeroElementaryCubeOutwardTraceExpansionProduct_exact

#print axioms finiteProductHaarComplex_alternatingSix_reversed_eq_standard
#print axioms radiusZeroElementaryCubeCanonicalFaceTraceExpansions_all_standard
#print axioms finiteProductHaarComplex_radiusZeroElementaryCubeOutward_eq_canonical
#print axioms finiteProductHaarComplex_radiusZeroElementaryCubeCanonical_eq_outward
#print axioms finiteProductHaarComplex_radiusZeroElementaryCubeCanonicalTraceExpansionProduct_exact

end YMGap.Continuum.SU2QuaternionElementaryCubeCanonicalTraceExpansionProduct
