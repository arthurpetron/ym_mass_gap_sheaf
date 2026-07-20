/-
# Face-word bridge for the edge-touching double cube

The production double-cube boundary exposes forty-eight fundamental matrix
coefficients in face-major order.  The bivalent contraction leaf instead
uses the inherited four-valent word as the base of a right-local fold.  This
leaf reconciles those two representatives only after finite-product Haar.

Every statement is pointwise in an arbitrary `List Bool`.  The assignment is
queried by `List.getD`; no Boolean assignment carrier, depth-forty-eight sum,
bounded labelling family, or trajectory is unfolded or materialized.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeBivalentContraction
import YMGap.Continuum.SU2QuaternionDistinctBlockFundamentalContractionReordering
import YMGap.Continuum.SU2QuaternionFiniteProductHaarFourFactorGrouping

namespace YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeBivalentContraction

open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveLinkCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur

/-! ## 1. Polynomial selected by one structural descriptor -/

def DoubleCubeCoefficientDescriptor.block
    (descriptor : DoubleCubeCoefficientDescriptor) : Nat :=
  adjacentEvenActiveLinkIndex 0 descriptor.physicalLink

/-- The honest complex coefficient selected by one descriptor and one opaque
forty-eight-tag assignment. -/
def DoubleCubeCoefficientDescriptor.coefficient
    (descriptor : DoubleCubeCoefficientDescriptor)
    (assignment : List Bool) : ComplexRatPoly :=
  if descriptor.positive then
    forwardFundamentalCoefficient descriptor.block
      (doubleCubeTagValue assignment descriptor.rowTag)
      (doubleCubeTagValue assignment descriptor.columnTag)
  else
    reverseFundamentalCoefficient descriptor.block
      (doubleCubeTagValue assignment descriptor.rowTag)
      (doubleCubeTagValue assignment descriptor.columnTag)

end YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeBivalentContraction

namespace YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeFaceWordBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveLinkCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexReordering
open YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTraceExpansion
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFourFactorGrouping
open YMGap.Continuum.SU2QuaternionDistinctBlockFundamentalContractionProduct
open YMGap.Continuum.SU2QuaternionDistinctBlockFundamentalContractionReordering
open YMGap.Continuum.SU2QuaternionOneLinkFourValentHaarProjectorReordering
open YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeBivalentContraction

/-! ## 2. Named resolved and face-major coefficient words -/

/-- The four inherited shared-link factors in their literal face order
`R1 F1 R2 F2`. -/
def radiusZeroEdgeTouchingDoubleCubeSharedCoefficientWord
    (assignment : List Bool) : List ComplexRatPoly :=
  [reverseFundamentalCoefficient
      radiusZeroEdgeTouchingDoubleCubeSharedBlock
      (doubleCubeTagValue assignment 18)
      (doubleCubeTagValue assignment 22),
   forwardFundamentalCoefficient
      radiusZeroEdgeTouchingDoubleCubeSharedBlock
      (doubleCubeTagValue assignment 23)
      (doubleCubeTagValue assignment 19),
   reverseFundamentalCoefficient
      radiusZeroEdgeTouchingDoubleCubeSharedBlock
      (doubleCubeTagValue assignment 27)
      (doubleCubeTagValue assignment 24),
   forwardFundamentalCoefficient
      radiusZeroEdgeTouchingDoubleCubeSharedBlock
      (doubleCubeTagValue assignment 25)
      (doubleCubeTagValue assignment 28)]

/-- The forty-eight factors in the certified resolved order: the inherited
shared row first, followed by the twenty-two forward/reverse bivalent rows. -/
def radiusZeroEdgeTouchingDoubleCubeResolvedCoefficientWord
    (assignment : List Bool) : List ComplexRatPoly :=
  radiusZeroEdgeTouchingDoubleCubeResolvedDescriptors.map
    (fun descriptor => descriptor.coefficient assignment)

/-- The same forty-eight coefficient factors in production face-major order. -/
def radiusZeroEdgeTouchingDoubleCubeFaceMajorCoefficientWord
    (assignment : List Bool) : List ComplexRatPoly :=
  radiusZeroEdgeTouchingDoubleCubeFaceMajorDescriptors.map
    (fun descriptor => descriptor.coefficient assignment)

/-- One bivalent descriptor row maps exactly to the generic forward/reverse
coefficient row of its contraction step. -/
theorem taggedDoubleCubeBivalentPairCoefficientFactors_eq_contractionFactors
    (pair : TaggedDoubleCubeBivalentPair) (assignment : List Bool) :
    (taggedDoubleCubeBivalentPairDescriptors pair).map
        (fun descriptor => descriptor.coefficient assignment) =
      orientedFundamentalContractionCoefficientFactors
        (pair.contraction assignment) := by
  unfold taggedDoubleCubeBivalentPairDescriptors
    DoubleCubeCoefficientDescriptor.coefficient
    DoubleCubeCoefficientDescriptor.block
    orientedFundamentalContractionCoefficientFactors
    TaggedDoubleCubeBivalentPair.contraction
  simp only [List.map_cons, List.map_nil, Bool.false_eq_true,
    if_true, if_false]

private theorem taggedDoubleCubeBivalentPairsCoefficientFactors_eq_scheduleFactors
    (assignment : List Bool) :
    ∀ pairs : List TaggedDoubleCubeBivalentPair,
      (pairs.flatMap taggedDoubleCubeBivalentPairDescriptors).map
          (fun descriptor => descriptor.coefficient assignment) =
        (pairs.map (fun pair => pair.contraction assignment)).flatMap
          orientedFundamentalContractionCoefficientFactors
  | [] => rfl
  | pair :: pairs => by
      simp only [List.flatMap_cons, List.map_append, List.map_cons]
      rw [taggedDoubleCubeBivalentPairCoefficientFactors_eq_contractionFactors,
        taggedDoubleCubeBivalentPairsCoefficientFactors_eq_scheduleFactors
          assignment pairs]

/-- Mapping the four shared descriptors through an opaque assignment gives
exactly the named literal `R1 F1 R2 F2` coefficient row. -/
theorem radiusZeroEdgeTouchingDoubleCubeSharedDescriptors_map_coefficient
    (assignment : List Bool) :
    radiusZeroEdgeTouchingDoubleCubeSharedDescriptors.map
        (fun descriptor => descriptor.coefficient assignment) =
      radiusZeroEdgeTouchingDoubleCubeSharedCoefficientWord assignment := by
  unfold radiusZeroEdgeTouchingDoubleCubeSharedDescriptors
    radiusZeroEdgeTouchingDoubleCubeSharedCoefficientWord
    DoubleCubeCoefficientDescriptor.coefficient
    DoubleCubeCoefficientDescriptor.block
    radiusZeroEdgeTouchingDoubleCubeSharedBlock
  simp only [List.map_cons, List.map_nil, Bool.false_eq_true,
    if_true, if_false]

/-- The resolved mapped word is literally the shared coefficient row followed
by the generic schedule-order bivalent coefficient word. -/
theorem radiusZeroEdgeTouchingDoubleCubeResolvedCoefficientWord_eq_shared_append_contractionWord
    (assignment : List Bool) :
    radiusZeroEdgeTouchingDoubleCubeResolvedCoefficientWord assignment =
      radiusZeroEdgeTouchingDoubleCubeSharedCoefficientWord assignment ++
        fundamentalContractionCoefficientWord
          (radiusZeroEdgeTouchingDoubleCubeBivalentSchedule assignment) := by
  unfold radiusZeroEdgeTouchingDoubleCubeResolvedCoefficientWord
    radiusZeroEdgeTouchingDoubleCubeResolvedDescriptors
    radiusZeroEdgeTouchingDoubleCubeBivalentSchedule
    fundamentalContractionCoefficientWord
  rw [List.map_append,
    radiusZeroEdgeTouchingDoubleCubeSharedDescriptors_map_coefficient,
    taggedDoubleCubeBivalentPairsCoefficientFactors_eq_scheduleFactors]

/-- Mapping the existing descriptor-level coverage permutation through an
opaque assignment yields the exact resolved-to-face factor permutation. -/
theorem radiusZeroEdgeTouchingDoubleCubeResolvedCoefficientWord_perm_faceMajor
    (assignment : List Bool) :
    (radiusZeroEdgeTouchingDoubleCubeResolvedCoefficientWord assignment).Perm
      (radiusZeroEdgeTouchingDoubleCubeFaceMajorCoefficientWord assignment) := by
  exact
    radiusZeroEdgeTouchingDoubleCubeResolvedDescriptors_perm_faceMajor.map
      (fun descriptor => descriptor.coefficient assignment)

/-! ## 3. Context-safe grouping of the shared row -/

/-- Grouping the first four resolved factors into the literal left-associated
shared-link base preserves finite-product Haar, with the entire bivalent word
retained as an opaque suffix. -/
theorem finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeSharedLiteral_mul_word_eq_resolved
    (assignment : List Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        (complexRatPolyMul
          (radiusZeroEdgeTouchingDoubleCubeSharedLiteralTerm assignment)
          (complexRatPolyProduct
            (fundamentalContractionCoefficientWord
              (radiusZeroEdgeTouchingDoubleCubeBivalentSchedule
                assignment)))))
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        (complexRatPolyProduct
          (radiusZeroEdgeTouchingDoubleCubeResolvedCoefficientWord
            assignment))) := by
  let blockCount := (adjacentEvenActiveLinks 0).length
  let suffix := fundamentalContractionCoefficientWord
    (radiusZeroEdgeTouchingDoubleCubeBivalentSchedule assignment)
  have hgroup :=
    finiteProductHaarComplex_mul_fourFactorRowProducts_eq_flatMap
      blockCount
      (fun _ : Unit =>
        reverseFundamentalCoefficient
          radiusZeroEdgeTouchingDoubleCubeSharedBlock
          (doubleCubeTagValue assignment 18)
          (doubleCubeTagValue assignment 22))
      (fun _ : Unit =>
        forwardFundamentalCoefficient
          radiusZeroEdgeTouchingDoubleCubeSharedBlock
          (doubleCubeTagValue assignment 23)
          (doubleCubeTagValue assignment 19))
      (fun _ : Unit =>
        reverseFundamentalCoefficient
          radiusZeroEdgeTouchingDoubleCubeSharedBlock
          (doubleCubeTagValue assignment 27)
          (doubleCubeTagValue assignment 24))
      (fun _ : Unit =>
        forwardFundamentalCoefficient
          radiusZeroEdgeTouchingDoubleCubeSharedBlock
          (doubleCubeTagValue assignment 25)
          (doubleCubeTagValue assignment 28))
      complexRatPolyOne [()] suffix
  have hgroupNamed : RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul complexRatPolyOne
          (complexRatPolyMul
            (radiusZeroEdgeTouchingDoubleCubeSharedLiteralTerm assignment)
            (complexRatPolyProduct suffix))))
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul complexRatPolyOne
          (complexRatPolyProduct
            (radiusZeroEdgeTouchingDoubleCubeSharedCoefficientWord assignment ++
              suffix)))) := by
    simpa only [complexRatPolyFourFactorRowPolynomial,
      complexRatPolyFourFactorRowFactors,
      radiusZeroEdgeTouchingDoubleCubeSharedLiteralTerm,
      reverseForwardReverseForwardFundamentalTerm,
      radiusZeroEdgeTouchingDoubleCubeSharedCoefficientWord,
      List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
      List.cons_append, List.nil_append, complexRatPolyProduct] using hgroup
  rw [radiusZeroEdgeTouchingDoubleCubeResolvedCoefficientWord_eq_shared_append_contractionWord]
  exact rationalComplexEqv_trans
    (rationalComplexEqv_symm
      (finiteProductHaarComplex_one_mul blockCount
        (complexRatPolyMul
          (radiusZeroEdgeTouchingDoubleCubeSharedLiteralTerm assignment)
          (complexRatPolyProduct suffix))))
    (rationalComplexEqv_trans hgroupNamed
      (finiteProductHaarComplex_one_mul blockCount
        (complexRatPolyProduct
          (radiusZeroEdgeTouchingDoubleCubeSharedCoefficientWord assignment ++
            suffix))))

/-! ## 4. Production face word to the grouped and contracted representatives -/

/-- **Exact fixed-assignment face-word bridge.**  The production face-major
forty-eight-factor word has the same finite-product Haar value as the literal
shared-base right-local bivalent fold. -/
theorem finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeFaceMajorCoefficientProduct_eq_groupedSummand
    (assignment : List Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        (complexRatPolyProduct
          (radiusZeroEdgeTouchingDoubleCubeFaceMajorCoefficientWord
            assignment)))
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        (radiusZeroEdgeTouchingDoubleCubeGroupedSummand assignment)) := by
  refine rationalComplexEqv_trans
    (rationalComplexEqv_symm
      (finiteProductHaarComplex_product_perm
        (adjacentEvenActiveLinks 0).length
        (radiusZeroEdgeTouchingDoubleCubeResolvedCoefficientWord_perm_faceMajor
          assignment))) ?_
  refine rationalComplexEqv_trans
    (rationalComplexEqv_symm
      (finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeSharedLiteral_mul_word_eq_resolved
        assignment)) ?_
  apply rationalComplexEqv_symm
  simpa only [radiusZeroEdgeTouchingDoubleCubeGroupedSummand] using
    (finiteProductHaarComplex_contractionProductOver_eq_mul_word
      (adjacentEvenActiveLinks 0).length
      (radiusZeroEdgeTouchingDoubleCubeSharedLiteralTerm assignment)
      (radiusZeroEdgeTouchingDoubleCubeBivalentSchedule assignment))

/-- The face-major factor word therefore contracts to the exact signed
projector with all twenty-two bivalent Schur deltas retained. -/
theorem finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeFaceMajorCoefficientProduct_eq_contractedValue
    (assignment : List Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        (complexRatPolyProduct
          (radiusZeroEdgeTouchingDoubleCubeFaceMajorCoefficientWord
            assignment)))
      (radiusZeroEdgeTouchingDoubleCubeContractedValue assignment) :=
  rationalComplexEqv_trans
    (finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeFaceMajorCoefficientProduct_eq_groupedSummand
      assignment)
    (finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeGroupedSummand
      assignment)

#print axioms DoubleCubeCoefficientDescriptor.block
#print axioms DoubleCubeCoefficientDescriptor.coefficient
#print axioms taggedDoubleCubeBivalentPairCoefficientFactors_eq_contractionFactors
#print axioms radiusZeroEdgeTouchingDoubleCubeSharedDescriptors_map_coefficient
#print axioms radiusZeroEdgeTouchingDoubleCubeResolvedCoefficientWord_eq_shared_append_contractionWord
#print axioms radiusZeroEdgeTouchingDoubleCubeResolvedCoefficientWord_perm_faceMajor
#print axioms finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeSharedLiteral_mul_word_eq_resolved
#print axioms finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeFaceMajorCoefficientProduct_eq_groupedSummand
#print axioms finiteProductHaarComplex_radiusZeroEdgeTouchingDoubleCubeFaceMajorCoefficientProduct_eq_contractedValue

end YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeFaceWordBridge
