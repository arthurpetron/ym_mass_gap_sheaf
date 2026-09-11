/-
# Tagged elementary-cube coefficient-product reconciliation

This leaf composes the generic right-local contraction-fold reconciliation
with the elementary cube's explicit twenty-four-slot occurrence permutation.
For every opaque Boolean assignment, it identifies the finite-product Haar
value of the face-major coefficient word with the already certified paired
summand and hence with its exact crossed-Schur-delta value.

The face-major object here is only the tail-first word of twenty-four honest
complex coefficient factors.  It is not yet packaged into six plaquette
trace terms, no Boolean assignment is enumerated, and no depth-twenty-four
sum is unfolded.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionDistinctBlockFundamentalContractionReordering
import YMGap.Continuum.SU2QuaternionElementaryCubeTaggedOccurrenceCoverage

namespace YMGap.Continuum.SU2QuaternionElementaryCubeTaggedProductReconciliation

open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexReordering
open YMGap.Continuum.SU2QuaternionDistinctBlockFundamentalContractionProduct
open YMGap.Continuum.SU2QuaternionDistinctBlockFundamentalContractionReordering
open YMGap.Continuum.SU2QuaternionElementaryCubeTaggedFundamentalContraction
open YMGap.Continuum.SU2QuaternionElementaryCubeTaggedOccurrenceCoverage
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveLinkCarrier

/-! ## 1. Named symbolic factor words -/

/-- The schedule-order forward/reverse coefficient word certified in the
tagged occurrence leaf. -/
def radiusZeroElementaryCubePairedCoefficientWord
    (assignment : List Bool) : List ComplexRatPoly :=
  radiusZeroElementaryCubePairedCoefficientDescriptors.map
    (fun descriptor => descriptor.coefficient assignment)

/-- The six-face-major coefficient word, still kept as twenty-four opaque
honest complex factors. -/
def radiusZeroElementaryCubeFaceMajorCoefficientWord
    (assignment : List Bool) : List ComplexRatPoly :=
  radiusZeroElementaryCubeFaceMajorCoefficientDescriptors.map
    (fun descriptor => descriptor.coefficient assignment)

/-- The named paired word is literally the generic forward/reverse flattening
of the established radius-zero contraction schedule. -/
theorem radiusZeroElementaryCubePairedCoefficientWord_eq_contractionWord
    (assignment : List Bool) :
    radiusZeroElementaryCubePairedCoefficientWord assignment =
      fundamentalContractionCoefficientWord
        (radiusZeroElementaryCubeContractionSchedule assignment) := by
  unfold radiusZeroElementaryCubePairedCoefficientWord
  rw [radiusZeroElementaryCubePairedCoefficientPolynomials_eq_scheduleFactors]
  rfl

/-- The explicit twenty-four-slot occurrence certificate, expressed through
the named symbolic words used below. -/
theorem radiusZeroElementaryCubePairedCoefficientWord_perm_faceMajor
    (assignment : List Bool) :
    (radiusZeroElementaryCubePairedCoefficientWord assignment).Perm
      (radiusZeroElementaryCubeFaceMajorCoefficientWord assignment) := by
  exact radiusZeroElementaryCubePairedCoefficientPolynomials_perm_faceMajor
    assignment

/-! ## 2. Fixed-assignment Haar reconciliation -/

/-- The schedule-order coefficient word has the same finite-product Haar
value as the established right-local paired summand. -/
theorem finiteProductHaarComplex_radiusZeroElementaryCubePairedCoefficientProduct_eq_pairedSummand
    (assignment : List Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        (complexRatPolyProduct
          (radiusZeroElementaryCubePairedCoefficientWord assignment)))
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        (radiusZeroElementaryCubePairedSummand assignment)) := by
  apply rationalComplexEqv_symm
  have h :=
    finiteProductHaarComplex_fundamentalContractionProduct_eq_word
      (adjacentEvenActiveLinks 0).length
      (radiusZeroElementaryCubeContractionSchedule assignment)
  rw [← radiusZeroElementaryCubePairedCoefficientWord_eq_contractionWord
    assignment] at h
  exact h

/-- The face-major twenty-four-factor word has the same finite-product Haar
value as the right-local paired summand. -/
theorem finiteProductHaarComplex_radiusZeroElementaryCubeFaceMajorCoefficientProduct_eq_pairedSummand
    (assignment : List Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        (complexRatPolyProduct
          (radiusZeroElementaryCubeFaceMajorCoefficientWord assignment)))
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        (radiusZeroElementaryCubePairedSummand assignment)) :=
  rationalComplexEqv_trans
    (rationalComplexEqv_symm
      (finiteProductHaarComplex_product_perm
        (adjacentEvenActiveLinks 0).length
        (radiusZeroElementaryCubePairedCoefficientWord_perm_faceMajor
          assignment)))
    (finiteProductHaarComplex_radiusZeroElementaryCubePairedCoefficientProduct_eq_pairedSummand
      assignment)

/-- Reverse-direction form consumed by the later face-chunk construction. -/
theorem finiteProductHaarComplex_radiusZeroElementaryCubePairedSummand_eq_faceMajorCoefficientProduct
    (assignment : List Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        (radiusZeroElementaryCubePairedSummand assignment))
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        (complexRatPolyProduct
          (radiusZeroElementaryCubeFaceMajorCoefficientWord assignment))) :=
  rationalComplexEqv_symm
    (finiteProductHaarComplex_radiusZeroElementaryCubeFaceMajorCoefficientProduct_eq_pairedSummand
      assignment)

/-- **Exact face-major fixed-assignment endpoint.**  The face-major
twenty-four-factor coefficient word contracts to the already resolved
crossed-Schur-delta value, pointwise in an opaque Boolean assignment. -/
theorem finiteProductHaarComplex_radiusZeroElementaryCubeFaceMajorCoefficientProduct_eq_schurDeltaValue
    (assignment : List Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        (complexRatPolyProduct
          (radiusZeroElementaryCubeFaceMajorCoefficientWord assignment)))
      (radiusZeroElementaryCubeSchurDeltaValue assignment) :=
  rationalComplexEqv_trans
    (finiteProductHaarComplex_radiusZeroElementaryCubeFaceMajorCoefficientProduct_eq_pairedSummand
      assignment)
    (finiteProductHaarComplex_radiusZeroElementaryCubePairedSummand assignment)

#print axioms radiusZeroElementaryCubePairedCoefficientWord_eq_contractionWord
#print axioms radiusZeroElementaryCubePairedCoefficientWord_perm_faceMajor
#print axioms finiteProductHaarComplex_radiusZeroElementaryCubePairedCoefficientProduct_eq_pairedSummand
#print axioms finiteProductHaarComplex_radiusZeroElementaryCubeFaceMajorCoefficientProduct_eq_pairedSummand
#print axioms finiteProductHaarComplex_radiusZeroElementaryCubePairedSummand_eq_faceMajorCoefficientProduct
#print axioms finiteProductHaarComplex_radiusZeroElementaryCubeFaceMajorCoefficientProduct_eq_schurDeltaValue

end YMGap.Continuum.SU2QuaternionElementaryCubeTaggedProductReconciliation
