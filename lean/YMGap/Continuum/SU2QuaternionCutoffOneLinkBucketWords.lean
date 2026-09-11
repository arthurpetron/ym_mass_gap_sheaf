/-
# Geometry-generic cutoff-one link-bucket words

This leaf performs the geometry-only half of the global cutoff-one Haar
regrouping.  For one named Boolean environment it turns every N0 face-major
descriptor into an orientation-complete `FundamentalOccurrence`, identifies
the N1 face product with the corresponding descriptor coefficient word under
finite-product Haar, and then stably regroups that word by the common touched-
link carrier.

The bucket permutation is proved by structural insertion.  It preserves
multiplicity, does not assume descriptor duplicate-freeness, and uses only
the duplicate-freeness of the touched-link carrier together with the N0
coverage theorem.  No local Haar kernel is evaluated in this file.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionCutoffOneNamedTraceExpansionProduct
import YMGap.Continuum.SU2QuaternionFiniteProductHaarFourFactorGrouping
import YMGap.Continuum.SU2QuaternionFundamentalSelfDuality

namespace YMGap.Continuum.SU2QuaternionCutoffOneLinkBucketWords

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexReordering
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFourFactorGrouping
open YMGap.Continuum.SU2QuaternionFundamentalSelfDuality
open YMGap.Continuum.SU2QuaternionCutoffOneOrientedFaceRows
open YMGap.Continuum.SU2QuaternionCutoffOneNamedTraceExpansionProduct

/-! ## 1. Descriptor occurrence and coefficient semantics -/

/-- Read the two named matrix indices of one geometric descriptor and retain
its literal forward/reverse link orientation. -/
def cutoffOneDescriptorOccurrence
    (environment : Nat → Bool)
    (descriptor : CutoffOneLinkOccurrenceDescriptor) :
    FundamentalOccurrence :=
  match descriptor.positive with
  | true =>
      ⟨.forward,
        environment descriptor.rowTag,
        environment descriptor.columnTag⟩
  | false =>
      ⟨.reverse,
        environment descriptor.rowTag,
        environment descriptor.columnTag⟩

/-- The honest polynomial coefficient carried by one descriptor in a common
physical-link block list. -/
def cutoffOneDescriptorCoefficient
    (links : List Z4Link) (environment : Nat → Bool)
    (descriptor : CutoffOneLinkOccurrenceDescriptor) : ComplexRatPoly :=
  fundamentalOccurrenceCoefficient (descriptor.block links)
    (cutoffOneDescriptorOccurrence environment descriptor)

theorem cutoffOneDescriptorCoefficient_eq_forward_of_positive
    (links : List Z4Link) (environment : Nat → Bool)
    (descriptor : CutoffOneLinkOccurrenceDescriptor)
    (hpositive : descriptor.positive = true) :
    cutoffOneDescriptorCoefficient links environment descriptor =
      forwardFundamentalCoefficient (descriptor.block links)
        (environment descriptor.rowTag)
        (environment descriptor.columnTag) := by
  obtain ⟨physicalLink, positive, rowTag, columnTag⟩ := descriptor
  cases positive <;> simp_all [cutoffOneDescriptorCoefficient,
    cutoffOneDescriptorOccurrence, fundamentalOccurrenceCoefficient,
    orientedFundamentalCoefficient]

theorem cutoffOneDescriptorCoefficient_eq_reverse_of_not_positive
    (links : List Z4Link) (environment : Nat → Bool)
    (descriptor : CutoffOneLinkOccurrenceDescriptor)
    (hpositive : descriptor.positive = false) :
    cutoffOneDescriptorCoefficient links environment descriptor =
      reverseFundamentalCoefficient (descriptor.block links)
        (environment descriptor.rowTag)
        (environment descriptor.columnTag) := by
  obtain ⟨physicalLink, positive, rowTag, columnTag⟩ := descriptor
  cases positive <;> simp_all [cutoffOneDescriptorCoefficient,
    cutoffOneDescriptorOccurrence, fundamentalOccurrenceCoefficient,
    orientedFundamentalCoefficient]

/-! ## 2. One face as four descriptor coefficients -/

def cutoffOneFaceFirstCoefficient
    (links : List Z4Link) (environment : Nat → Bool)
    (row : CutoffOneOrientedFaceRow) : ComplexRatPoly :=
  match row.orientation with
  | .standard =>
      forwardFundamentalCoefficient
        (cutoffOneOrientedFaceBlock0 links row)
        (environment row.firstTag) (environment row.secondTag)
  | .reversed =>
      forwardFundamentalCoefficient
        (cutoffOneOrientedFaceBlock1 links row)
        (environment row.firstTag) (environment row.secondTag)

def cutoffOneFaceSecondCoefficient
    (links : List Z4Link) (environment : Nat → Bool)
    (row : CutoffOneOrientedFaceRow) : ComplexRatPoly :=
  match row.orientation with
  | .standard =>
      forwardFundamentalCoefficient
        (cutoffOneOrientedFaceBlock3 links row)
        (environment row.secondTag) (environment row.thirdTag)
  | .reversed =>
      forwardFundamentalCoefficient
        (cutoffOneOrientedFaceBlock2 links row)
        (environment row.secondTag) (environment row.thirdTag)

def cutoffOneFaceThirdCoefficient
    (links : List Z4Link) (environment : Nat → Bool)
    (row : CutoffOneOrientedFaceRow) : ComplexRatPoly :=
  match row.orientation with
  | .standard =>
      reverseFundamentalCoefficient
        (cutoffOneOrientedFaceBlock2 links row)
        (environment row.thirdTag) (environment row.fourthTag)
  | .reversed =>
      reverseFundamentalCoefficient
        (cutoffOneOrientedFaceBlock3 links row)
        (environment row.thirdTag) (environment row.fourthTag)

def cutoffOneFaceFourthCoefficient
    (links : List Z4Link) (environment : Nat → Bool)
    (row : CutoffOneOrientedFaceRow) : ComplexRatPoly :=
  match row.orientation with
  | .standard =>
      reverseFundamentalCoefficient
        (cutoffOneOrientedFaceBlock1 links row)
        (environment row.fourthTag) (environment row.firstTag)
  | .reversed =>
      reverseFundamentalCoefficient
        (cutoffOneOrientedFaceBlock0 links row)
        (environment row.fourthTag) (environment row.firstTag)

/-- The N1 fixed face term is literally the established left-associated
four-factor row formed by the four descriptor coefficients. -/
theorem cutoffOneOrientedFaceTraceTermAt_eq_fourFactorRowPolynomial
    (links : List Z4Link) (environment : Nat → Bool)
    (row : CutoffOneOrientedFaceRow) :
    cutoffOneOrientedFaceTraceTermAt links environment row =
      complexRatPolyFourFactorRowPolynomial
        (cutoffOneFaceFirstCoefficient links environment)
        (cutoffOneFaceSecondCoefficient links environment)
        (cutoffOneFaceThirdCoefficient links environment)
        (cutoffOneFaceFourthCoefficient links environment) row := by
  obtain ⟨supportPosition, physicalFaceId, plaquette, orientation⟩ := row
  cases orientation <;> rfl

/-- The four factors of one row, in their trace order, are exactly the map of
the N0 coefficient descriptors through the occurrence semantics above. -/
theorem cutoffOneFaceFactors_eq_descriptorCoefficients
    (links : List Z4Link) (environment : Nat → Bool)
    (row : CutoffOneOrientedFaceRow) :
    complexRatPolyFourFactorRowFactors
        (cutoffOneFaceFirstCoefficient links environment)
        (cutoffOneFaceSecondCoefficient links environment)
        (cutoffOneFaceThirdCoefficient links environment)
        (cutoffOneFaceFourthCoefficient links environment) row =
      row.coefficientDescriptors.map
        (cutoffOneDescriptorCoefficient links environment) := by
  obtain ⟨supportPosition, physicalFaceId, plaquette, orientation⟩ := row
  cases orientation <;> rfl

private theorem cutoffOneFaceTraceTerms_eq_fourFactorRows
    (links : List Z4Link) (environment : Nat → Bool) :
    ∀ rows : List CutoffOneOrientedFaceRow,
      rows.map (cutoffOneOrientedFaceTraceTermAt links environment) =
        rows.map (complexRatPolyFourFactorRowPolynomial
          (cutoffOneFaceFirstCoefficient links environment)
          (cutoffOneFaceSecondCoefficient links environment)
          (cutoffOneFaceThirdCoefficient links environment)
          (cutoffOneFaceFourthCoefficient links environment))
  | [] => rfl
  | row :: rows => by
      simp only [List.map_cons, List.cons.injEq]
      exact
        ⟨cutoffOneOrientedFaceTraceTermAt_eq_fourFactorRowPolynomial
            links environment row,
          cutoffOneFaceTraceTerms_eq_fourFactorRows
            links environment rows⟩

private theorem cutoffOneFaceFactorRows_eq_faceMajorDescriptorCoefficients
    (links : List Z4Link) (environment : Nat → Bool) :
    ∀ rows : List CutoffOneOrientedFaceRow,
      rows.flatMap (complexRatPolyFourFactorRowFactors
          (cutoffOneFaceFirstCoefficient links environment)
          (cutoffOneFaceSecondCoefficient links environment)
          (cutoffOneFaceThirdCoefficient links environment)
          (cutoffOneFaceFourthCoefficient links environment)) =
        (rows.flatMap
            CutoffOneOrientedFaceRow.coefficientDescriptors).map
          (cutoffOneDescriptorCoefficient links environment)
  | [] => rfl
  | row :: rows => by
      simp only [List.flatMap_cons, List.map_append]
      rw [cutoffOneFaceFactors_eq_descriptorCoefficients,
        cutoffOneFaceFactorRows_eq_faceMajorDescriptorCoefficients
          links environment rows]

/-! ## 3. Face-major coefficient word -/

def cutoffOneFaceMajorCoefficientWord
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) (environment : Nat → Bool) :
    List ComplexRatPoly :=
  (cutoffOneFaceMajorOccurrenceDescriptors
    orientationAt n support).map
      (cutoffOneDescriptorCoefficient
        (cutoffOneTouchedLinks n support) environment)

/-- Replacing the per-face left associations by the flattened face-major
descriptor word preserves the exact finite-product Haar value. -/
theorem finiteProductHaarComplex_cutoffOneOrientedFaceTraceProductAt_eq_faceMajorCoefficientProduct
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) (environment : Nat → Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex
        (cutoffOneTouchedLinks n support).length
        (cutoffOneOrientedFaceTraceProductAt
          orientationAt n support environment))
      (finiteProductHaarComplex
        (cutoffOneTouchedLinks n support).length
        (complexRatPolyProduct
          (cutoffOneFaceMajorCoefficientWord
            orientationAt n support environment))) := by
  unfold cutoffOneOrientedFaceTraceProductAt
    cutoffOneOrientedFaceTraceTermsAt
    cutoffOneFaceMajorCoefficientWord
  rw [cutoffOneFaceTraceTerms_eq_fourFactorRows]
  have h := finiteProductHaarComplex_fourFactorRowProducts_eq_flatMap
    (cutoffOneTouchedLinks n support).length
    (cutoffOneFaceFirstCoefficient
      (cutoffOneTouchedLinks n support) environment)
    (cutoffOneFaceSecondCoefficient
      (cutoffOneTouchedLinks n support) environment)
    (cutoffOneFaceThirdCoefficient
      (cutoffOneTouchedLinks n support) environment)
    (cutoffOneFaceFourthCoefficient
      (cutoffOneTouchedLinks n support) environment)
    (cutoffOneOrientedFaceRows orientationAt n support)
  rw [cutoffOneFaceFactorRows_eq_faceMajorDescriptorCoefficients] at h
  exact h

/-! ## 4. Structural stable bucketing by physical link -/

private def descriptorLinkBucket
    (link : Z4Link)
    (descriptors : List CutoffOneLinkOccurrenceDescriptor) :
    List CutoffOneLinkOccurrenceDescriptor :=
  descriptors.filter
    (fun descriptor => decide (descriptor.physicalLink = link))

private def descriptorLinkBuckets
    (links : List Z4Link)
    (descriptors : List CutoffOneLinkOccurrenceDescriptor) :
    List CutoffOneLinkOccurrenceDescriptor :=
  links.flatMap (fun link => descriptorLinkBucket link descriptors)

private theorem descriptorLinkBuckets_cons
    (link : Z4Link) (links : List Z4Link)
    (descriptors : List CutoffOneLinkOccurrenceDescriptor) :
    descriptorLinkBuckets (link :: links) descriptors =
      descriptorLinkBucket link descriptors ++
        descriptorLinkBuckets links descriptors := by
  rfl

private theorem descriptorLinkBucket_cons_of_eq
    (link : Z4Link) (descriptor : CutoffOneLinkOccurrenceDescriptor)
    (descriptors : List CutoffOneLinkOccurrenceDescriptor)
    (hlink : descriptor.physicalLink = link) :
    descriptorLinkBucket link (descriptor :: descriptors) =
      descriptor :: descriptorLinkBucket link descriptors := by
  simp [descriptorLinkBucket, hlink]

private theorem descriptorLinkBucket_cons_of_ne
    (link : Z4Link) (descriptor : CutoffOneLinkOccurrenceDescriptor)
    (descriptors : List CutoffOneLinkOccurrenceDescriptor)
    (hlink : descriptor.physicalLink ≠ link) :
    descriptorLinkBucket link (descriptor :: descriptors) =
      descriptorLinkBucket link descriptors := by
  simp [descriptorLinkBucket, hlink]

private theorem descriptorLinkBuckets_nil :
    ∀ links : List Z4Link, descriptorLinkBuckets links [] = []
  | [] => rfl
  | link :: links => by
      rw [descriptorLinkBuckets_cons,
        descriptorLinkBuckets_nil links]
      rfl

private theorem descriptorLinkBuckets_cons_of_key_not_mem
    (descriptor : CutoffOneLinkOccurrenceDescriptor)
    (descriptors : List CutoffOneLinkOccurrenceDescriptor) :
    ∀ links : List Z4Link, descriptor.physicalLink ∉ links →
      descriptorLinkBuckets links (descriptor :: descriptors) =
        descriptorLinkBuckets links descriptors
  | [], _ => rfl
  | link :: links, hnot => by
      have hhead : descriptor.physicalLink ≠ link := by
        intro heq
        exact hnot (List.mem_cons.mpr (Or.inl heq))
      have htail : descriptor.physicalLink ∉ links := by
        intro hmem
        exact hnot (List.mem_cons.mpr (Or.inr hmem))
      rw [descriptorLinkBuckets_cons,
        descriptorLinkBucket_cons_of_ne link descriptor descriptors hhead,
        descriptorLinkBuckets_cons_of_key_not_mem
          descriptor descriptors links htail,
        descriptorLinkBuckets_cons]

/-- Inserting one covered descriptor into every bucket word inserts it
exactly once, in the unique bucket selected by its physical link. -/
private theorem descriptorLinkBuckets_cons_perm
    (descriptor : CutoffOneLinkOccurrenceDescriptor)
    (descriptors : List CutoffOneLinkOccurrenceDescriptor) :
    ∀ links : List Z4Link, links.Nodup →
      descriptor.physicalLink ∈ links →
      (descriptorLinkBuckets links (descriptor :: descriptors)).Perm
        (descriptor :: descriptorLinkBuckets links descriptors)
  | [], _, hmem => by cases hmem
  | link :: links, hnodup, hmem => by
      have hparts := List.nodup_cons.mp hnodup
      by_cases hlink : descriptor.physicalLink = link
      · have hnot : descriptor.physicalLink ∉ links := by
          rw [hlink]
          exact hparts.1
        rw [descriptorLinkBuckets_cons,
          descriptorLinkBucket_cons_of_eq
            link descriptor descriptors hlink,
          descriptorLinkBuckets_cons_of_key_not_mem
            descriptor descriptors links hnot,
          descriptorLinkBuckets_cons]
        exact List.Perm.refl _
      · have htail : descriptor.physicalLink ∈ links :=
          (List.mem_cons.mp hmem).resolve_left hlink
        have ih := descriptorLinkBuckets_cons_perm
          descriptor descriptors links hparts.2 htail
        rw [descriptorLinkBuckets_cons,
          descriptorLinkBucket_cons_of_ne
            link descriptor descriptors hlink,
          descriptorLinkBuckets_cons]
        exact
          (ih.append_left (descriptorLinkBucket link descriptors)).trans
            (List.perm_middle
              (l₁ := descriptorLinkBucket link descriptors)
              (a := descriptor)
              (l₂ := descriptorLinkBuckets links descriptors))

private theorem descriptorLinkBuckets_perm_of_coverage
    (links : List Z4Link) (hnodup : links.Nodup) :
    ∀ descriptors : List CutoffOneLinkOccurrenceDescriptor,
      (∀ descriptor, descriptor ∈ descriptors →
        descriptor.physicalLink ∈ links) →
      (descriptorLinkBuckets links descriptors).Perm descriptors
  | [], _ => by
      rw [descriptorLinkBuckets_nil]
  | descriptor :: descriptors, hcoverage => by
      refine (descriptorLinkBuckets_cons_perm
        descriptor descriptors links hnodup
        (hcoverage descriptor List.mem_cons_self)).trans ?_
      exact List.Perm.cons descriptor
        (descriptorLinkBuckets_perm_of_coverage
          links hnodup descriptors (fun item hitem =>
            hcoverage item (List.mem_cons_of_mem descriptor hitem)))

/-! ## 5. The production link-major word and coefficient bridge -/

/-- Stable link-major order: touched links retain their canonical geometric
order, and occurrences within a link retain face-major order. -/
def cutoffOneLinkMajorOccurrenceDescriptors
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) :
    List CutoffOneLinkOccurrenceDescriptor :=
  (cutoffOneTouchedLinks n support).flatMap
    (cutoffOneLinkOccurrenceBucket orientationAt n support)

private theorem cutoffOneLinkMajorOccurrenceDescriptors_eq_buckets
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) :
    cutoffOneLinkMajorOccurrenceDescriptors orientationAt n support =
      descriptorLinkBuckets
        (cutoffOneTouchedLinks n support)
        (cutoffOneFaceMajorOccurrenceDescriptors
          orientationAt n support) := by
  rfl

/-- **Geometry-only link bucketing.**  The stable link-major word is a
constructive permutation of the full face-major descriptor word.  No
descriptor is dropped, duplicated, or identified with another descriptor. -/
theorem cutoffOneLinkMajorOccurrenceDescriptors_perm_faceMajor
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) :
    (cutoffOneLinkMajorOccurrenceDescriptors
      orientationAt n support).Perm
      (cutoffOneFaceMajorOccurrenceDescriptors
        orientationAt n support) := by
  rw [cutoffOneLinkMajorOccurrenceDescriptors_eq_buckets]
  exact descriptorLinkBuckets_perm_of_coverage
    (cutoffOneTouchedLinks n support)
    (cutoffOneTouchedLinks_nodup n support)
    (cutoffOneFaceMajorOccurrenceDescriptors orientationAt n support)
    (fun descriptor hdescriptor =>
      cutoffOneFaceMajorOccurrenceDescriptor_physicalLink_mem_touched
        hdescriptor)

def cutoffOneLinkMajorCoefficientWord
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) (environment : Nat → Bool) :
    List ComplexRatPoly :=
  (cutoffOneLinkMajorOccurrenceDescriptors
    orientationAt n support).map
      (cutoffOneDescriptorCoefficient
        (cutoffOneTouchedLinks n support) environment)

theorem cutoffOneLinkMajorCoefficientWord_perm_faceMajor
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) (environment : Nat → Bool) :
    (cutoffOneLinkMajorCoefficientWord
      orientationAt n support environment).Perm
      (cutoffOneFaceMajorCoefficientWord
        orientationAt n support environment) := by
  exact
    (cutoffOneLinkMajorOccurrenceDescriptors_perm_faceMajor
      orientationAt n support).map
        (cutoffOneDescriptorCoefficient
          (cutoffOneTouchedLinks n support) environment)

/-- Reindexing the coefficient factors from face-major to link-major order
preserves finite-product Haar. -/
theorem finiteProductHaarComplex_cutoffOneFaceMajorCoefficientProduct_eq_linkMajor
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) (environment : Nat → Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex
        (cutoffOneTouchedLinks n support).length
        (complexRatPolyProduct
          (cutoffOneFaceMajorCoefficientWord
            orientationAt n support environment)))
      (finiteProductHaarComplex
        (cutoffOneTouchedLinks n support).length
        (complexRatPolyProduct
          (cutoffOneLinkMajorCoefficientWord
            orientationAt n support environment))) :=
  rationalComplexEqv_symm
    (finiteProductHaarComplex_product_perm
      (cutoffOneTouchedLinks n support).length
      (cutoffOneLinkMajorCoefficientWord_perm_faceMajor
        orientationAt n support environment))

/-- **N1-to-link-major bridge.**  At every named environment, the literal
oriented face product has the same finite-product Haar value as the stable
link-major word of honest orientation-complete fundamental coefficients. -/
theorem finiteProductHaarComplex_cutoffOneOrientedFaceTraceProductAt_eq_linkMajorCoefficientProduct
    (orientationAt : CutoffOneFaceOrientationChoice)
    (n : Nat) (support : List Nat) (environment : Nat → Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex
        (cutoffOneTouchedLinks n support).length
        (cutoffOneOrientedFaceTraceProductAt
          orientationAt n support environment))
      (finiteProductHaarComplex
        (cutoffOneTouchedLinks n support).length
        (complexRatPolyProduct
          (cutoffOneLinkMajorCoefficientWord
            orientationAt n support environment))) :=
  rationalComplexEqv_trans
    (finiteProductHaarComplex_cutoffOneOrientedFaceTraceProductAt_eq_faceMajorCoefficientProduct
      orientationAt n support environment)
    (finiteProductHaarComplex_cutoffOneFaceMajorCoefficientProduct_eq_linkMajor
      orientationAt n support environment)

#print axioms cutoffOneDescriptorCoefficient_eq_forward_of_positive
#print axioms cutoffOneDescriptorCoefficient_eq_reverse_of_not_positive
#print axioms cutoffOneOrientedFaceTraceTermAt_eq_fourFactorRowPolynomial
#print axioms cutoffOneFaceFactors_eq_descriptorCoefficients
#print axioms finiteProductHaarComplex_cutoffOneOrientedFaceTraceProductAt_eq_faceMajorCoefficientProduct
#print axioms cutoffOneLinkMajorOccurrenceDescriptors_perm_faceMajor
#print axioms cutoffOneLinkMajorCoefficientWord_perm_faceMajor
#print axioms finiteProductHaarComplex_cutoffOneOrientedFaceTraceProductAt_eq_linkMajorCoefficientProduct

end YMGap.Continuum.SU2QuaternionCutoffOneLinkBucketWords
