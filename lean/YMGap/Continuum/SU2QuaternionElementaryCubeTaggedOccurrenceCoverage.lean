/-
# Tagged elementary-cube endpoint incidence and occurrence coverage

This leaf supplies the finite incidence certificates needed before the
right-local paired contraction network may be compared with a six-face
trace representative.  It identifies each of the twenty-four vertex-major
tags with a geometric cube vertex and proves that flattening the twelve
forward/reverse link rows is a constructive permutation of the twenty-four
face-major coefficient descriptors.

The permutation is proved from an explicit position witness using only
`List.Perm` constructors.  It does not use a bulk decidable permutation
reduction; an earlier generic formulation was rejected because its public
axiom gate exposed `Classical.choice`.  No Boolean assignment is enumerated
and no depth-twenty-four sum is unfolded, simplified, evaluated, or printed.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionElementaryCubeTaggedFundamentalContraction

namespace YMGap.Continuum.SU2QuaternionElementaryCubeTaggedOccurrenceCoverage

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionFundamentalMatrixSemantics
open YMGap.Continuum.SU2QuaternionDistinctBlockFundamentalContractionProduct
open YMGap.Continuum.SU2QuaternionElementaryCubeOrientedTraceWiring
open YMGap.Continuum.SU2QuaternionElementaryCubeTaggedFundamentalContraction
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveLinkCarrier

/-! ## 1. Constructive finite-permutation helper -/

/-- The concrete face-major to pair-major permutation, proved only with the
constructors of `List.Perm`.  Keeping the entries polymorphic lets the same
witness reindex positions, occurrences, descriptors, or polynomials without
calling a bulk decidable permutation reduction. -/
private theorem faceMajor_perm_pairMajor {A : Type}
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
     a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 : A) :
    [a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,
     a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23].Perm
    [a4,a3,a0,a11,a1,a19,a20,a2,a8,a7,a12,a6,
     a5,a23,a9,a15,a16,a10,a17,a14,a13,a22,a21,a18] := by
  refine List.Perm.trans (List.perm_middle
    (l₁ := [a0,a1,a2,a3]) (a := a4)
    (l₂ := [a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,
      a19,a20,a21,a22,a23])) ?_
  refine List.Perm.cons a4 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [a0,a1,a2]) (a := a3)
    (l₂ := [a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,
      a19,a20,a21,a22,a23])) ?_
  refine List.Perm.cons a3 ?_
  refine List.Perm.cons a0 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [a1,a2,a5,a6,a7,a8,a9,a10]) (a := a11)
    (l₂ := [a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23])) ?_
  refine List.Perm.cons a11 ?_
  refine List.Perm.cons a1 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [a2,a5,a6,a7,a8,a9,a10,a12,a13,a14,a15,a16,a17,a18])
    (a := a19) (l₂ := [a20,a21,a22,a23])) ?_
  refine List.Perm.cons a19 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [a2,a5,a6,a7,a8,a9,a10,a12,a13,a14,a15,a16,a17,a18])
    (a := a20) (l₂ := [a21,a22,a23])) ?_
  refine List.Perm.cons a20 ?_
  refine List.Perm.cons a2 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [a5,a6,a7]) (a := a8)
    (l₂ := [a9,a10,a12,a13,a14,a15,a16,a17,a18,a21,a22,a23])) ?_
  refine List.Perm.cons a8 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [a5,a6]) (a := a7)
    (l₂ := [a9,a10,a12,a13,a14,a15,a16,a17,a18,a21,a22,a23])) ?_
  refine List.Perm.cons a7 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [a5,a6,a9,a10]) (a := a12)
    (l₂ := [a13,a14,a15,a16,a17,a18,a21,a22,a23])) ?_
  refine List.Perm.cons a12 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [a5]) (a := a6)
    (l₂ := [a9,a10,a13,a14,a15,a16,a17,a18,a21,a22,a23])) ?_
  refine List.Perm.cons a6 ?_
  refine List.Perm.cons a5 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [a9,a10,a13,a14,a15,a16,a17,a18,a21,a22]) (a := a23)
    (l₂ := [])) ?_
  refine List.Perm.cons a23 ?_
  refine List.Perm.cons a9 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [a10,a13,a14]) (a := a15)
    (l₂ := [a16,a17,a18,a21,a22])) ?_
  refine List.Perm.cons a15 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [a10,a13,a14]) (a := a16)
    (l₂ := [a17,a18,a21,a22])) ?_
  refine List.Perm.cons a16 ?_
  refine List.Perm.cons a10 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [a13,a14]) (a := a17) (l₂ := [a18,a21,a22])) ?_
  refine List.Perm.cons a17 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [a13]) (a := a14) (l₂ := [a18,a21,a22])) ?_
  refine List.Perm.cons a14 ?_
  refine List.Perm.cons a13 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [a18,a21]) (a := a22) (l₂ := [])) ?_
  refine List.Perm.cons a22 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [a18]) (a := a21) (l₂ := [])) ?_
  refine List.Perm.cons a21 ?_
  exact List.Perm.refl _

/-- The smaller explicit permutation relating vertex-major order to the
order produced by deduplicating the boundary occurrences. -/
private theorem vertexMajor_perm_boundaryOrder {A : Type}
    (a0 a1 a2 a3 a4 a5 a6 a7 : A) :
    [a0,a1,a2,a3,a4,a5,a6,a7].Perm
      [a0,a3,a2,a1,a5,a4,a7,a6] := by
  refine List.Perm.cons a0 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [a1,a2]) (a := a3) (l₂ := [a4,a5,a6,a7])) ?_
  refine List.Perm.cons a3 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [a1]) (a := a2) (l₂ := [a4,a5,a6,a7])) ?_
  refine List.Perm.cons a2 ?_
  refine List.Perm.cons a1 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [a4]) (a := a5) (l₂ := [a6,a7])) ?_
  refine List.Perm.cons a5 ?_
  refine List.Perm.cons a4 ?_
  refine List.Perm.trans (List.perm_middle
    (l₁ := [a6]) (a := a7) (l₂ := [])) ?_
  refine List.Perm.cons a7 ?_
  exact List.Perm.refl _

/-! ## 2. Vertex-major tags agree with geometric endpoints -/

/-- The eight geometric cube vertices in vertex-major tag order. -/
def radiusZeroElementaryCubeVertexTagVertices : List Z4Vertex :=
  [(0, 0, 0, 1), (1, 0, 0, 1),
   (1, 1, 0, 1), (0, 1, 0, 1),
   (0, 0, 1, 1), (1, 0, 1, 1),
   (1, 1, 1, 1), (0, 1, 1, 1)]

theorem radiusZeroElementaryCubeVertexTagVertices_length :
    radiusZeroElementaryCubeVertexTagVertices.length = 8 := by
  decide

theorem radiusZeroElementaryCubeVertexTagVertices_nodup :
    radiusZeroElementaryCubeVertexTagVertices.Nodup := by
  decide

/-- The geometric vertex named by a tag.  The default is irrelevant for the
certified range `tag < 24`. -/
def radiusZeroElementaryCubeTagVertex (tag : Nat) : Z4Vertex :=
  radiusZeroElementaryCubeVertexTagVertices.getD
    (tag / 3) (0, 0, 0, 1)

/-- Consecutive triples of tags name the same vertex, and all eight vertices
occur in the intended order. -/
theorem radiusZeroElementaryCubeTagVertex_range_exact :
    (List.range 24).map radiusZeroElementaryCubeTagVertex =
      radiusZeroElementaryCubeVertexTagVertices.flatMap
        (fun vertex => [vertex, vertex, vertex]) := by
  decide

/-- Every one of the eight vertex-major vertices has exactly three tags. -/
theorem radiusZeroElementaryCubeTagVertex_fiber_length_three
    {vertex : Z4Vertex}
    (hvertex : vertex ∈ radiusZeroElementaryCubeVertexTagVertices) :
    ((List.range 24).filter (fun tag =>
      decide (radiusZeroElementaryCubeTagVertex tag = vertex))).length = 3 := by
  simp only [radiusZeroElementaryCubeVertexTagVertices,
    List.mem_cons, List.not_mem_nil, or_false] at hvertex
  rcases hvertex with rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;> decide

/-- Concrete order produced by deduplicating the outward boundary
occurrences.  This is recorded only to relate the vertex-major order to the
already audited geometric carrier. -/
theorem radiusZeroElementaryCubeBoundaryVertices_exact :
    radiusZeroElementaryCubeBoundaryVertices =
      [(0, 0, 0, 1), (0, 1, 0, 1),
       (1, 1, 0, 1), (1, 0, 0, 1),
       (1, 0, 1, 1), (0, 0, 1, 1),
       (0, 1, 1, 1), (1, 1, 1, 1)] := by
  decide

/-- Vertex-major order is a constructive permutation of the independent
geometry-derived boundary-vertex carrier. -/
theorem radiusZeroElementaryCubeVertexTagVertices_perm_boundaryVertices :
    radiusZeroElementaryCubeVertexTagVertices.Perm
      radiusZeroElementaryCubeBoundaryVertices := by
  rw [radiusZeroElementaryCubeBoundaryVertices_exact]
  exact vertexMajor_perm_boundaryOrder _ _ _ _ _ _ _ _

/-- Boolean endpoint check for one tagged boundary occurrence. -/
def taggedCubeBoundaryOccurrenceTagEndpointsCoherentB
    (tagged : TaggedCubeBoundaryOccurrence) : Bool :=
  decide (radiusZeroElementaryCubeTagVertex tagged.sourceTag =
      tagged.occurrence.sourceVertex) &&
    decide (radiusZeroElementaryCubeTagVertex tagged.targetTag =
      tagged.occurrence.targetVertex)

/-- In face-major order, the tag-edge source and target vertices agree
position by position with the audited oriented physical occurrences. -/
theorem radiusZeroElementaryCubeBoundaryTagEndpoints_exact :
    radiusZeroElementaryCubeBoundaryTagEdges.map (fun edge =>
        (radiusZeroElementaryCubeTagVertex edge.1,
          radiusZeroElementaryCubeTagVertex edge.2)) =
      radiusZeroElementaryCubeBoundaryOccurrences.map (fun occurrence =>
        (occurrence.sourceVertex, occurrence.targetVertex)) := by
  decide

/-- All twenty-four positional endpoint checks succeed. -/
def radiusZeroElementaryCubeTaggedEndpointChecks : List Bool :=
  radiusZeroElementaryCubeTaggedBoundaryOccurrences.map (fun tagged =>
    taggedCubeBoundaryOccurrenceTagEndpointsCoherentB tagged)

theorem radiusZeroElementaryCubeTaggedEndpointChecks_exact :
    radiusZeroElementaryCubeTaggedEndpointChecks =
      List.replicate 24 true := by
  decide

/-- Every face-major tagged occurrence carries the tags of its literal
geometric source and target. -/
theorem radiusZeroElementaryCubeTaggedBoundaryOccurrence_tagEndpointsCoherent
    {tagged : TaggedCubeBoundaryOccurrence}
    (htagged : tagged ∈
      radiusZeroElementaryCubeTaggedBoundaryOccurrences) :
    radiusZeroElementaryCubeTagVertex tagged.sourceTag =
        tagged.occurrence.sourceVertex ∧
      radiusZeroElementaryCubeTagVertex tagged.targetTag =
        tagged.occurrence.targetVertex := by
  have hmember :
      taggedCubeBoundaryOccurrenceTagEndpointsCoherentB tagged ∈
      radiusZeroElementaryCubeTaggedEndpointChecks := by
    unfold radiusZeroElementaryCubeTaggedEndpointChecks
    exact List.mem_map.mpr ⟨tagged, htagged, rfl⟩
  rw [radiusZeroElementaryCubeTaggedEndpointChecks_exact] at hmember
  have htrue :
      taggedCubeBoundaryOccurrenceTagEndpointsCoherentB tagged = true := by
    simpa using hmember
  unfold taggedCubeBoundaryOccurrenceTagEndpointsCoherentB at htrue
  rw [Bool.and_eq_true] at htrue
  exact ⟨of_decide_eq_true htrue.1, of_decide_eq_true htrue.2⟩

/-! ## 3. Face-major and paired coefficient descriptors -/

/-- The raw data selecting one fundamental matrix coefficient.  Physical
links are retained here; the production quaternion block is derived by the
already audited active-link index. -/
structure CubeCoefficientDescriptor where
  physicalLink : Z4Link
  positive : Bool
  rowTag : Nat
  columnTag : Nat
  deriving DecidableEq

def CubeCoefficientDescriptor.block
    (descriptor : CubeCoefficientDescriptor) : Nat :=
  adjacentEvenActiveLinkIndex 0 descriptor.physicalLink

/-- Polynomial coefficient selected by a descriptor and one opaque
vertex-major Boolean assignment. -/
def CubeCoefficientDescriptor.coefficient
    (descriptor : CubeCoefficientDescriptor)
    (assignment : List Bool) : ComplexRatPoly :=
  if descriptor.positive then
    forwardFundamentalCoefficient descriptor.block
      (cubeTagValue assignment descriptor.rowTag)
      (cubeTagValue assignment descriptor.columnTag)
  else
    reverseFundamentalCoefficient descriptor.block
      (cubeTagValue assignment descriptor.rowTag)
      (cubeTagValue assignment descriptor.columnTag)

def taggedCubeBoundaryOccurrenceCoefficientDescriptor
    (tagged : TaggedCubeBoundaryOccurrence) : CubeCoefficientDescriptor :=
  { physicalLink := tagged.occurrence.physicalLink
    positive := tagged.occurrence.positive
    rowTag := tagged.sourceTag
    columnTag := tagged.targetTag }

def taggedCubeLinkPairForwardCoefficientDescriptor
    (pair : TaggedCubeLinkPair) : CubeCoefficientDescriptor :=
  { physicalLink := pair.physicalLink
    positive := true
    rowTag := pair.forwardRowTag
    columnTag := pair.forwardColumnTag }

def taggedCubeLinkPairReverseCoefficientDescriptor
    (pair : TaggedCubeLinkPair) : CubeCoefficientDescriptor :=
  { physicalLink := pair.physicalLink
    positive := false
    rowTag := pair.reverseRowTag
    columnTag := pair.reverseColumnTag }

def taggedCubeLinkPairCoefficientDescriptors
    (pair : TaggedCubeLinkPair) : List CubeCoefficientDescriptor :=
  [taggedCubeLinkPairForwardCoefficientDescriptor pair,
   taggedCubeLinkPairReverseCoefficientDescriptor pair]

/-- The two descriptors of a link row select exactly the raw polynomial used
by its oriented fundamental contraction. -/
theorem taggedCubeLinkPairCoefficientMul_eq_contractionPolynomial
    (pair : TaggedCubeLinkPair) (assignment : List Bool) :
    complexRatPolyMul
        ((taggedCubeLinkPairForwardCoefficientDescriptor pair).coefficient
          assignment)
        ((taggedCubeLinkPairReverseCoefficientDescriptor pair).coefficient
          assignment) =
      (TaggedCubeLinkPair.contraction pair assignment).polynomial := by
  unfold taggedCubeLinkPairForwardCoefficientDescriptor
    taggedCubeLinkPairReverseCoefficientDescriptor
    CubeCoefficientDescriptor.coefficient CubeCoefficientDescriptor.block
    TaggedCubeLinkPair.contraction OrientedFundamentalContraction.polynomial
    orientedFundamentalLinkContraction
  simp

/-- Twenty-four descriptors in six-face occurrence order. -/
def radiusZeroElementaryCubeFaceMajorCoefficientDescriptors :
    List CubeCoefficientDescriptor :=
  radiusZeroElementaryCubeTaggedBoundaryOccurrences.map
    taggedCubeBoundaryOccurrenceCoefficientDescriptor

/-- Twenty-four descriptors in schedule order, forward then reverse within
each of the twelve rows.  This is the schedule-order flattening, not the raw
left-to-right syntactic factor order of the right-local contraction product. -/
def radiusZeroElementaryCubePairedCoefficientDescriptors :
    List CubeCoefficientDescriptor :=
  radiusZeroElementaryCubeTaggedLinkPairs.flatMap
    taggedCubeLinkPairCoefficientDescriptors

theorem radiusZeroElementaryCubeFaceMajorCoefficientDescriptors_length :
    radiusZeroElementaryCubeFaceMajorCoefficientDescriptors.length = 24 := by
  decide

theorem radiusZeroElementaryCubePairedCoefficientDescriptors_length :
    radiusZeroElementaryCubePairedCoefficientDescriptors.length = 24 := by
  decide

theorem radiusZeroElementaryCubeFaceMajorCoefficientDescriptors_nodup :
    radiusZeroElementaryCubeFaceMajorCoefficientDescriptors.Nodup := by
  decide

theorem radiusZeroElementaryCubePairedCoefficientDescriptors_nodup :
    radiusZeroElementaryCubePairedCoefficientDescriptors.Nodup := by
  decide

/-! ## 4. Explicit constructive coverage permutation -/

/-- In paired-row reading order, the positions of the selected descriptors
inside the face-major occurrence list. -/
def radiusZeroElementaryCubePairedOccurrenceFacePositions : List Nat :=
  [4, 3, 0, 11, 1, 19, 20, 2, 8, 7, 12, 6,
   5, 23, 9, 15, 16, 10, 17, 14, 13, 22, 21, 18]

theorem radiusZeroElementaryCubePairedOccurrenceFacePositions_length :
    radiusZeroElementaryCubePairedOccurrenceFacePositions.length = 24 := by
  decide

theorem radiusZeroElementaryCubePairedOccurrenceFacePositions_nodup :
    radiusZeroElementaryCubePairedOccurrenceFacePositions.Nodup := by
  decide

theorem radiusZeroElementaryCubePairedOccurrenceFacePositions_mem_iff
    (position : Nat) :
    position ∈ radiusZeroElementaryCubePairedOccurrenceFacePositions ↔
      position < 24 := by
  simp only [radiusZeroElementaryCubePairedOccurrenceFacePositions,
    List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- The explicit position witness is a constructive permutation of all
twenty-four face-major slots. -/
theorem radiusZeroElementaryCubePairedOccurrenceFacePositions_perm_range :
    radiusZeroElementaryCubePairedOccurrenceFacePositions.Perm
      (List.range 24) := by
  simpa [radiusZeroElementaryCubePairedOccurrenceFacePositions] using
    (faceMajor_perm_pairMajor (A := Nat)
      0 1 2 3 4 5 6 7 8 9 10 11
      12 13 14 15 16 17 18 19 20 21 22 23).symm

def defaultCubeCoefficientDescriptor : CubeCoefficientDescriptor :=
  { physicalLink := ((0, 0, 0, 1), .x0)
    positive := true
    rowTag := 0
    columnTag := 0 }

def radiusZeroElementaryCubeFaceMajorCoefficientDescriptorAt
    (position : Nat) : CubeCoefficientDescriptor :=
  radiusZeroElementaryCubeFaceMajorCoefficientDescriptors.getD
    position defaultCubeCoefficientDescriptor

/-- The paired row table is literally obtained by the displayed positional
reindexing of the face-major descriptor list. -/
theorem radiusZeroElementaryCubePairedCoefficientDescriptors_eq_reindex :
    radiusZeroElementaryCubePairedCoefficientDescriptors =
      radiusZeroElementaryCubePairedOccurrenceFacePositions.map
        radiusZeroElementaryCubeFaceMajorCoefficientDescriptorAt := by
  decide

theorem radiusZeroElementaryCubeFaceDescriptorAt_range :
    (List.range 24).map
        radiusZeroElementaryCubeFaceMajorCoefficientDescriptorAt =
      radiusZeroElementaryCubeFaceMajorCoefficientDescriptors := by
  decide

/-- **Descriptor-level global occurrence coverage.**  The twelve
forward/reverse link rows cover every face-major tagged coefficient exactly
once. -/
theorem radiusZeroElementaryCubePairedCoefficientDescriptors_perm_faceMajor :
    radiusZeroElementaryCubePairedCoefficientDescriptors.Perm
      radiusZeroElementaryCubeFaceMajorCoefficientDescriptors := by
  rw [radiusZeroElementaryCubePairedCoefficientDescriptors_eq_reindex]
  have hperm :=
    radiusZeroElementaryCubePairedOccurrenceFacePositions_perm_range.map
      radiusZeroElementaryCubeFaceMajorCoefficientDescriptorAt
  rw [radiusZeroElementaryCubeFaceDescriptorAt_range] at hperm
  exact hperm

/-- Mapping the coverage permutation through an opaque assignment gives the
exact factor permutation needed by the next Haar-reordering leaf. -/
theorem radiusZeroElementaryCubePairedCoefficientPolynomials_perm_faceMajor
    (assignment : List Bool) :
    (radiusZeroElementaryCubePairedCoefficientDescriptors.map
        (fun descriptor => descriptor.coefficient assignment)).Perm
      (radiusZeroElementaryCubeFaceMajorCoefficientDescriptors.map
        (fun descriptor => descriptor.coefficient assignment)) :=
  radiusZeroElementaryCubePairedCoefficientDescriptors_perm_faceMajor.map _

/-- The pair-major descriptor factors are definitionally the forward/reverse
coefficient factors of the established twelve-step contraction schedule. -/
theorem radiusZeroElementaryCubePairedCoefficientPolynomials_eq_scheduleFactors
    (assignment : List Bool) :
    radiusZeroElementaryCubePairedCoefficientDescriptors.map
        (fun descriptor => descriptor.coefficient assignment) =
      (radiusZeroElementaryCubeContractionSchedule assignment).flatMap
        (fun step =>
          [forwardFundamentalCoefficient step.block
              step.forwardRow step.forwardColumn,
           reverseFundamentalCoefficient step.block
              step.reverseRow step.reverseColumn]) := by
  unfold radiusZeroElementaryCubePairedCoefficientDescriptors
    radiusZeroElementaryCubeContractionSchedule
    radiusZeroElementaryCubeTaggedLinkPairs
    taggedCubeLinkPairCoefficientDescriptors
    taggedCubeLinkPairForwardCoefficientDescriptor
    taggedCubeLinkPairReverseCoefficientDescriptor
    CubeCoefficientDescriptor.coefficient CubeCoefficientDescriptor.block
    TaggedCubeLinkPair.contraction
  simp

/-! ## 5. Literal occurrence projection -/

/-- Reconstruct the canonical oriented occurrence retained by a coefficient
descriptor.  Endpoint incidence proves that this agrees with the original
face-major tagged occurrence. -/
def CubeCoefficientDescriptor.taggedOccurrence
    (descriptor : CubeCoefficientDescriptor) :
    TaggedCubeBoundaryOccurrence :=
  { occurrence :=
      { physicalLink := descriptor.physicalLink
        sourceVertex := if descriptor.positive then
            descriptor.physicalLink.1
          else addE descriptor.physicalLink.1 descriptor.physicalLink.2
        targetVertex := if descriptor.positive then
            addE descriptor.physicalLink.1 descriptor.physicalLink.2
          else descriptor.physicalLink.1
        positive := descriptor.positive }
    sourceTag := descriptor.rowTag
    targetTag := descriptor.columnTag }

theorem radiusZeroElementaryCubeFaceMajorDescriptors_taggedOccurrences :
    radiusZeroElementaryCubeFaceMajorCoefficientDescriptors.map
        CubeCoefficientDescriptor.taggedOccurrence =
      radiusZeroElementaryCubeTaggedBoundaryOccurrences := by
  decide

/-- Literal occurrence-level form of the global coverage theorem. -/
theorem radiusZeroElementaryCubePairedDescriptors_taggedOccurrences_perm :
    (radiusZeroElementaryCubePairedCoefficientDescriptors.map
        CubeCoefficientDescriptor.taggedOccurrence).Perm
      radiusZeroElementaryCubeTaggedBoundaryOccurrences := by
  have hperm :=
    radiusZeroElementaryCubePairedCoefficientDescriptors_perm_faceMajor.map
      CubeCoefficientDescriptor.taggedOccurrence
  rw [radiusZeroElementaryCubeFaceMajorDescriptors_taggedOccurrences] at hperm
  exact hperm

#print axioms radiusZeroElementaryCubeVertexTagVertices_perm_boundaryVertices
#print axioms radiusZeroElementaryCubeTagVertex_fiber_length_three
#print axioms radiusZeroElementaryCubeBoundaryTagEndpoints_exact
#print axioms radiusZeroElementaryCubeTaggedBoundaryOccurrence_tagEndpointsCoherent
#print axioms taggedCubeLinkPairCoefficientMul_eq_contractionPolynomial
#print axioms radiusZeroElementaryCubeFaceMajorCoefficientDescriptors_nodup
#print axioms radiusZeroElementaryCubePairedCoefficientDescriptors_nodup
#print axioms radiusZeroElementaryCubePairedOccurrenceFacePositions_perm_range
#print axioms radiusZeroElementaryCubePairedCoefficientDescriptors_perm_faceMajor
#print axioms radiusZeroElementaryCubePairedCoefficientPolynomials_perm_faceMajor
#print axioms radiusZeroElementaryCubePairedCoefficientPolynomials_eq_scheduleFactors
#print axioms radiusZeroElementaryCubePairedDescriptors_taggedOccurrences_perm

end YMGap.Continuum.SU2QuaternionElementaryCubeTaggedOccurrenceCoverage
