/-
# Edge-touching double-cube shared-link orientation and scalar Haar trace

The radius-zero edge-touching double cube has one certified four-valent link.
This leaf attaches an explicit outward orientation to both cube boundaries,
keeps the four exceptional face occurrences tagged by their production face
identifiers, and proves their exact polarity word

    [reverse, forward, reverse, forward].

It then compares two scalar quantities at that one link: the trace of the
signed normalized four-coefficient Haar projector and the production
invariant-space cardinality. Both equal two. This agreement is deliberately
only a closed-trace statement. The negative `-1/6` mixed projector entry from
the upstream leaf remains essential for any surrounding network contraction.

No twelve-face trace product or depth-forty-eight Boolean sum is defined,
unfolded, reduced, or materialized here.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionOneLinkFourValentHaarProjector
import YMGap.Continuum.SU2QuaternionElementaryCubeOrientedTraceWiring
import YMGap.Continuum.Z4SingleFourIncidenceActivity

namespace YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeSharedLinkHaarNormalization

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionElementaryCubeOrientedTraceWiring
open YMGap.Continuum.SU2QuaternionOneLinkFourValentHaarProjector
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenRadiusZeroClosedGeometryFence
open YMGap.Continuum.Z4SingleFourIncidenceActivity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Two outward cube boundaries in the audited face order -/

/-- Outward orientations in the exact order of the twelve audited faces.

The first cube occupies positions `0,1,2,3,4,10`; the second occupies
`5,6,7,8,9,11`. Each cube has the lower/upper orientation pattern
`reversed,standard,reversed,standard,reversed,standard`. -/
def radiusZeroEdgeTouchingDoubleCubeOutwardOrientationMask :
    List FundamentalFaceOrientation :=
  [.reversed, .standard, .reversed, .standard, .reversed,
   .reversed, .standard, .reversed, .standard, .reversed,
   .standard, .standard]

theorem radiusZeroEdgeTouchingDoubleCubeOutwardOrientationMask_length :
    radiusZeroEdgeTouchingDoubleCubeOutwardOrientationMask.length = 12 := by
  decide

/-- Production face ID, decoded plaquette, and chosen outward orientation. -/
def radiusZeroEdgeTouchingDoubleCubeOutwardFaces :
    List ((Nat × Z4Plaq) × FundamentalFaceOrientation) :=
  (radiusZeroEdgeTouchingDoubleCubeFaceIds.zip
      radiusZeroEdgeTouchingDoubleCubeFaces).zip
    radiusZeroEdgeTouchingDoubleCubeOutwardOrientationMask

theorem radiusZeroEdgeTouchingDoubleCubeOutwardFaces_length :
    radiusZeroEdgeTouchingDoubleCubeOutwardFaces.length = 12 := by
  decide

theorem radiusZeroEdgeTouchingDoubleCubeOutwardFaces_map_ids :
    radiusZeroEdgeTouchingDoubleCubeOutwardFaces.map
      (fun taggedFace => taggedFace.1.1) =
        radiusZeroEdgeTouchingDoubleCubeFaceIds := by
  decide

theorem radiusZeroEdgeTouchingDoubleCubeOutwardFaces_map_plaquettes :
    radiusZeroEdgeTouchingDoubleCubeOutwardFaces.map
      (fun taggedFace => taggedFace.1.2) =
        radiusZeroEdgeTouchingDoubleCubeFaces := by
  decide

/-- All forty-eight oriented link occurrences, retaining the originating
production face identifier. -/
def radiusZeroEdgeTouchingDoubleCubeBoundaryOccurrences :
    List (Nat × OrientedFundamentalLinkOccurrence) :=
  radiusZeroEdgeTouchingDoubleCubeOutwardFaces.flatMap (fun taggedFace =>
    (plaquetteBoundaryOccurrences taggedFace.2 taggedFace.1.2).map
      (fun occurrence => (taggedFace.1.1, occurrence)))

theorem radiusZeroEdgeTouchingDoubleCubeBoundaryOccurrences_length :
    radiusZeroEdgeTouchingDoubleCubeBoundaryOccurrences.length = 48 := by
  decide

/-- Every tagged occurrence has the endpoint coherence certified by its
chosen standard or reversed plaquette word. -/
theorem radiusZeroEdgeTouchingDoubleCubeBoundaryOccurrence_coherent
    {taggedOccurrence : Nat × OrientedFundamentalLinkOccurrence}
    (hoccurrence : taggedOccurrence ∈
      radiusZeroEdgeTouchingDoubleCubeBoundaryOccurrences) :
    taggedOccurrence.2.Coherent := by
  unfold radiusZeroEdgeTouchingDoubleCubeBoundaryOccurrences at hoccurrence
  obtain ⟨taggedFace, _, hlocal⟩ := List.mem_flatMap.mp hoccurrence
  obtain ⟨occurrence, hlocalOccurrence, heq⟩ := List.mem_map.mp hlocal
  subst taggedOccurrence
  obtain ⟨⟨faceId, plaquette⟩, orientation⟩ := taggedFace
  cases orientation with
  | standard =>
      exact standardPlaquetteBoundaryOccurrence_coherent
        plaquette hlocalOccurrence
  | reversed =>
      exact reversedPlaquetteBoundaryOccurrence_coherent
        plaquette hlocalOccurrence

/-! ## 2. Literal four-occurrence orientation at the shared link -/

/-- The four tagged occurrences carried by the unique four-valent link. -/
def radiusZeroEdgeTouchingDoubleCubeSharedLinkOccurrences :
    List (Nat × OrientedFundamentalLinkOccurrence) :=
  radiusZeroEdgeTouchingDoubleCubeBoundaryOccurrences.filter
    (fun taggedOccurrence => decide
      (taggedOccurrence.2.physicalLink =
        radiusZeroEdgeTouchingDoubleCubeSharedLink))

theorem radiusZeroEdgeTouchingDoubleCubeSharedLinkOccurrences_length :
    radiusZeroEdgeTouchingDoubleCubeSharedLinkOccurrences.length = 4 := by
  decide

/-- The exceptional occurrences arise from exactly these four audited face
IDs, in the inherited production order. -/
theorem radiusZeroEdgeTouchingDoubleCubeSharedLinkOccurrence_faceIds :
    radiusZeroEdgeTouchingDoubleCubeSharedLinkOccurrences.map Prod.fst =
      [21, 52, 66, 67] := by
  decide

/-- **Exact two-forward/two-reverse orientation word.** The two sheets each
contribute one occurrence in each physical-link direction. -/
theorem radiusZeroEdgeTouchingDoubleCubeSharedLinkOccurrence_polarities :
    radiusZeroEdgeTouchingDoubleCubeSharedLinkOccurrences.map
      (fun taggedOccurrence => taggedOccurrence.2.positive) =
        [false, true, false, true] := by
  decide

/-- **Exact external matrix-index order at the shared link.** For each of the
four face IDs above, the pair is `(row vertex, column vertex)` in the cyclic
plaquette trace. Thus the reverse occurrences carry the endpoints in the
opposite order from the forward occurrences; the fourth-moment projector's
reverse row/column transpose is fixed geometrically rather than inferred from
the incidence count. -/
theorem radiusZeroEdgeTouchingDoubleCubeSharedLinkOccurrence_rowColumnVertices :
    radiusZeroEdgeTouchingDoubleCubeSharedLinkOccurrences.map
      (fun taggedOccurrence =>
        (taggedOccurrence.2.sourceVertex,
          taggedOccurrence.2.targetVertex)) =
      [(((1, 1, 1, 1) : Z4Vertex), ((0, 1, 1, 1) : Z4Vertex)),
       (((0, 1, 1, 1) : Z4Vertex), ((1, 1, 1, 1) : Z4Vertex)),
       (((1, 1, 1, 1) : Z4Vertex), ((0, 1, 1, 1) : Z4Vertex)),
       (((0, 1, 1, 1) : Z4Vertex), ((1, 1, 1, 1) : Z4Vertex))] := by
  decide

theorem radiusZeroEdgeTouchingDoubleCubeSharedLink_two_each_direction :
    (radiusZeroEdgeTouchingDoubleCubeSharedLinkOccurrences.filter
      (fun taggedOccurrence => taggedOccurrence.2.positive)).length = 2 ∧
    (radiusZeroEdgeTouchingDoubleCubeSharedLinkOccurrences.filter
      (fun taggedOccurrence => !taggedOccurrence.2.positive)).length = 2 := by
  decide

/-! ## 3. Closed Haar trace versus production scalar multiplicity -/

/-- The production link factor at the certified four-incidence edge is two. -/
theorem radiusZeroEdgeTouchingDoubleCubeSharedLink_productionFactor_eq_two :
    geometricLinkMultiplicityFactor
      radiusZeroEdgeTouchingDoubleCubeFaces
      radiusZeroEdgeTouchingDoubleCubeSharedLink = 2 :=
  geometricLinkMultiplicityFactor_eq_two_of_incidence_four
    radiusZeroEdgeTouchingDoubleCubeSharedLink_incidence_four

/-- The traced honest projector and the production scalar link factor agree.
This does not identify the scalar factor with the untraced signed kernel. -/
theorem finiteProductHaarComplex_oneLinkFourValentClosedTrace_eq_productionFactor :
    RationalComplexEqv
      (finiteProductHaarComplex 1
        oneLinkFourValentClosedTracePolynomial)
      (geometricLinkMultiplicityFactor
        radiusZeroEdgeTouchingDoubleCubeFaces
        radiusZeroEdgeTouchingDoubleCubeSharedLink, 0) := by
  rw [radiusZeroEdgeTouchingDoubleCubeSharedLink_productionFactor_eq_two]
  exact finiteProductHaarComplex_oneLinkFourValentClosedTrace_exact

#print axioms radiusZeroEdgeTouchingDoubleCubeOutwardFaces_map_ids
#print axioms radiusZeroEdgeTouchingDoubleCubeOutwardFaces_map_plaquettes
#print axioms radiusZeroEdgeTouchingDoubleCubeBoundaryOccurrence_coherent
#print axioms radiusZeroEdgeTouchingDoubleCubeSharedLinkOccurrence_faceIds
#print axioms radiusZeroEdgeTouchingDoubleCubeSharedLinkOccurrence_polarities
#print axioms radiusZeroEdgeTouchingDoubleCubeSharedLinkOccurrence_rowColumnVertices
#print axioms radiusZeroEdgeTouchingDoubleCubeSharedLink_two_each_direction
#print axioms radiusZeroEdgeTouchingDoubleCubeSharedLink_productionFactor_eq_two
#print axioms finiteProductHaarComplex_oneLinkFourValentClosedTrace_eq_productionFactor

end YMGap.Continuum.SU2QuaternionEdgeTouchingDoubleCubeSharedLinkHaarNormalization
