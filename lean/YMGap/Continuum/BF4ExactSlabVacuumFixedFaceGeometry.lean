/-
# Exposed-link geometry of the exact BF4 vacuum interface

With vacuum data on the lower and upper spatial faces, the literal extent-one
slab leaves only the twenty-four temporal plaquettes crossing the reflection
plane.  Each such plaquette has a distinguished spatial link on the lower
slice, and that link occurs in no other fixed plaquette.  This finite geometric
fact is the entry point for the remaining one-link Peter--Weyl orthogonality
argument: a nontrivial fixed-face character can be integrated first over its
exposed link.

No positivity statement is smuggled into this file.  It proves only the exact
incidence and side data needed by the analytic Haar gluing theorem.
-/

import YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork

namespace YMGap.Continuum.BF4ExactSlabVacuumFixedFaceGeometry

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-- The lower-slice spatial edge traversed first by a temporal plaquette.
The spatial-plane branches are irrelevant on `exactCorrectedSlabFixedFaces`
and merely make the definition total. -/
def exactFixedFaceExposedLink : Z4Plaq → Z4Link
  | (vertex, .p01) => (vertex, .x0)
  | (vertex, .p02) => (vertex, .x0)
  | (vertex, .p03) => (vertex, .x0)
  | (vertex, .p12) => (vertex, .x1)
  | (vertex, .p13) => (vertex, .x1)
  | (vertex, .p23) => (vertex, .x2)

private theorem exposed_incident_check :
    exactCorrectedSlabFixedFaces.all (fun face =>
      decide (exactFixedFaceExposedLink face ∈ edgesOf face)) = true := by
  decide

private theorem exposed_carrier_check :
    exactCorrectedSlabFixedFaces.all (fun face =>
      decide (exactFixedFaceExposedLink face ∈
        boundaryCompleteSlabLinks 1)) = true := by
  decide

private theorem exposed_lower_check :
    exactCorrectedSlabFixedFaces.all (fun face =>
      decide (linkHalfSide 0 (exactFixedFaceExposedLink face) =
        CrossPlaneSide.lower)) = true := by
  decide

private theorem exposed_unique_check :
    exactCorrectedSlabFixedFaces.all (fun face =>
      exactCorrectedSlabFixedFaces.all (fun other =>
        decide (exactFixedFaceExposedLink face ∈ edgesOf other →
          other = face))) = true := by
  decide

/-- Every literal fixed temporal face has a lower spatial link that belongs
to the 116-link Haar carrier and to no other fixed face. -/
theorem exactFixedFaceExposedLink_spec
    {face : Z4Plaq} (hface : face ∈ exactCorrectedSlabFixedFaces) :
    exactFixedFaceExposedLink face ∈ edgesOf face ∧
    exactFixedFaceExposedLink face ∈ boundaryCompleteSlabLinks 1 ∧
    linkHalfSide 0 (exactFixedFaceExposedLink face) =
      CrossPlaneSide.lower ∧
    ∀ other, other ∈ exactCorrectedSlabFixedFaces →
      exactFixedFaceExposedLink face ∈ edgesOf other → other = face := by
  have hincident := List.all_eq_true.mp exposed_incident_check face hface
  have hcarrier := List.all_eq_true.mp exposed_carrier_check face hface
  have hlower := List.all_eq_true.mp exposed_lower_check face hface
  have hunique := List.all_eq_true.mp exposed_unique_check face hface
  refine ⟨of_decide_eq_true hincident, of_decide_eq_true hcarrier,
    of_decide_eq_true hlower, ?_⟩
  intro other hother hotherIncident
  have hentry := List.all_eq_true.mp hunique other hother
  exact (of_decide_eq_true hentry) hotherIncident

/-- Constructive finite-support extraction: if a natural-valued function is
zero away from a finite list but is not identically zero, then the list
contains a point where it is nonzero. -/
private theorem finiteSupport_has_nonzero
    (boundary : Nat → Nat) (ids : List Nat)
    (hoff : ∀ id, id ∉ ids → boundary id = 0)
    (hnonzero : boundary ≠ fun _ => 0) :
    ∃ id, id ∈ ids ∧ boundary id ≠ 0 := by
  induction ids with
  | nil =>
      apply False.elim
      apply hnonzero
      funext id
      exact hoff id (by simp)
  | cons head tail ih =>
      by_cases hhead : boundary head = 0
      · have htailOff : ∀ id, id ∉ tail → boundary id = 0 := by
          intro id hid
          by_cases hidHead : id = head
          · simpa [hidHead] using hhead
          · exact hoff id (by simp [hidHead, hid])
        obtain ⟨id, hid, hvalue⟩ := ih htailOff
        exact ⟨id, by simp [hid], hvalue⟩
      · exact ⟨head, by simp, hhead⟩

/-- Every non-vacuum interface labelling has a genuinely nontrivial fixed
face.  Together with `exactFixedFaceExposedLink_spec`, this selects the first
Haar block on which nontrivial-character orthogonality must be applied. -/
theorem nonvacuumBoundary_has_nonzero_fixed_face
    {K : Nat} {boundary : EdgeLabelling}
    (hboundary : boundary ∈ centralBoundaryChannels K 0)
    (hnonvacuum : boundary ≠ zeroEdgeLabelling) :
    ∃ id, id ∈ centralFixedFaceIds 0 ∧ boundary id ≠ 0 := by
  have hsound := boundedEdgeLabellings_sound K
    (centralFixedFaceIds 0) boundary hboundary
  exact finiteSupport_has_nonzero boundary (centralFixedFaceIds 0)
    hsound.2 hnonvacuum

private theorem getD_idxOf_of_mem
    {A : Type} [BEq A] [LawfulBEq A]
    (fallback target : A) (items : List A)
    (hmem : target ∈ items) :
    items.getD (items.idxOf target) fallback = target := by
  have hlt := List.idxOf_lt_length_of_mem hmem
  have hfound : items[items.idxOf target] == target := by
    exact List.findIdx_getElem (w := hlt)
  have heq : items[items.idxOf target] = target :=
    LawfulBEq.eq_of_beq hfound
  have hget := List.getElem_eq_getD
    (l := items) (i := items.idxOf target) (h := hlt) fallback
  rw [← hget]
  exact heq

/-- On the physical extent-one face carrier, converting an identifier to its
literal plaquette and searching the noduplicated carrier returns the original
identifier. -/
theorem idxOf_slabPlaquetteAt_one
    {id : Nat} (hid : id ∈ slabPhysicalFaceEdges 1) :
    (boundaryCompleteSlabPlaquettes 1).idxOf
        (slabPlaquetteAt 1 id) = id := by
  have hface := slabPlaquetteAt_mem hid
  have hidxPhysical :
      (boundaryCompleteSlabPlaquettes 1).idxOf
          (slabPlaquetteAt 1 id) ∈
        slabPhysicalFaceEdges 1 :=
    List.mem_range.mpr (List.idxOf_lt_length_of_mem hface)
  apply slabPlaquetteAt_injective_on_physical hidxPhysical hid
  change slabPlaquetteAt 1
      ((boundaryCompleteSlabPlaquettes 1).idxOf
        (slabPlaquetteAt 1 id)) = slabPlaquetteAt 1 id
  exact getD_idxOf_of_mem fallbackPlaquette
    (slabPlaquetteAt 1 id) _ hface

/-- A non-vacuum fixed-interface labelling selects a literal temporal face
whose displayed character is nontrivial, together with the complete exposed
link specification needed to integrate that character first. -/
theorem nonvacuumBoundary_has_exposed_nontrivial_face
    {K : Nat} {boundary : EdgeLabelling}
    (hboundary : boundary ∈ centralBoundaryChannels K 0)
    (hnonvacuum : boundary ≠ zeroEdgeLabelling) :
    ∃ face,
      face ∈ exactCorrectedSlabFixedFaces ∧
      boundary
          ((boundaryCompleteSlabPlaquettes 1).idxOf face) ≠ 0 ∧
      exactFixedFaceExposedLink face ∈ edgesOf face ∧
      exactFixedFaceExposedLink face ∈ boundaryCompleteSlabLinks 1 ∧
      linkHalfSide 0 (exactFixedFaceExposedLink face) =
        CrossPlaneSide.lower ∧
      ∀ other, other ∈ exactCorrectedSlabFixedFaces →
        exactFixedFaceExposedLink face ∈ edgesOf other →
          other = face := by
  obtain ⟨id, hid, hvalue⟩ :=
    nonvacuumBoundary_has_nonzero_fixed_face hboundary hnonvacuum
  let face := slabPlaquetteAt 1 id
  have hidPhysical : id ∈ slabPhysicalFaceEdges 1 := by
    exact (mem_centralFixedFaceIds.mp hid).1
  have hfaceFixed : face ∈ exactCorrectedSlabFixedFaces := by
    exact List.mem_map.mpr ⟨id, hid, rfl⟩
  have hidx :
      (boundaryCompleteSlabPlaquettes 1).idxOf face = id := by
    exact idxOf_slabPlaquetteAt_one hidPhysical
  have hspec := exactFixedFaceExposedLink_spec hfaceFixed
  refine ⟨face, hfaceFixed, ?_, hspec⟩
  rw [hidx]
  exact hvalue

/-- The exact analytic target selected by the exposed-face theorem.  It is
stated at the unweighted 116-link Haar coefficient, so its truth is
independent of the coupling and of the positive heat coefficients. -/
def ExactVacuumNontrivialHaarTermsVanish (K : Nat) : Prop :=
  ∀ boundary,
    boundary ∈ centralBoundaryChannels K 0 →
    boundary ≠ zeroEdgeLabelling →
      exactCorrectedSlabHaarCoefficient 1
        (assembleReflectedSlabLabelling 0
          zeroEdgeLabelling boundary zeroEdgeLabelling) ≈
        0

end YMGap.Continuum.BF4ExactSlabVacuumFixedFaceGeometry

#print axioms YMGap.Continuum.BF4ExactSlabVacuumFixedFaceGeometry.exactFixedFaceExposedLink_spec
#print axioms YMGap.Continuum.BF4ExactSlabVacuumFixedFaceGeometry.idxOf_slabPlaquetteAt_one
#print axioms YMGap.Continuum.BF4ExactSlabVacuumFixedFaceGeometry.nonvacuumBoundary_has_nonzero_fixed_face
#print axioms YMGap.Continuum.BF4ExactSlabVacuumFixedFaceGeometry.nonvacuumBoundary_has_exposed_nontrivial_face
