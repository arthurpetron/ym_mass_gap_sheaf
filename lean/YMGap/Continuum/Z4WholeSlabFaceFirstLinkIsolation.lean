/-
# A canonical production link for every corrected-slab face

Every physical coarse plaquette has four literal boundary links.  This file
chooses its first one and proves that the link lies in the corrected-slab
production carrier and that the face identifier lies in its incident list.
Combining this geometry with isolated-face link annihilation shows that a
globally isolated nonzero coarse label kills the complete slab link product.

This removes existential link choice from the pair-bubble whole-row proof.
It does not yet establish that the bubble source's face weights force the
required globally isolated target pattern.

Constructive contract: finite cubical geometry and exact SU(2) fusion data
only; no `Classical`, choice, `native_decide`, proof hole, noncomputable
declaration, trusted external computation, or new axiom.
-/

import YMGap.Continuum.Z4WholeSlabIsolatedFaceLinkAnnihilation

namespace YMGap.Continuum.Z4WholeSlabFaceFirstLinkIsolation

set_option autoImplicit false
set_option maxRecDepth 20000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4WholeSlabIsolatedFaceLinkAnnihilation

/-- The first genuine boundary edge of the plaquette represented by a slab
face identifier. -/
def slabFaceFirstLink (extent faceId : Nat) : Z4Link :=
  let face := slabPlaquetteAt extent faceId
  (face.1, (dirsOf face.2).1)

theorem slabFaceFirstLink_mem_edgesOf
    (extent faceId : Nat) :
    slabFaceFirstLink extent faceId ∈
      edgesOf (slabPlaquetteAt extent faceId) := by
  simp [slabFaceFirstLink, edgesOf]

/-- The selected edge belongs to the literal whole-slab link carrier whenever
the face identifier is physical. -/
theorem slabFaceFirstLink_mem_boundaryCompleteSlabLinks
    {extent faceId : Nat}
    (hface : faceId ∈ slabPhysicalFaceEdges extent) :
    slabFaceFirstLink extent faceId ∈
      boundaryCompleteSlabLinks extent := by
  apply (mem_boundaryCompleteSlabLinks_iff extent _).mpr
  exact ⟨slabPlaquetteAt extent faceId,
    slabPlaquetteAt_mem hface,
    slabFaceFirstLink_mem_edgesOf extent faceId⟩

/-- The selected face identifier occurs in the selected link's exact incident
face list. -/
theorem faceId_mem_slabIncidentPlaqIds_firstLink
    {extent faceId : Nat}
    (hface : faceId ∈ slabPhysicalFaceEdges extent) :
    faceId ∈
      slabIncidentPlaqIds extent (slabFaceFirstLink extent faceId) := by
  apply mem_slabIncidentPlaqIds.mpr
  exact ⟨slabPlaquetteAt extent faceId,
    slabPlaquetteAt_mem_enumerate hface,
    slabFaceFirstLink_mem_edgesOf extent faceId⟩

/-- Canonical-link form of the isolated-label annihilator.  Every incident
identifier is automatically a physical slab face, so a global off-selected
zero hypothesis specializes to the local incident word. -/
theorem slabExplicitLinkMultiplicityProduct_eq_zero_of_globally_isolated_face
    (K extent : Nat) (physical : Nat → Nat) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges extent)
    (hnonzero : physical faceId ≠ 0)
    (hbound : physical faceId ≤ linkAuxiliaryCutoff K)
    (hother : ∀ other,
      other ∈ slabPhysicalFaceEdges extent →
      other ≠ faceId → physical other = 0) :
    slabExplicitLinkMultiplicityProduct K extent physical = 0 := by
  let link := slabFaceFirstLink extent faceId
  apply
    slabExplicitLinkMultiplicityProduct_eq_zero_of_isolated_nonzero_face
      K extent physical link faceId
  · exact slabFaceFirstLink_mem_boundaryCompleteSlabLinks hface
  · exact faceId_mem_slabIncidentPlaqIds_firstLink hface
  · exact hnonzero
  · exact hbound
  · intro other hincident hne
    exact hother other (slabIncidentPlaqId_physical hincident) hne

#print axioms slabFaceFirstLink_mem_edgesOf
#print axioms slabFaceFirstLink_mem_boundaryCompleteSlabLinks
#print axioms faceId_mem_slabIncidentPlaqIds_firstLink
#print axioms slabExplicitLinkMultiplicityProduct_eq_zero_of_globally_isolated_face

end YMGap.Continuum.Z4WholeSlabFaceFirstLinkIsolation
