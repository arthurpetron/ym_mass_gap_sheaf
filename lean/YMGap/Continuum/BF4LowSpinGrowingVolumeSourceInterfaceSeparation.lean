/-
# Low-spin source separation from the reflection interface

The growing low-spin source cubes are spatial surfaces on time slices
`0, ..., volume`, while the reflection half is `volume + 1`.  Hence every
actual link touched by any selected cube lies strictly below the interface,
and every face incident on such a link is classified as lower.

This is the geometric core needed to factor a selected cube from an arbitrary
fixed/upper completion.  The completion factorization and raw-row equality
are not asserted in this module.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeFixedReferenceCompletionInjectionGate
import YMGap.Continuum.Z4HalfTimeReflectionLowerSupportLocalQuery

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeSourceInterfaceSeparation

set_option maxRecDepth 500000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Continuum
open YMGap.Continuum.BF4LowSpinGrowingVolumeReflectedCarrier
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4DyadicSlabCubeManyTimeSliceProjectedFamily
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4ExplicitExcitationLocalization
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLowerSupportLocalQuery
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientWeights
open YMGap.Continuum.Z4LinkIdentifierFreshness
open YMGap.Continuum.Z4LinkSeparatedComponentFactorization
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels

private theorem shiftedSurfaceEdge_time_and_spatial
    {shift : Nat} {plaquette : Z4Plaq} {link : Z4Link}
    (hplaquette : plaquette ∈ shiftedOddFineCubeSurface shift)
    (hlink : link ∈ edgesOf plaquette) :
    link.1.2.2.2 = shift ∧
      (link.2 = .x0 ∨ link.2 = .x1 ∨ link.2 = .x2) := by
  have htime := shiftedOddFineCubeSurface_time hplaquette
  have hplane := shiftedOddFineCubeSurface_spatialPlane hplaquette
  obtain ⟨⟨a, b, c, time⟩, plane⟩ := plaquette
  simp only at htime hplane
  rcases hplane with hplane | hplane | hplane
  all_goals subst plane
  all_goals simp only [edgesOf, dirsOf, addE, List.mem_cons,
    List.not_mem_nil, or_false] at hlink
  all_goals rcases hlink with rfl | rfl | rfl | rfl
  all_goals constructor
  all_goals try omega
  all_goals simp

private theorem spatialLink_incidentFace_lower
    {half : Nat} {plaquette : Z4Plaq} {link : Z4Link}
    (htime : link.1.2.2.2 < half)
    (hdirection : link.2 = .x0 ∨ link.2 = .x1 ∨ link.2 = .x2)
    (hlink : link ∈ edgesOf plaquette) :
    plaquetteHalfSide half plaquette = .lower := by
  obtain ⟨⟨a, b, c, time⟩, plane⟩ := plaquette
  cases plane <;>
    simp only [edgesOf, dirsOf, addE, List.mem_cons,
      List.not_mem_nil, or_false] at hlink <;>
    rcases hlink with rfl | rfl | rfl | rfl <;>
    simp only at hdirection htime ⊢ <;>
    simp [plaquetteHalfSide, spatialHalfSide, temporalHalfSide] <;>
    omega

/-- Every face of a selected low-spin source cube is strictly on the lower
side of the reflection decomposition. -/
theorem lowSpinCentralSourceFace_lower
    {volume : Nat} (index : LowSpinCentralIndex volume)
    {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ shiftedOddFineCubeSurface index.val) :
    plaquetteHalfSide (volume + 1) plaquette = .lower := by
  have htime := shiftedOddFineCubeSurface_time hplaquette
  have hplane := shiftedOddFineCubeSurface_spatialPlane hplaquette
  have hindex := List.mem_range.mp index.property
  rcases hplane with hplane | hplane | hplane
  all_goals obtain ⟨⟨a, b, c, time⟩, plane⟩ := plaquette
  all_goals simp only at htime hplane
  all_goals subst plane
  all_goals simp only [plaquetteHalfSide, spatialHalfSide]
  all_goals rw [if_pos (by omega)]

/-- Every face sharing an actual link with a selected low-spin source cube is
strictly on the lower side of the reflection decomposition. -/
theorem lowSpinCentralSourceLink_incidentFace_lower
    {volume : Nat} (index : LowSpinCentralIndex volume)
    {sourceFace otherFace : Z4Plaq} {link : Z4Link}
    (hsourceFace :
      sourceFace ∈ shiftedOddFineCubeSurface index.val)
    (hsourceLink : link ∈ edgesOf sourceFace)
    (hotherLink : link ∈ edgesOf otherFace) :
    plaquetteHalfSide (volume + 1) otherFace = .lower := by
  have hinfo := shiftedSurfaceEdge_time_and_spatial
    hsourceFace hsourceLink
  have hindex := List.mem_range.mp index.property
  apply spatialLink_incidentFace_lower
  · rw [hinfo.1]
    exact hindex
  · exact hinfo.2
  · exact hotherLink

/-! ## 2. The fixed/upper completion remainder vanishes below the interface -/

/-- Remove the selected lower source while leaving the fixed boundary and
reflected positive target unchanged. -/
def lowSpinCentralCompletionRemainder
    (volume : Nat) (boundary target : EdgeLabelling) : EdgeLabelling :=
  assembleReflectedSlabLabelling (volume + 1)
    zeroEdgeLabelling boundary target

/-- Ambient zero extension of the source-free completion remainder. -/
def lowSpinCentralCompletionRemainderAmbient
    (volume : Nat) (boundary target : EdgeLabelling) : EdgeLabelling :=
  slabToAmbientPhysical (centralExtent (volume + 1))
    (lowSpinCentralCompletionRemainder volume boundary target)

theorem lowSpinCentralCompletionRemainder_zero_on_lower
    {volume id : Nat} {boundary target : EdgeLabelling}
    (hphysical : id ∈
      slabPhysicalFaceEdges (centralExtent (volume + 1)))
    (hlower : plaquetteHalfSide (volume + 1)
      (slabPlaquetteAt (centralExtent (volume + 1)) id) = .lower) :
    lowSpinCentralCompletionRemainder volume boundary target id = 0 := by
  unfold lowSpinCentralCompletionRemainder
  rw [assembleReflectedSlabLabelling_lower hphysical hlower]
  rfl

private theorem slabPlaquetteAt_eq_of_enumerate_local
    {extent id : Nat} {plaquette : Z4Plaq}
    (hindexed : (id, plaquette) ∈
      enumerate (boundaryCompleteSlabPlaquettes extent)) :
    slabPlaquetteAt extent id = plaquette := by
  unfold slabPlaquetteAt
  exact enumerate_getD_of_mem fallbackPlaquette hindexed

/-- On every physical ambient face geometrically below the reflection plane,
the fixed/upper completion remainder is exactly zero. -/
theorem lowSpinCentralCompletionRemainderAmbient_zero_on_lower
    {volume targetId : Nat} {boundary target : EdgeLabelling}
    (htarget : targetId ∈ physicalFaceEdges (centralAmbient (volume + 1)))
    (hlower : plaquetteHalfSide (volume + 1)
      (boxPlaquetteAt (centralAmbient (volume + 1)) targetId) = .lower) :
    lowSpinCentralCompletionRemainderAmbient
        volume boundary target targetId = 0 := by
  have hslab := lowerAmbientFace_mem_centralSlab htarget hlower
  obtain ⟨sourceId, hsourceIndexed⟩ := exists_mem_enumerate hslab
  have hsourcePhysical : sourceId ∈
      slabPhysicalFaceEdges (centralExtent (volume + 1)) := by
    unfold slabPhysicalFaceEdges
    exact List.mem_range.mpr (enumerate_index_lt hsourceIndexed)
  have hsourceAt :
      slabPlaquetteAt (centralExtent (volume + 1)) sourceId =
        boxPlaquetteAt (centralAmbient (volume + 1)) targetId :=
    slabPlaquetteAt_eq_of_enumerate_local hsourceIndexed
  have htargetIndexed :
      (targetId, boxPlaquetteAt (centralAmbient (volume + 1)) targetId) ∈
        enumerate (boxPlaquettes (centralAmbient (volume + 1))) := by
    apply boxPlaquetteAt_mem_enumerate
    unfold physicalFaceEdges plaquetteEdgeCount at htarget
    exact List.mem_range.mp htarget
  unfold lowSpinCentralCompletionRemainderAmbient
  rw [slabToAmbientPhysical_eq_on_enumerate htargetIndexed,
    slabGeometricSpin_eq_of_enumerate hsourceIndexed]
  apply lowSpinCentralCompletionRemainder_zero_on_lower hsourcePhysical
  simpa only [hsourceAt] using hlower

/-! ## 3. Exact face and link separation -/

/-- A positive entry of an explicit finite edge list has a witnessing
coordinate. -/
private theorem hasExcitedB_exists_local (label : EdgeLabelling) :
    ∀ edges, hasExcitedB label edges = true →
      ∃ edge, edge ∈ edges ∧ 1 ≤ label edge
  | [], h => by cases h
  | edge :: rest, h => by
      by_cases hexcited : 1 ≤ label edge
      · exact ⟨edge, List.mem_cons_self, hexcited⟩
      · have hrest : hasExcitedB label rest = true := by
          simpa [hasExcitedB, hexcited] using h
        obtain ⟨found, hmem, hfound⟩ :=
          hasExcitedB_exists_local label rest hrest
        exact ⟨found, List.mem_cons_of_mem edge hmem, hfound⟩

private theorem lowSpinCentralSource_one_le_support
    {volume faceId : Nat} (index : LowSpinCentralIndex volume)
    (hpositive : 1 ≤
      timeSlicePhysical (2 * volume)
        (lowSpinCentralTimeSliceIndex index) faceId) :
    faceId ∈ timeSliceSupportIds (2 * volume)
      (lowSpinCentralTimeSliceIndex index) := by
  unfold timeSlicePhysical at hpositive
  by_cases hmem : faceId ∈ timeSliceSupportIds (2 * volume)
      (lowSpinCentralTimeSliceIndex index)
  · exact hmem
  · rw [componentLabel_eq_zero_of_not_mem hmem] at hpositive
    omega

/-- The selected source and the source-free fixed/upper completion occupy no
common physical ambient face. -/
theorem lowSpinCentralSource_completionRemainder_faceDisjoint
    {volume : Nat} (index : LowSpinCentralIndex volume)
    (boundary target : EdgeLabelling) :
    FaceDisjoint (centralAmbient (volume + 1))
      (timeSlicePhysical (2 * volume)
        (lowSpinCentralTimeSliceIndex index))
      (lowSpinCentralCompletionRemainderAmbient
        volume boundary target) := by
  intro faceId hphysical
  by_cases hzero :
      timeSlicePhysical (2 * volume)
        (lowSpinCentralTimeSliceIndex index) faceId = 0
  · exact Or.inl hzero
  · right
    have hpositive : 1 ≤
        timeSlicePhysical (2 * volume)
          (lowSpinCentralTimeSliceIndex index) faceId := by
      omega
    have hsupport :=
      lowSpinCentralSource_one_le_support index hpositive
    have hgeometric :
        boxPlaquetteAt (4 + 2 * volume) faceId ∈
          geometricPolymer (4 + 2 * volume)
            (timeSliceSupportIds (2 * volume)
              (lowSpinCentralTimeSliceIndex index)) :=
      List.mem_map.mpr ⟨faceId, hsupport, rfl⟩
    have hshifted :
        boxPlaquetteAt (4 + 2 * volume) faceId ∈
          shiftedOddFineCubeSurface index.val :=
      (timeSliceSupportIds_sameSupport
        (lowSpinCentralTimeSliceIndex index)).1 _ hgeometric
    apply lowSpinCentralCompletionRemainderAmbient_zero_on_lower
      hphysical
    simpa only [lowSpinCentralAmbient_eq volume] using
      (lowSpinCentralSourceFace_lower index hshifted)

/-- No physical lattice link is touched both by the selected source and by
the source-free fixed/upper completion. -/
theorem lowSpinCentralSource_completionRemainder_linkSeparated
    {volume : Nat} (index : LowSpinCentralIndex volume)
    (boundary target : EdgeLabelling) :
    LinkSeparated (centralAmbient (volume + 1))
      (timeSlicePhysical (2 * volume)
        (lowSpinCentralTimeSliceIndex index))
      (lowSpinCentralCompletionRemainderAmbient
        volume boundary target) := by
  intro indexed hindexed hboth
  unfold linkTouchesExcitationB at hboth
  obtain ⟨sourceId, hsourceIncident, hsourcePositive⟩ :=
    hasExcitedB_exists_local _ _ hboth.1
  obtain ⟨otherId, hotherIncident, hotherPositive⟩ :=
    hasExcitedB_exists_local _ _ hboth.2
  obtain ⟨sourceFace, hsourceIndexed, hsourceLink⟩ :=
    mem_incidentPlaqIds.mp hsourceIncident
  obtain ⟨otherFace, hotherIndexed, hotherLink⟩ :=
    mem_incidentPlaqIds.mp hotherIncident
  have hsourceSupport :=
    lowSpinCentralSource_one_le_support index hsourcePositive
  have hsourceIndexed' :
      (sourceId, sourceFace) ∈
        enumerate (boxPlaquettes (4 + 2 * volume)) := by
    simpa only [lowSpinCentralAmbient_eq volume] using hsourceIndexed
  have hsourceGeometric : sourceFace ∈
      geometricPolymer (4 + 2 * volume)
        (timeSliceSupportIds (2 * volume)
          (lowSpinCentralTimeSliceIndex index)) := by
    apply List.mem_map.mpr
    exact ⟨sourceId, hsourceSupport,
      boxPlaquetteAt_eq_of_enumerate hsourceIndexed'⟩
  have hsourceShifted : sourceFace ∈
      shiftedOddFineCubeSurface index.val :=
    (timeSliceSupportIds_sameSupport
      (lowSpinCentralTimeSliceIndex index)).1 _ hsourceGeometric
  have hotherLower : plaquetteHalfSide (volume + 1) otherFace = .lower :=
    lowSpinCentralSourceLink_incidentFace_lower index
      hsourceShifted hsourceLink hotherLink
  have hotherPhysical : otherId ∈
      physicalFaceEdges (centralAmbient (volume + 1)) := by
    unfold physicalFaceEdges plaquetteEdgeCount
    exact List.mem_range.mpr (enumerate_index_lt hotherIndexed)
  have hotherAt :
      boxPlaquetteAt (centralAmbient (volume + 1)) otherId = otherFace :=
    boxPlaquetteAt_eq_of_enumerate hotherIndexed
  have hzero := lowSpinCentralCompletionRemainderAmbient_zero_on_lower
    (boundary := boundary) (target := target)
    hotherPhysical (by simpa only [hotherAt] using hotherLower)
  rw [hzero] at hotherPositive
  omega

end YMGap.Continuum.BF4LowSpinGrowingVolumeSourceInterfaceSeparation

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeSourceInterfaceSeparation.lowSpinCentralSourceLink_incidentFace_lower
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeSourceInterfaceSeparation.lowSpinCentralCompletionRemainderAmbient_zero_on_lower
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeSourceInterfaceSeparation.lowSpinCentralSource_completionRemainder_faceDisjoint
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeSourceInterfaceSeparation.lowSpinCentralSource_completionRemainder_linkSeparated
