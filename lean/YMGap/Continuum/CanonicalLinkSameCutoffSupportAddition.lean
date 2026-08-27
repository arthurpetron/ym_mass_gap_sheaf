/-
# Same-cutoff addition of accepted canonical SU(2) link witnesses

Pointwise addition preserves the canonical SU(2) fusion guard.  The generic
Cartesian theorem therefore places a sum of two auxiliary witnesses in a
doubled cutoff window.  For a facewise two-replica switch this is wasteful:
the recombined external field chooses one source spin at each face and hence
remains bounded by the original physical cutoff.

This module combines additive admissibility with the sharp canonical-channel
support theorem.  On used coordinates the accepted sum is at most `6*K`; off
the used list it is zero because both enumerated summands are zero.  The sum
therefore occurs in the original production enumeration.  A corrected-slab
specialization states the result directly for one physical link.

Constructive contract: exact finite support, Boolean guards, and natural
arithmetic only.  No `Classical.*`, choice, `native_decide`, `sorry`, custom
axiom, `noncomputable`, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CanonicalLinkAuxiliarySupportBound

namespace YMGap.Continuum.CanonicalLinkSameCutoffSupportAddition

set_option autoImplicit false

open YMGap.Continuum.CanonicalLinkAuxiliarySupportBound
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FusionSupportAddition
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

/-- Two enumerated accepted canonical witnesses whose summed external field
is still `K`-bounded add to an auxiliary witness in the same `6*K` Cartesian
window. -/
theorem canonicalLinkAcceptedAuxiliary_add_mem_sameCutoff
    {K degree : Nat}
    {leftExternal rightExternal leftAuxiliary rightAuxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hexternal : ∀ position : Fin degree,
      addEdgeLabelling leftExternal rightExternal position.val ≤ K)
    (hleftBounded : leftAuxiliary ∈
      boundedEdgeLabellings (linkAuxiliaryCutoff K)
        (canonicalUsedAuxiliaryCoordinates degree))
    (hrightBounded : rightAuxiliary ∈
      boundedEdgeLabellings (linkAuxiliaryCutoff K)
        (canonicalUsedAuxiliaryCoordinates degree))
    (hleftAllowed : canonicalLinkConditionalAllowedB
      degree leftExternal leftAuxiliary = true)
    (hrightAllowed : canonicalLinkConditionalAllowedB
      degree rightExternal rightAuxiliary = true) :
    addEdgeLabelling leftAuxiliary rightAuxiliary ∈
      (boundedEdgeLabellings (linkAuxiliaryCutoff K)
        (canonicalUsedAuxiliaryCoordinates degree)).filter
          (canonicalLinkConditionalAllowedB degree
            (addEdgeLabelling leftExternal rightExternal)) := by
  have hallowed := canonicalLinkConditionalAllowedB_add degree
    leftExternal rightExternal leftAuxiliary rightAuxiliary
    hleftAllowed hrightAllowed
  apply List.mem_filter.mpr
  constructor
  · have hleftSound := boundedEdgeLabellings_sound
      (linkAuxiliaryCutoff K)
      (canonicalUsedAuxiliaryCoordinates degree)
      leftAuxiliary hleftBounded
    have hrightSound := boundedEdgeLabellings_sound
      (linkAuxiliaryCutoff K)
      (canonicalUsedAuxiliaryCoordinates degree)
      rightAuxiliary hrightBounded
    apply boundedEdgeLabellings_complete
    · intro edge hedge
      exact Nat.lt_succ_iff.mpr
        (canonicalLinkConditionalAllowedB_auxiliary_le_linkAuxiliaryCutoff
          hdegree hexternal hallowed hedge)
    · intro edge hedge
      unfold addEdgeLabelling
      rw [hleftSound.2 edge hedge, hrightSound.2 edge hedge]
  · exact hallowed

/-- Corrected-slab specialization: if the physical sum remains bounded by
`K` facewise, two accepted local link witnesses add to an accepted witness
over that sum at the original cutoff. -/
theorem slabLinkFusionWitness_add_mem_sameCutoff
    {K extent : Nat}
    {leftPhysical rightPhysical leftAuxiliary rightAuxiliary : EdgeLabelling}
    (link : SlabLink)
    (hphysical : SlabFaceLabellingBounded K extent
      (addEdgeLabelling leftPhysical rightPhysical))
    (hleft : leftAuxiliary ∈
      slabLinkFusionWitnesses K extent leftPhysical link)
    (hright : rightAuxiliary ∈
      slabLinkFusionWitnesses K extent rightPhysical link) :
    addEdgeLabelling leftAuxiliary rightAuxiliary ∈
      slabLinkFusionWitnesses K extent
        (addEdgeLabelling leftPhysical rightPhysical) link := by
  let degree := (slabIncidentPlaqIds extent link).length
  let leftExternal := slabLinkExternalSpins extent leftPhysical link
  let rightExternal := slabLinkExternalSpins extent rightPhysical link
  have hdegree : degree ≤ linkIncidenceBound := by
    dsimp [degree]
    exact slabIncidentPlaqIds_length_le_six extent link
  have hexternal : ∀ position : Fin degree,
      addEdgeLabelling leftExternal rightExternal position.val ≤ K := by
    intro position
    let actualPosition : Fin (slabIncidentPlaqIds extent link).length :=
      ⟨position.val, position.isLt⟩
    have hleftValue := externalSpinsOfList_map_get
      (slabIncidentPlaqIds extent link) leftPhysical actualPosition
    have hrightValue := externalSpinsOfList_map_get
      (slabIncidentPlaqIds extent link) rightPhysical actualPosition
    dsimp [leftExternal, rightExternal, slabLinkExternalSpins,
      addEdgeLabelling]
    rw [show position.val = actualPosition.val from rfl,
      hleftValue, hrightValue]
    exact hphysical _
      (slabIncidentPlaqId_physical
        (List.get_mem (slabIncidentPlaqIds extent link) actualPosition))
  have hleftParts := List.mem_filter.mp hleft
  have hrightParts := List.mem_filter.mp hright
  have hsum := canonicalLinkAcceptedAuxiliary_add_mem_sameCutoff
    hdegree hexternal hleftParts.1 hrightParts.1
      (slabLinkFusionWitness_mem_allowed
        K extent leftPhysical link leftAuxiliary hleft)
      (slabLinkFusionWitness_mem_allowed
        K extent rightPhysical link rightAuxiliary hright)
  unfold slabLinkFusionWitnesses
  change addEdgeLabelling leftAuxiliary rightAuxiliary ∈
    (boundedEdgeLabellings (linkAuxiliaryCutoff K)
      (canonicalUsedAuxiliaryCoordinates degree)).filter
        (canonicalLinkConditionalAllowedB degree
          (slabLinkExternalSpins extent
            (addEdgeLabelling leftPhysical rightPhysical) link))
  have hexternalAdd :
      slabLinkExternalSpins extent
          (addEdgeLabelling leftPhysical rightPhysical) link =
        addEdgeLabelling leftExternal rightExternal := by
    dsimp [slabLinkExternalSpins, leftExternal, rightExternal]
    exact externalSpinsOfList_map_add
      (slabIncidentPlaqIds extent link) leftPhysical rightPhysical
  rw [hexternalAdd]
  exact hsum

#print axioms canonicalLinkAcceptedAuxiliary_add_mem_sameCutoff
#print axioms slabLinkFusionWitness_add_mem_sameCutoff

end YMGap.Continuum.CanonicalLinkSameCutoffSupportAddition
