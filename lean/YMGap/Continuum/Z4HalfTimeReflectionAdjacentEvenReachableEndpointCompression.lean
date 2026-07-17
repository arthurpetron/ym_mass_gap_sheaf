/-
# Physically reachable endpoint compression at the first noncommuting cutoff

The full auxiliary channel window contains algebraic states that no lower
half-amplitude can reach.  In particular, the exact two-face fence lives at
shared channels `11,12` for `K=2`.  This file computes the literal radius-zero
lower incidence geometry and proves that every fixed link has zero or one
lower incident face.  The empty word selects endpoint channel zero; a
singleton word selects its one physical spin.  All reachable endpoints lie in
`0,...,K`; the fenced hard-boundary corner is absent from the physical image.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedInterfaceEndpointOperator

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReachableEndpointCompression

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FusionChannelConvolution
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedInterfaceEndpointOperator
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedLinkEndpointFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceSlabFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReflectedBoundaryAssembly
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenSlabIncidenceBridge
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4FusionPathZeroInsertion

/-! ## 1. Exact radius-zero lower-incidence geometry -/

def adjacentEvenRadiusZeroLowerAtMostOneCheck : Bool :=
  (adjacentEvenFixedLinks 0).all (fun link =>
    decide ((adjacentEvenIncidentFaceIdParts 0 link).1.length ≤ 1))

theorem adjacentEvenRadiusZeroLowerAtMostOneCheck_true :
    adjacentEvenRadiusZeroLowerAtMostOneCheck = true := by
  decide

theorem adjacentEvenRadiusZeroFixedLink_lowerIds_length_le_one
    {link : Z4Link} (hlink : link ∈ adjacentEvenFixedLinks 0) :
    (adjacentEvenIncidentFaceIdParts 0 link).1.length ≤ 1 := by
  have hcheck := List.all_eq_true.mp
    adjacentEvenRadiusZeroLowerAtMostOneCheck_true link hlink
  exact of_decide_eq_true hcheck

theorem adjacentEvenRadiusZeroLowerSpins_length_le_one
    (physical : Nat → Nat) {link : Z4Link}
    (hlink : link ∈ adjacentEvenFixedLinks 0) :
    (adjacentEvenIncidentLowerSpins 0 physical link).length ≤ 1 := by
  unfold adjacentEvenIncidentLowerSpins
  rw [List.length_map]
  exact adjacentEvenRadiusZeroFixedLink_lowerIds_length_le_one hlink

/-! ## 2. The common endpoint map and its exact support -/

def adjacentEvenRadiusZeroCommonLowerEndpoint
    (physical : Nat → Nat) (link : Z4Link) : Nat :=
  (adjacentEvenIncidentLowerSpins 0 physical link).getD 0 0

theorem adjacentEvenRadiusZeroCommonLowerEndpoint_le
    {K : Nat} {physical : Nat → Nat}
    (hphysical : SlabFaceLabellingBounded K
      (adjacentEvenExtent 0) physical)
    (link : Z4Link) :
    adjacentEvenRadiusZeroCommonLowerEndpoint physical link ≤ K := by
  have hbounded :=
    adjacentEvenPartitionedIncidentSpins_bounded hphysical link
  cases hlower : adjacentEvenIncidentLowerSpins 0 physical link with
  | nil =>
      simp [adjacentEvenRadiusZeroCommonLowerEndpoint, hlower]
  | cons head tail =>
      unfold adjacentEvenRadiusZeroCommonLowerEndpoint
      rw [hlower]
      simp only [List.getD_cons_zero]
      apply hbounded head
      unfold adjacentEvenPartitionedIncidentSpins
      apply List.mem_append_left
      apply List.mem_append_left
      rw [hlower]
      exact List.mem_cons_self

/-- At radius zero the lower half-amplitude is exactly the indicator of the
singleton incident lower spin when present, with the empty
boundary-completion case selecting channel zero. -/
theorem adjacentEvenRadiusZeroLowerChannelAmplitude_eq_indicator
    (cutoff : Nat) (physical : Nat → Nat)
    {link : Z4Link} (hlink : link ∈ adjacentEvenFixedLinks 0)
    (channel : Nat) :
    fusionChannelAmplitude cutoff
        (adjacentEvenIncidentLowerSpins 0 physical link) channel =
      boolMultiplicity (decide
        (channel = adjacentEvenRadiusZeroCommonLowerEndpoint physical link)) := by
  have hlength := adjacentEvenRadiusZeroLowerSpins_length_le_one
    physical hlink
  cases hlower : adjacentEvenIncidentLowerSpins 0 physical link with
  | nil =>
      unfold fusionChannelAmplitude
        adjacentEvenRadiusZeroCommonLowerEndpoint
      simp [hlower, fusionPathMultiplicity_singleton,
        boolMultiplicity]
  | cons head tail =>
      cases tail with
      | nil =>
          have hendpoint :
              adjacentEvenRadiusZeroCommonLowerEndpoint physical link =
                head := by
            unfold adjacentEvenRadiusZeroCommonLowerEndpoint
            rw [hlower]
            rfl
          rw [hendpoint]
          unfold fusionChannelAmplitude
          change fusionPathMultiplicity cutoff [head, channel] =
            boolMultiplicity (decide (channel = head))
          rw [fusionPathMultiplicity_two,
            fusionOK_zero_output_eq_decide]
          simp [eq_comm]
      | cons second rest =>
          simp [hlower] at hlength

private theorem zeroEdgeLabelling_mem_bounded_local (K : Nat) :
    ∀ ids : List Nat,
      zeroEdgeLabelling ∈ boundedEdgeLabellings K ids := by
  intro ids
  apply boundedEdgeLabellings_complete
  · intro _ _
    change 0 < K + 1
    omega
  · intro _ _
    rfl

def adjacentEvenRadiusZeroCommonEndpointFromHalfState
    (state : EdgeLabelling) : Z4Link → Nat :=
  adjacentEvenRadiusZeroCommonLowerEndpoint
    (assembleAdjacentEvenReflectedSlabLabelling 0 state
      zeroEdgeLabelling zeroEdgeLabelling)

def adjacentEvenRadiusZeroReachableEndpointAssignments
    (K : Nat) : List (Z4Link → Nat) :=
  (boundedEdgeLabellings K (adjacentEvenLowerFaceIds 0)).map
    adjacentEvenRadiusZeroCommonEndpointFromHalfState

theorem adjacentEvenRadiusZeroReachableEndpoint_le
    {K : Nat} {endpoint : Z4Link → Nat}
    (hendpoint : endpoint ∈
      adjacentEvenRadiusZeroReachableEndpointAssignments K)
    (link : Z4Link) :
    endpoint link ≤ K := by
  obtain ⟨state, hstate, rfl⟩ := List.mem_map.mp hendpoint
  exact adjacentEvenRadiusZeroCommonLowerEndpoint_le
    (assembleAdjacentEvenReflectedSlabLabelling_bounded
      hstate
      (zeroEdgeLabelling_mem_bounded_local K
        (adjacentEvenFixedFaceIds 0))
      (zeroEdgeLabelling_mem_bounded_local K
        (adjacentEvenLowerFaceIds 0))) link

/-- The shared link used by the cutoff-two patch is itself one of the literal
radius-zero fixed links. -/
theorem adjacentEvenRadiusZeroPatchSharedLink_fixed :
    adjacentEvenRadiusZeroPatchSharedLink ∈
      adjacentEvenFixedLinks 0 := by
  decide

/-- Neither channel `11` nor channel `12` can occur at the fenced shared link
in the physical `K=2` endpoint image. -/
theorem adjacentEvenRadiusZeroPatch_bad_channels_unreachable
    {endpoint : Z4Link → Nat}
    (hendpoint : endpoint ∈
      adjacentEvenRadiusZeroReachableEndpointAssignments 2) :
    endpoint adjacentEvenRadiusZeroPatchSharedLink ≠ 11 ∧
      endpoint adjacentEvenRadiusZeroPatchSharedLink ≠ 12 := by
  have hbound := adjacentEvenRadiusZeroReachableEndpoint_le
    hendpoint adjacentEvenRadiusZeroPatchSharedLink
  constructor
  · intro heq
    have himpossible : 11 ≤ 2 := heq ▸ hbound
    exact (by decide : ¬ (11 ≤ 2)) himpossible
  · intro heq
    have himpossible : 12 ≤ 2 := heq ▸ hbound
    exact (by decide : ¬ (12 ≤ 2)) himpossible

/-! ## 3. The physically compressed fixed-interface matrix -/

def adjacentEvenRadiusZeroReachableEndpointAt
    (K index : Nat) : Z4Link → Nat :=
  (adjacentEvenRadiusZeroReachableEndpointAssignments K).getD index
    (zeroLabellingOn : Z4Link → Nat)

def adjacentEvenRadiusZeroCompressedFixedInterfaceMatrix
    (K left right : Nat) : Q' :=
  adjacentEvenFixedInterfaceEndpointKernel K 0
    (adjacentEvenRadiusZeroReachableEndpointAt K left)
    (adjacentEvenRadiusZeroReachableEndpointAt K right)

#print axioms adjacentEvenRadiusZeroLowerAtMostOneCheck_true
#print axioms adjacentEvenRadiusZeroFixedLink_lowerIds_length_le_one
#print axioms adjacentEvenRadiusZeroLowerSpins_length_le_one
#print axioms adjacentEvenRadiusZeroCommonLowerEndpoint_le
#print axioms adjacentEvenRadiusZeroLowerChannelAmplitude_eq_indicator
#print axioms adjacentEvenRadiusZeroReachableEndpoint_le
#print axioms adjacentEvenRadiusZeroPatchSharedLink_fixed
#print axioms adjacentEvenRadiusZeroPatch_bad_channels_unreachable

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReachableEndpointCompression
