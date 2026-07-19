/-
# Reachable fixed-word symmetry for the adjacent-even interface

The unrestricted auxiliary endpoint window contains a known nonsymmetric
two-face corner.  The physical lower amplitudes never reach that corner.  This
leaf proves the exact replacement: on the deterministic endpoints selected by
the two reflected lower halves, every fixed-link fusion word is reversible
inside the unchanged production cutoff.

It also names the zero-padded fixed-interface pullback on enumerated physical
half states.  No Gram witness is asserted for that pullback.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenDeterministicLowerEndpoint
import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenPhysicalReflectionQuadratic

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReachableFixedWordSymmetry

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SchurHadamardTransfer
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionChannelConvolution
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenDeterministicLowerEndpoint
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceBijection
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedInterfaceEndpointOperator
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceSlabFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenPhysicalKernelSymmetry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenPhysicalReflectionQuadratic
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReachableSupportGeneric
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReflectedBoundaryAssembly
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenSlabIncidenceBridge
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## 1. Assembly locality of the lower and fixed words -/

theorem adjacentEvenAssembledFixedSpins_swap
    (radius : Nat) (left boundary right : EdgeLabelling)
    (link : Z4Link) :
    adjacentEvenIncidentFixedSpins radius
        (assembleAdjacentEvenReflectedSlabLabelling
          radius left boundary right) link =
      adjacentEvenIncidentFixedSpins radius
        (assembleAdjacentEvenReflectedSlabLabelling
          radius right boundary left) link := by
  unfold adjacentEvenIncidentFixedSpins
  apply List.map_congr_left
  intro id hid
  have hparts :=
    mem_adjacentEvenIncidentFixedFaceIds.mp hid
  have hphysical :
      id ∈ slabPhysicalFaceEdges (adjacentEvenExtent radius) :=
    slabIncidentPlaqId_physical hparts.1
  rw [assembleAdjacentEvenReflectedSlabLabelling_fixed
        hphysical hparts.2,
      assembleAdjacentEvenReflectedSlabLabelling_fixed
        hphysical hparts.2]

theorem adjacentEvenAssembledLowerSpins_eq_left
    (radius : Nat) (left boundary right : EdgeLabelling)
    (link : Z4Link) :
    adjacentEvenIncidentLowerSpins radius
        (assembleAdjacentEvenReflectedSlabLabelling
          radius left boundary right) link =
      adjacentEvenIncidentLowerSpins radius left link := by
  unfold adjacentEvenIncidentLowerSpins
  apply List.map_congr_left
  intro id hid
  have hparts :=
    (YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization.mem_partitionBySide_lower
      (fun faceId => adjacentEvenPlaquetteSide radius
        (slabPlaquetteAt (adjacentEvenExtent radius) faceId))
      id (slabIncidentPlaqIds (adjacentEvenExtent radius) link)).mp hid
  rw [assembleAdjacentEvenReflectedSlabLabelling_lower
    (slabIncidentPlaqId_physical hparts.1) hparts.2]

theorem adjacentEvenAssembledCommonLowerEndpoint_eq_left
    (radius : Nat) (left boundary right : EdgeLabelling)
    (link : Z4Link) :
    adjacentEvenCommonLowerEndpoint radius
        (assembleAdjacentEvenReflectedSlabLabelling
          radius left boundary right) link =
      adjacentEvenCommonLowerEndpoint radius left link := by
  unfold adjacentEvenCommonLowerEndpoint
  rw [adjacentEvenAssembledLowerSpins_eq_left]

/-! ## 2. General coupled-support reversal -/

private theorem adjacentEvenIncidentLowerSpins_bounded_aux
    {K radius : Nat} {physical : EdgeLabelling}
    (hphysical : SlabFaceLabellingBounded K
      (adjacentEvenExtent radius) physical)
    (link : Z4Link) :
    SpinsBounded (linkAuxiliaryCutoff K)
      (adjacentEvenIncidentLowerSpins radius physical link) := by
  have hfull :=
    adjacentEvenPartitionedIncidentSpins_bounded hphysical link
  intro spin hspin
  exact Nat.le_trans
    (hfull spin (by
      unfold adjacentEvenPartitionedIncidentSpins
      exact List.mem_append_left _
        (List.mem_append_left _ hspin)))
    (externalCutoff_le_linkAuxiliaryCutoff K)

private theorem adjacentEvenIncidentFixedSpins_bounded_aux
    {K radius : Nat} {physical : EdgeLabelling}
    (hphysical : SlabFaceLabellingBounded K
      (adjacentEvenExtent radius) physical)
    (link : Z4Link) :
    SpinsBounded (linkAuxiliaryCutoff K)
      (adjacentEvenIncidentFixedSpins radius physical link) := by
  have hfull :=
    adjacentEvenPartitionedIncidentSpins_bounded hphysical link
  intro spin hspin
  exact Nat.le_trans
    (hfull spin (by
      unfold adjacentEvenPartitionedIncidentSpins
      exact List.mem_append_left _
        (List.mem_append_right _ hspin)))
    (externalCutoff_le_linkAuxiliaryCutoff K)

/-- If `source` and `target` are genuinely reached by lower half-words whose
fixed words agree, the complete fixed-word transition is symmetric.  The
coupled lower-plus-fixed budget is retained separately on the two sides; the
coarser independent endpoint box is not used. -/
theorem adjacentEvenReachableFixedWordTransition_symmetric
    {K radius : Nat}
    {physical reflected : EdgeLabelling}
    (hphysical : SlabFaceLabellingBounded K
      (adjacentEvenExtent radius) physical)
    (hreflected : SlabFaceLabellingBounded K
      (adjacentEvenExtent radius) reflected)
    (link : Z4Link)
    (hfixed : adjacentEvenIncidentFixedSpins radius physical link =
      adjacentEvenIncidentFixedSpins radius reflected link)
    (source target : Nat)
    (hsource : source ≤ linkAuxiliaryCutoff K)
    (htarget : target ≤ linkAuxiliaryCutoff K)
    (hsourceReach :
      fusionChannelAmplitude (linkAuxiliaryCutoff K)
        (adjacentEvenIncidentLowerSpins radius physical link)
        source ≠ 0)
    (htargetReach :
      fusionChannelAmplitude (linkAuxiliaryCutoff K)
        (adjacentEvenIncidentLowerSpins radius reflected link)
        target ≠ 0) :
    fusionWalkMultiplicity (linkAuxiliaryCutoff K) source target
        (adjacentEvenIncidentFixedSpins radius physical link) =
      fusionWalkMultiplicity (linkAuxiliaryCutoff K) target source
        (adjacentEvenIncidentFixedSpins radius physical link) := by
  have hsourceSupport :
      source ≤ natListSum
        (adjacentEvenIncidentLowerSpins radius physical link) :=
    fusionChannelAmplitude_nonzero_implies_le_sum
      hsource
      (adjacentEvenIncidentLowerSpins_bounded_aux hphysical link)
      hsourceReach
  have htargetSupport :
      target ≤ natListSum
        (adjacentEvenIncidentLowerSpins radius reflected link) :=
    fusionChannelAmplitude_nonzero_implies_le_sum
      htarget
      (adjacentEvenIncidentLowerSpins_bounded_aux hreflected link)
      htargetReach
  have hsourceCoupled :=
    adjacentEvenFixedLink_lower_add_fixed_sum_le_auxiliary
      hphysical link
  have htargetCoupled :=
    adjacentEvenFixedLink_lower_add_fixed_sum_le_auxiliary
      hreflected link
  have hsourceBudget :
      source + natListSum
          (adjacentEvenIncidentFixedSpins radius physical link) ≤
        linkAuxiliaryCutoff K := by
    omega
  have htargetBudget :
      target + natListSum
          (adjacentEvenIncidentFixedSpins radius physical link) ≤
        linkAuxiliaryCutoff K := by
    rw [hfixed]
    omega
  exact fusionWalkMultiplicity_symmetric_of_endpoint_budgets
    (adjacentEvenIncidentFixedSpins radius physical link)
    hsource htarget
    (adjacentEvenIncidentFixedSpins_bounded_aux hphysical link)
    hsourceBudget htargetBudget

/-! ## 3. Deterministic reflected-slab specialization -/

theorem adjacentEvenAssembledEndpointFixedWordTransition_symmetric
    {K radius : Nat} {left boundary right : EdgeLabelling}
    (hleft : left ∈ adjacentEvenHalfStates K radius)
    (hboundary : boundary ∈ adjacentEvenBoundaryChannels K radius)
    (hright : right ∈ adjacentEvenHalfStates K radius)
    (link : Z4Link) (hlink : link ∈ adjacentEvenFixedLinks radius) :
    let physical := assembleAdjacentEvenReflectedSlabLabelling
      radius left boundary right
    let reflected := assembleAdjacentEvenReflectedSlabLabelling
      radius right boundary left
    fusionWalkMultiplicity (linkAuxiliaryCutoff K)
        (adjacentEvenCommonLowerEndpoint radius physical link)
        (adjacentEvenCommonLowerEndpoint radius reflected link)
        (adjacentEvenIncidentFixedSpins radius physical link) =
      fusionWalkMultiplicity (linkAuxiliaryCutoff K)
        (adjacentEvenCommonLowerEndpoint radius reflected link)
        (adjacentEvenCommonLowerEndpoint radius physical link)
        (adjacentEvenIncidentFixedSpins radius physical link) := by
  dsimp only
  let physical := assembleAdjacentEvenReflectedSlabLabelling
    radius left boundary right
  let reflected := assembleAdjacentEvenReflectedSlabLabelling
    radius right boundary left
  have hphysical : SlabFaceLabellingBounded K
      (adjacentEvenExtent radius) physical :=
    assembleAdjacentEvenReflectedSlabLabelling_bounded
      hleft hboundary hright
  have hreflected : SlabFaceLabellingBounded K
      (adjacentEvenExtent radius) reflected :=
    assembleAdjacentEvenReflectedSlabLabelling_bounded
      hright hboundary hleft
  have hsource : adjacentEvenCommonLowerEndpoint radius physical link ≤
      linkAuxiliaryCutoff K :=
    Nat.le_trans (adjacentEvenCommonLowerEndpoint_le hphysical link)
      (externalCutoff_le_linkAuxiliaryCutoff K)
  have htarget : adjacentEvenCommonLowerEndpoint radius reflected link ≤
      linkAuxiliaryCutoff K :=
    Nat.le_trans (adjacentEvenCommonLowerEndpoint_le hreflected link)
      (externalCutoff_le_linkAuxiliaryCutoff K)
  have hsourceReach :
      fusionChannelAmplitude (linkAuxiliaryCutoff K)
        (adjacentEvenIncidentLowerSpins radius physical link)
        (adjacentEvenCommonLowerEndpoint radius physical link) ≠ 0 := by
    rw [adjacentEvenLowerChannelAmplitude_eq_indicator
      (linkAuxiliaryCutoff K) radius physical hlink]
    simp [boolMultiplicity]
  have htargetReach :
      fusionChannelAmplitude (linkAuxiliaryCutoff K)
        (adjacentEvenIncidentLowerSpins radius reflected link)
        (adjacentEvenCommonLowerEndpoint radius reflected link) ≠ 0 := by
    rw [adjacentEvenLowerChannelAmplitude_eq_indicator
      (linkAuxiliaryCutoff K) radius reflected hlink]
    simp [boolMultiplicity]
  exact adjacentEvenReachableFixedWordTransition_symmetric
    hphysical hreflected link
    (adjacentEvenAssembledFixedSpins_swap
      radius left boundary right link)
    _ _ hsource htarget hsourceReach htargetReach

/-! ## 4. The exact reachable fixed-interface target -/

def adjacentEvenHalfStateEndpointAssignment
    (radius : Nat) (state : EdgeLabelling) : Z4Link → Nat :=
  fun link => adjacentEvenCommonLowerEndpoint radius state link

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

theorem adjacentEvenHalfStateEndpointAssignment_le
    {K radius : Nat} {state : EdgeLabelling}
    (hstate : state ∈ adjacentEvenHalfStates K radius)
    (link : Z4Link) :
    adjacentEvenHalfStateEndpointAssignment radius state link ≤ K := by
  let physical := assembleAdjacentEvenReflectedSlabLabelling
    radius state zeroEdgeLabelling zeroEdgeLabelling
  have hphysical : SlabFaceLabellingBounded K
      (adjacentEvenExtent radius) physical :=
    assembleAdjacentEvenReflectedSlabLabelling_bounded
      hstate
      (zeroEdgeLabelling_mem_bounded_local K
        (adjacentEvenFixedFaceIds radius))
      (zeroEdgeLabelling_mem_bounded_local K
        (adjacentEvenLowerFaceIds radius))
  have hbound := adjacentEvenCommonLowerEndpoint_le hphysical link
  unfold adjacentEvenHalfStateEndpointAssignment
  rw [adjacentEvenAssembledCommonLowerEndpoint_eq_left] at hbound
  exact hbound

/-- The physical fixed-interface operator pulled back to deterministic
endpoints of enumerated half states, padded by zero off the finite carrier. -/
def adjacentEvenReachableFixedInterfaceMatrix
    (K radius left right : Nat) : Q' :=
  if left < adjacentEvenPhysicalHalfStateCount K radius then
    if right < adjacentEvenPhysicalHalfStateCount K radius then
      adjacentEvenFixedInterfaceEndpointKernel K radius
        (adjacentEvenHalfStateEndpointAssignment radius
          (adjacentEvenPhysicalHalfStateAt K radius left))
        (adjacentEvenHalfStateEndpointAssignment radius
          (adjacentEvenPhysicalHalfStateAt K radius right))
    else 0
  else 0

theorem adjacentEvenReachableFixedInterfaceMatrix_eq_kernel
    {K radius left right : Nat}
    (hleft : left < adjacentEvenPhysicalHalfStateCount K radius)
    (hright : right < adjacentEvenPhysicalHalfStateCount K radius) :
    adjacentEvenReachableFixedInterfaceMatrix K radius left right =
      adjacentEvenFixedInterfaceEndpointKernel K radius
        (adjacentEvenHalfStateEndpointAssignment radius
          (adjacentEvenPhysicalHalfStateAt K radius left))
        (adjacentEvenHalfStateEndpointAssignment radius
          (adjacentEvenPhysicalHalfStateAt K radius right)) := by
  simp [adjacentEvenReachableFixedInterfaceMatrix, hleft, hright]

/-- A constructive Gram of the deterministic reachable pullback is the exact
remaining common-middle witness.  This type is named but not inhabited here. -/
def AdjacentEvenReachableFixedInterfaceGramWitness
    (K radius : Nat) : Type :=
  GramRep (adjacentEvenReachableFixedInterfaceMatrix K radius)

#print axioms adjacentEvenAssembledFixedSpins_swap
#print axioms adjacentEvenAssembledLowerSpins_eq_left
#print axioms adjacentEvenAssembledCommonLowerEndpoint_eq_left
#print axioms adjacentEvenReachableFixedWordTransition_symmetric
#print axioms adjacentEvenAssembledEndpointFixedWordTransition_symmetric
#print axioms adjacentEvenHalfStateEndpointAssignment_le
#print axioms adjacentEvenReachableFixedInterfaceMatrix_eq_kernel

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReachableFixedWordSymmetry
