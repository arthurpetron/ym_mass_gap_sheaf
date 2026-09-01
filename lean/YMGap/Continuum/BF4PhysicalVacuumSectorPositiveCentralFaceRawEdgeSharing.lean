/-
# Raw edge-sharing compiler for the positive central-face BF4 routing

Loop erasure only removes directed edges from each state-to-vacuum path.
Consequently every state using an edge after normalization already used that
edge in the explicit raw central-face prefix-plus-terminal route.  This module
proves the pointwise user-set inclusion and its cardinality consequence.

The remaining cofinal producer can therefore state both of its hypotheses on
the same raw routing: a uniform raw edge-user count and a uniform explicit
prefix-terminal state load.  These hypotheses are not inhabited here, so no
unconditional congestion bound, finite gap, scaling limit, continuum theory,
or Clay conclusion is asserted.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceRawStateLoad

namespace YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceRawEdgeSharing

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceEdgeTail
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceFlow
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceSimpleRouting
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceRawStateLoad
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalPrefixAssignment
open YMGap.Continuum.BF4PhysicalVacuumSectorSpinCubeTerminalPrefixCompiler
open YMGap.Continuum.FiniteBoolGraphSimplePaths
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

/-! ## 1. Loop-erased edge users are raw edge users -/

theorem loopErased_routedRootEdgeUsingStates_subset_raw
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source target state : Nat)
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorRoutedRootEdgeUsingStates
        (loopErasedCentralPhysicalFiniteVacuumSectorPositiveRoutingAt routing)
        source target) :
    state ∈ centralPhysicalFiniteVacuumSectorRoutedRootEdgeUsingStates
      routing source target := by
  obtain ⟨hsector, hedge⟩ :=
    mem_centralPhysicalFiniteVacuumSectorRoutedRootEdgeUsingStates_iff.mp
      hstate
  apply
    mem_centralPhysicalFiniteVacuumSectorRoutedRootEdgeUsingStates_iff.mpr
  refine ⟨hsector, ?_⟩
  exact
    (centralPhysicalFiniteVacuumSectorLoopErasedPositivePath_directedEdges_sublist
      hsector
      (routing.path state 0 hsector
        (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K 0))).mem
      hedge

theorem loopErased_routedRootEdgeUsingStates_length_le_raw
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source target : Nat) :
    (centralPhysicalFiniteVacuumSectorRoutedRootEdgeUsingStates
        (loopErasedCentralPhysicalFiniteVacuumSectorPositiveRoutingAt routing)
        source target).length ≤
      (centralPhysicalFiniteVacuumSectorRoutedRootEdgeUsingStates
        routing source target).length := by
  apply FiniteListBound.nodup_subset_length_le
  · unfold centralPhysicalFiniteVacuumSectorRoutedRootEdgeUsingStates
    exact List.filter_sublist.nodup
      (centralPhysicalFiniteVacuumSectorIndices_nodup w hw K 0)
  · intro state hstate
    exact loopErased_routedRootEdgeUsingStates_subset_raw
      routing source target state hstate

/-! ## 2. A producer stated entirely on the explicit raw routing -/

structure FixedNomeCofinalPositiveCentralFaceRawBoundedSharingPrefixTerminalLoad
    {w : Q'} (hw : (0 : Q') < w) : Type where
  start : Nat
  start_positive : 1 ≤ start
  sharingBound : Q'
  stateLoadBound : Q'
  sharingBound_nonnegative : (0 : Q') ≤ sharingBound
  stateLoadBound_nonnegative : (0 : Q') ≤ stateLoadBound
  rawEdgeUsers_cardinality_le : ∀ K, (hK : start ≤ K) →
    ∀ source target,
      Q'.ofNat
          (centralPhysicalFiniteVacuumSectorRoutedRootEdgeUsingStates
            (positiveCentralFaceSpinTerminalPrefixAssignment
              hw K (Nat.le_trans start_positive hK)).toPositiveRouting
            source target).length ≤
        sharingBound
  prefixTerminalStateLoad_le : ∀ K, (hK : start ≤ K) →
    ∀ state,
      (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0) →
        positiveCentralFacePrefixTerminalStateLoad hw
            (Nat.le_trans start_positive hK) hstate ≤
          stateLoadBound

namespace FixedNomeCofinalPositiveCentralFaceRawBoundedSharingPrefixTerminalLoad

def toBoundedSharingPrefixTerminalLoad
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalPositiveCentralFaceRawBoundedSharingPrefixTerminalLoad
        hw) :
    FixedNomeCofinalPositiveCentralFaceBoundedSharingPrefixTerminalLoad hw where
  start := family.start
  start_positive := family.start_positive
  sharingBound := family.sharingBound
  stateLoadBound := family.stateLoadBound
  sharingBound_nonnegative := family.sharingBound_nonnegative
  stateLoadBound_nonnegative := family.stateLoadBound_nonnegative
  edgeUsers_cardinality_le := by
    intro K hK source target
    let raw :=
      (positiveCentralFaceSpinTerminalPrefixAssignment
        hw K (Nat.le_trans family.start_positive hK)).toPositiveRouting
    have hlength := loopErased_routedRootEdgeUsingStates_length_le_raw
      raw source target
    exact Q'.le_trans' _ _ _
      (Q'.ofNat_le_ofNat hlength)
      (family.rawEdgeUsers_cardinality_le K hK source target)
  prefixTerminalStateLoad_le := family.prefixTerminalStateLoad_le

def toSimpleRootResistanceCongestionBound
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalPositiveCentralFaceRawBoundedSharingPrefixTerminalLoad
        hw) :
    FixedNomeCofinalVacuumSectorMassExactSimpleRootResistanceCongestionBound
      hw :=
  family.toBoundedSharingPrefixTerminalLoad
    |>.toSimpleRootResistanceCongestionBound

theorem flowLoad_le_product
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalPositiveCentralFaceRawBoundedSharingPrefixTerminalLoad
        hw)
    (K : Nat) (hK : family.start ≤ K) (source target : Nat) :
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad
        (simplePositiveCentralFaceRouting hw K
          (Nat.le_trans family.start_positive hK))
        source target ≤
      family.sharingBound * family.stateLoadBound :=
  family.toBoundedSharingPrefixTerminalLoad.flowLoad_le_product
    K hK source target

end FixedNomeCofinalPositiveCentralFaceRawBoundedSharingPrefixTerminalLoad

end YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceRawEdgeSharing

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceRawEdgeSharing.loopErased_routedRootEdgeUsingStates_subset_raw
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceRawEdgeSharing.loopErased_routedRootEdgeUsingStates_length_le_raw
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceRawEdgeSharing.FixedNomeCofinalPositiveCentralFaceRawBoundedSharingPrefixTerminalLoad.toBoundedSharingPrefixTerminalLoad
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceRawEdgeSharing.FixedNomeCofinalPositiveCentralFaceRawBoundedSharingPrefixTerminalLoad.flowLoad_le_product
