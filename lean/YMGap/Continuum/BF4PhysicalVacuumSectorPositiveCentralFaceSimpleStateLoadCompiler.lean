/-
# Simple-path state-load compiler for the central-face BF4 routing

The bounded-sharing target initially asks for a uniform bound on each user's
multiplicity-aware load at each directed edge.  For the normalized central-
face routing this is stronger notation than necessary: every route is vertex-
simple, hence its directed-edge list is duplicate-free and every edge
multiplicity is at most one.

This module proves that the exact per-edge state load is bounded by the whole
route state load.  It then replaces the per-edge producer field by one uniform
bound on

  2 * stationaryWeight(state) * pathResistance(state, vacuum).

Together with a uniform edge-user bound, this compiles into the exact cofinal
load target.  Neither remaining uniform estimate is constructed here, so no
unconditional cofinal finite gap, physical scaling, continuum, or Clay result
is asserted.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceCofinalLoadTarget

namespace YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceSimpleStateLoadCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorResistanceCauchy
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceEdgeTail
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceFlow
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceSimpleRouting
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceCofinalLoadTarget
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalPrefixAssignment
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

/-! ## 1. Simplicity removes directed-edge multiplicity -/

theorem simplePositiveCentralFaceRouting_stateLoad_nonnegative
    {w : Q'} (hw : (0 : Q') < w) {K state : Nat} (hK : 1 ≤ K)
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0) :
    (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateLoad
        (simplePositiveCentralFaceRouting hw K hK) state := by
  unfold centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateLoad
  rw [dif_pos hstate]
  let path := (simplePositiveCentralFaceRouting hw K hK).path state 0
    hstate
    (zero_mem_centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
  let singleLoad := centralPhysicalFiniteWeight
    w (Q'.le_of_lt hw) K 0 state *
      PositiveKernelChainIn.resistance path
  have hsingle : (0 : Q') ≤ singleLoad :=
    Q'.mul_nonneg _ _
      (Q'.le_of_lt
        (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hstate))
      (PositiveKernelChainIn.resistance_nonnegative path)
  exact Q'.zero_le_add _ _ hsingle hsingle

theorem simplePositiveCentralFaceRouting_stateEdgeMultiplicity_le_one
    {w : Q'} (hw : (0 : Q') < w) {K state : Nat} (hK : 1 ≤ K)
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (source target : Nat) :
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeMultiplicity
        (simplePositiveCentralFaceRouting hw K hK) state source target ≤
      1 := by
  unfold
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeMultiplicity
  rw [dif_pos hstate]
  apply weightedDirectedEdgeLoad_unitMap_le_one_of_nodup
  apply PositiveKernelChainIn.directedEdges_nodup_of_vertices_nodup
  exact simplePositiveCentralFaceRouting_path_vertices_nodup
    hw hK state 0 hstate
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0)

/-- On the normalized routing, the multiplicity-aware contribution of one
state to one directed edge is no larger than that state's whole route load. -/
theorem simplePositiveCentralFaceRouting_stateEdgeLoad_le_stateLoad
    {w : Q'} (hw : (0 : Q') < w) {K state : Nat} (hK : 1 ≤ K)
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (source target : Nat) :
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad
        (simplePositiveCentralFaceRouting hw K hK) state source target ≤
      centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateLoad
        (simplePositiveCentralFaceRouting hw K hK) state := by
  let routing := simplePositiveCentralFaceRouting hw K hK
  let stateLoad :=
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateLoad
      routing state
  let multiplicity :=
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeMultiplicity
      routing state source target
  have heq :=
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad_eqv_load_mul_multiplicity
      routing state source target
  have hmult : multiplicity ≤ 1 :=
    simplePositiveCentralFaceRouting_stateEdgeMultiplicity_le_one
      hw hK hstate source target
  have hload0 : (0 : Q') ≤ stateLoad :=
    simplePositiveCentralFaceRouting_stateLoad_nonnegative hw hK hstate
  have hscaled : stateLoad * multiplicity ≤ stateLoad * 1 :=
    Q'.mul_le_mul_of_nonneg_left _ _ stateLoad hmult hload0
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq)
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (Q'.mul_one_eqv stateLoad)))

/-! ## 2. A simpler cofinal producer interface -/

/-- For simple central-face paths, it suffices to bound literal edge sharing
and each state's whole route load. -/
structure FixedNomeCofinalPositiveCentralFaceBoundedSharingStateLoad
    {w : Q'} (hw : (0 : Q') < w) : Type where
  start : Nat
  start_positive : 1 ≤ start
  sharingBound : Q'
  stateLoadBound : Q'
  sharingBound_nonnegative : (0 : Q') ≤ sharingBound
  stateLoadBound_nonnegative : (0 : Q') ≤ stateLoadBound
  edgeUsers_cardinality_le : ∀ K, (hK : start ≤ K) →
    ∀ source target,
      Q'.ofNat
          (centralPhysicalFiniteVacuumSectorRoutedRootEdgeUsingStates
            (simplePositiveCentralFaceRouting hw K
              (Nat.le_trans start_positive hK))
            source target).length ≤
        sharingBound
  stateLoad_le : ∀ K, (hK : start ≤ K) →
    ∀ state,
      state ∈ centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0 →
        centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateLoad
            (simplePositiveCentralFaceRouting hw K
              (Nat.le_trans start_positive hK))
            state ≤
          stateLoadBound

namespace FixedNomeCofinalPositiveCentralFaceBoundedSharingStateLoad

def toBoundedSharingEdgeLoad
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalPositiveCentralFaceBoundedSharingStateLoad hw) :
    FixedNomeCofinalPositiveCentralFaceBoundedSharingEdgeLoad hw where
  start := family.start
  start_positive := family.start_positive
  sharingBound := family.sharingBound
  stateEdgeLoadBound := family.stateLoadBound
  sharingBound_nonnegative := family.sharingBound_nonnegative
  stateEdgeLoadBound_nonnegative := family.stateLoadBound_nonnegative
  edgeUsers_cardinality_le := family.edgeUsers_cardinality_le
  stateEdgeLoad_le := by
    intro K hK source target state huser
    obtain ⟨hstate, _hedge⟩ :=
      mem_centralPhysicalFiniteVacuumSectorRoutedRootEdgeUsingStates_iff.mp
        huser
    exact Q'.le_trans' _ _ _
      (simplePositiveCentralFaceRouting_stateEdgeLoad_le_stateLoad
        hw (Nat.le_trans family.start_positive hK) hstate source target)
      (family.stateLoad_le K hK state hstate)

def toSimpleRootResistanceCongestionBound
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalPositiveCentralFaceBoundedSharingStateLoad hw) :
    FixedNomeCofinalVacuumSectorMassExactSimpleRootResistanceCongestionBound
      hw :=
  family.toBoundedSharingEdgeLoad.toSimpleRootResistanceCongestionBound

theorem flowLoad_le_product
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalPositiveCentralFaceBoundedSharingStateLoad hw)
    (K : Nat) (hK : family.start ≤ K) (source target : Nat) :
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad
        (simplePositiveCentralFaceRouting hw K
          (Nat.le_trans family.start_positive hK))
        source target ≤
      family.sharingBound * family.stateLoadBound :=
  family.toBoundedSharingEdgeLoad.flowLoad_le_product K hK source target

theorem nonzero_cardinality_le_cutoff_mul_loadBound
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalPositiveCentralFaceBoundedSharingStateLoad hw)
    (K : Nat) (hK : family.start ≤ K) :
    Q'.ofNat
        (centralPhysicalFiniteVacuumSectorNonzeroIndices
          w (Q'.le_of_lt hw) K).length ≤
      Q'.ofNat K *
        (family.sharingBound * family.stateLoadBound) :=
  family.toBoundedSharingEdgeLoad.nonzero_cardinality_le_cutoff_mul_loadBound
    K hK

end FixedNomeCofinalPositiveCentralFaceBoundedSharingStateLoad

end YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceSimpleStateLoadCompiler

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceSimpleStateLoadCompiler.simplePositiveCentralFaceRouting_stateEdgeMultiplicity_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceSimpleStateLoadCompiler.simplePositiveCentralFaceRouting_stateEdgeLoad_le_stateLoad
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceSimpleStateLoadCompiler.FixedNomeCofinalPositiveCentralFaceBoundedSharingStateLoad.toBoundedSharingEdgeLoad
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceSimpleStateLoadCompiler.FixedNomeCofinalPositiveCentralFaceBoundedSharingStateLoad.flowLoad_le_product
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceSimpleStateLoadCompiler.FixedNomeCofinalPositiveCentralFaceBoundedSharingStateLoad.nonzero_cardinality_le_cutoff_mul_loadBound
