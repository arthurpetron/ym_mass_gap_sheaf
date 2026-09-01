/-
# Raw state-load comparison for the positive central-face BF4 routing

The normalized central-face routing is obtained by loop erasing an explicit
prefix-to-spin-cube route followed by one certified spin-cube-to-vacuum edge.
This module moves the remaining whole-route state-load estimate back to that
raw construction.  Loop erasure cannot increase resistance, while the raw
route resistance is exactly the prefix resistance plus the reciprocal
terminal conductance.

Thus a future cutoff-uniform state-load proof may work directly with the
explicit prefix and final spoke.  No such uniform estimate, congestion bound,
finite gap, physical scaling, continuum theory, or Clay conclusion is
asserted here.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceSimpleStateLoadCompiler

namespace YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceRawStateLoad

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorResistanceCauchy
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceEdgeTail
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceFlow
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceSimpleRouting
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceSimpleStateLoadCompiler
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalPrefixAssignment
open YMGap.Continuum.BF4PhysicalVacuumSectorSpinCubeTerminalPrefixCompiler
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Resistance of a concatenated positive chain -/

theorem positiveKernelChain_resistance_trans
    {State : Type} {kernel : State → State → Q'}
    {support : List State} :
    ∀ {first middle last : State}
      (left : PositiveKernelChainIn kernel support first middle)
      (right : PositiveKernelChainIn kernel support middle last),
      PositiveKernelChainIn.resistance (left.trans right) ≈
        PositiveKernelChainIn.resistance left +
          PositiveKernelChainIn.resistance right
  | _, _, _, PositiveKernelChainIn.refl _, right =>
      Q'.eqv_symm
        (Q'.eqv_of_eq
          (Q'.zero_add' (PositiveKernelChainIn.resistance right)))
  | _, _, _, PositiveKernelChainIn.step positive hnext rest, right => by
      simp only [PositiveKernelChainIn.trans,
        PositiveKernelChainIn.resistance]
      refine Q'.eqv_trans _
        (Q'.recipPos _ positive +
          (PositiveKernelChainIn.resistance rest +
            PositiveKernelChainIn.resistance right)) _
        (Q'.add_eqv_congr_left _ _ _
          (positiveKernelChain_resistance_trans rest right)) ?_
      exact Q'.eqv_symm
        (Q'.add_assoc_eqv
          (Q'.recipPos _ positive)
          (PositiveKernelChainIn.resistance rest)
          (PositiveKernelChainIn.resistance right))

/-! ## 2. Exact raw prefix-plus-terminal resistance -/

theorem rootPath_resistance_eqv_prefix_add_terminalReciprocal
    {w : Q'} (hw : (0 : Q') < w) {K state : Nat}
    (assignment :
      CentralPhysicalFiniteVacuumSectorSpinCubeTerminalPrefixAssignmentAt
        w hw K)
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (hne : state ≠ 0) :
    PositiveKernelChainIn.resistance
        (assignment.rootPath state hstate hne) ≈
      PositiveKernelChainIn.resistance
          (assignment.prefixPath state hstate hne) +
        Q'.recipPos
          (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0
            (centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K
              (assignment.terminalSpin state)) 0)
          (centralPhysicalFiniteKernel_spinCubeIndex_zero_pos hw
            (assignment.terminalSpin_le state hstate hne)) := by
  unfold CentralPhysicalFiniteVacuumSectorSpinCubeTerminalPrefixAssignmentAt.rootPath
  refine Q'.eqv_trans _
    (PositiveKernelChainIn.resistance
        (assignment.prefixPath state hstate hne) +
      PositiveKernelChainIn.resistance
        (centralLowerSpinCubeToVacuumSpoke hw
          (assignment.terminalSpin_le state hstate hne))) _
    (positiveKernelChain_resistance_trans _ _) ?_
  apply Q'.add_eqv_congr_left
  exact Q'.eqv_of_eq (Q'.add_zero' _)

/-! ## 3. Loop-erased state load is dominated by the raw state load -/

theorem simplePositiveCentralFaceRouting_stateLoad_le_raw
    {w : Q'} (hw : (0 : Q') < w) {K state : Nat} (hK : 1 ≤ K) :
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateLoad
        (simplePositiveCentralFaceRouting hw K hK) state ≤
      centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateLoad
        (positiveCentralFaceSpinTerminalPrefixAssignment
          hw K hK).toPositiveRouting state := by
  unfold centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateLoad
  by_cases hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0
  · rw [dif_pos hstate, dif_pos hstate]
    let raw :=
      (positiveCentralFaceSpinTerminalPrefixAssignment
        hw K hK).toPositiveRouting
    let rootMem := zero_mem_centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0
    let weight := centralPhysicalFiniteWeight
      w (Q'.le_of_lt hw) K 0 state
    have hweight : (0 : Q') ≤ weight :=
      Q'.le_of_lt
        (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hstate)
    have hres :
        PositiveKernelChainIn.resistance
            ((simplePositiveCentralFaceRouting hw K hK).path
              state 0 hstate rootMem) ≤
          PositiveKernelChainIn.resistance
            (raw.path state 0 hstate rootMem) := by
      exact
        loopErasedCentralPhysicalFiniteVacuumSectorPositiveRoutingAt_path_resistance_le
          raw hstate rootMem
    have hsingle :
        weight * PositiveKernelChainIn.resistance
            ((simplePositiveCentralFaceRouting hw K hK).path
              state 0 hstate rootMem) ≤
          weight * PositiveKernelChainIn.resistance
            (raw.path state 0 hstate rootMem) :=
      Q'.mul_le_mul_of_nonneg_left _ _ weight hres hweight
    exact Q'.add_le_add hsingle hsingle
  · rw [dif_neg hstate, dif_neg hstate]
    exact Q'.le_refl' 0

theorem positiveCentralFaceRawRouting_stateLoad_eqv_prefixTerminal
    {w : Q'} (hw : (0 : Q') < w) {K state : Nat} (hK : 1 ≤ K)
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (hne : state ≠ 0) :
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateLoad
        (positiveCentralFaceSpinTerminalPrefixAssignment
          hw K hK).toPositiveRouting state ≈
      let assignment :=
        positiveCentralFaceSpinTerminalPrefixAssignment hw K hK
      let terminalResistance :=
        Q'.recipPos
          (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0
            (centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K
              (assignment.terminalSpin state)) 0)
          (centralPhysicalFiniteKernel_spinCubeIndex_zero_pos hw
            (assignment.terminalSpin_le state hstate hne))
      let singleLoad :=
        centralPhysicalFiniteWeight w (Q'.le_of_lt hw) K 0 state *
          (PositiveKernelChainIn.resistance
              (assignment.prefixPath state hstate hne) +
            terminalResistance)
      singleLoad + singleLoad := by
  unfold centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateLoad
  rw [dif_pos hstate]
  rw [CentralPhysicalFiniteVacuumSectorSpinCubeTerminalPrefixAssignmentAt.toPositiveRouting_rootPath
    (positiveCentralFaceSpinTerminalPrefixAssignment hw K hK) hstate hne]
  let assignment := positiveCentralFaceSpinTerminalPrefixAssignment hw K hK
  have hres := rootPath_resistance_eqv_prefix_add_terminalReciprocal
    hw assignment hstate hne
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left _ _ _ hres)
    (Q'.mul_eqv_congr_left _ _ _ hres)

theorem positiveCentralFaceRawRouting_zero_stateLoad_eqv_zero
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K) :
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateLoad
        (positiveCentralFaceSpinTerminalPrefixAssignment
          hw K hK).toPositiveRouting 0 ≈ 0 := by
  unfold centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateLoad
  rw [dif_pos
    (zero_mem_centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)]
  unfold
    CentralPhysicalFiniteVacuumSectorSpinCubeTerminalPrefixAssignmentAt.toPositiveRouting
  refine Q'.eqv_trans _ (0 + 0) _
    (Q'.add_eqv_congr'
      (Q'.mul_zero_eqv _)
      (Q'.mul_zero_eqv _)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' 0)

/-! ## 4. The remaining state-load producer is an explicit expression -/

/-- Twice the stationary weight times the raw prefix resistance plus the
reciprocal conductance of its selected terminal spoke.  The vacuum is assigned
zero load because its compiled raw root route is reflexive. -/
def positiveCentralFacePrefixTerminalStateLoad
    {w : Q'} (hw : (0 : Q') < w) {K state : Nat} (hK : 1 ≤ K)
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0) : Q' :=
  if hne : state ≠ 0 then
    let assignment :=
      positiveCentralFaceSpinTerminalPrefixAssignment hw K hK
    let terminalResistance :=
      Q'.recipPos
        (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0
          (centralLowerSpinCubeIndex w (Q'.le_of_lt hw) K
            (assignment.terminalSpin state)) 0)
        (centralPhysicalFiniteKernel_spinCubeIndex_zero_pos hw
          (assignment.terminalSpin_le state hstate hne))
    let singleLoad :=
      centralPhysicalFiniteWeight w (Q'.le_of_lt hw) K 0 state *
        (PositiveKernelChainIn.resistance
            (assignment.prefixPath state hstate hne) +
          terminalResistance)
    singleLoad + singleLoad
  else 0

theorem positiveCentralFaceRawRouting_stateLoad_eqv_prefixTerminalStateLoad
    {w : Q'} (hw : (0 : Q') < w) {K state : Nat} (hK : 1 ≤ K)
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0) :
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateLoad
        (positiveCentralFaceSpinTerminalPrefixAssignment
          hw K hK).toPositiveRouting state ≈
      positiveCentralFacePrefixTerminalStateLoad hw hK hstate := by
  unfold positiveCentralFacePrefixTerminalStateLoad
  by_cases hne : state ≠ 0
  · rw [dif_pos hne]
    exact positiveCentralFaceRawRouting_stateLoad_eqv_prefixTerminal
      hw hK hstate hne
  · rw [dif_neg hne]
    have hzero : state = 0 := by
      cases state with
      | zero => rfl
      | succ predecessor =>
          exact False.elim (hne (Nat.succ_ne_zero predecessor))
    subst state
    exact positiveCentralFaceRawRouting_zero_stateLoad_eqv_zero hw hK

/-- A producer may now bound the literal central-face prefix formula rather
than reason about the dependent loop-erased route.  Edge sharing is still
measured on the normalized routing because that is the route used by the
downstream exact congestion theorem. -/
structure FixedNomeCofinalPositiveCentralFaceBoundedSharingPrefixTerminalLoad
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
  prefixTerminalStateLoad_le : ∀ K, (hK : start ≤ K) →
    ∀ state,
      (hstate : state ∈ centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0) →
        positiveCentralFacePrefixTerminalStateLoad hw
            (Nat.le_trans start_positive hK) hstate ≤
          stateLoadBound

namespace FixedNomeCofinalPositiveCentralFaceBoundedSharingPrefixTerminalLoad

def toBoundedSharingStateLoad
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalPositiveCentralFaceBoundedSharingPrefixTerminalLoad hw) :
    FixedNomeCofinalPositiveCentralFaceBoundedSharingStateLoad hw where
  start := family.start
  start_positive := family.start_positive
  sharingBound := family.sharingBound
  stateLoadBound := family.stateLoadBound
  sharingBound_nonnegative := family.sharingBound_nonnegative
  stateLoadBound_nonnegative := family.stateLoadBound_nonnegative
  edgeUsers_cardinality_le := family.edgeUsers_cardinality_le
  stateLoad_le := by
    intro K hK state hstate
    have hsimple := simplePositiveCentralFaceRouting_stateLoad_le_raw
      hw (Nat.le_trans family.start_positive hK)
        (state := state)
    have hraw :=
      positiveCentralFaceRawRouting_stateLoad_eqv_prefixTerminalStateLoad
        hw (Nat.le_trans family.start_positive hK) hstate
    exact Q'.le_trans' _ _ _ hsimple
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hraw)
        (family.prefixTerminalStateLoad_le K hK state hstate))

def toSimpleRootResistanceCongestionBound
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalPositiveCentralFaceBoundedSharingPrefixTerminalLoad hw) :
    FixedNomeCofinalVacuumSectorMassExactSimpleRootResistanceCongestionBound
      hw :=
  family.toBoundedSharingStateLoad.toSimpleRootResistanceCongestionBound

theorem flowLoad_le_product
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalPositiveCentralFaceBoundedSharingPrefixTerminalLoad hw)
    (K : Nat) (hK : family.start ≤ K) (source target : Nat) :
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad
        (simplePositiveCentralFaceRouting hw K
          (Nat.le_trans family.start_positive hK))
        source target ≤
      family.sharingBound * family.stateLoadBound :=
  family.toBoundedSharingStateLoad.flowLoad_le_product
    K hK source target

end FixedNomeCofinalPositiveCentralFaceBoundedSharingPrefixTerminalLoad

end YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceRawStateLoad

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceRawStateLoad.positiveKernelChain_resistance_trans
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceRawStateLoad.rootPath_resistance_eqv_prefix_add_terminalReciprocal
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceRawStateLoad.simplePositiveCentralFaceRouting_stateLoad_le_raw
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceRawStateLoad.positiveCentralFaceRawRouting_stateLoad_eqv_prefixTerminal
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceRawStateLoad.positiveCentralFaceRawRouting_stateLoad_eqv_prefixTerminalStateLoad
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceRawStateLoad.FixedNomeCofinalPositiveCentralFaceBoundedSharingPrefixTerminalLoad.toBoundedSharingStateLoad
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceRawStateLoad.FixedNomeCofinalPositiveCentralFaceBoundedSharingPrefixTerminalLoad.flowLoad_le_product
