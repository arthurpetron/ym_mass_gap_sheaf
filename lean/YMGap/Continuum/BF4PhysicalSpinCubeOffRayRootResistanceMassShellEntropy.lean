/-
# Cutoff-uniform entropy of BF4 off-ray physical-mass shells

The lower half of the smallest central BF4 slab has exactly 24 physical face
coordinates.  Reading an edge-user source state on those coordinates gives a
natural word of length 24 whose l1 mass is its literal twice-spin shell.
Unary separation encodes a mass-`n` word injectively as a binary word of
length `n + 24`.  Hence every literal directed-edge-user shell has size at
most

    2^(n + 24) = 2^24 * 2^n,

uniformly in representation cutoff and directed edge.

This closes the entropy half of the physical-mass-shell reduction.  It does
not bound the stationary weight times canonical-path resistance of an
individual state; that pointwise decay is the remaining finite analytic
input.  No continuum or Clay conclusion is asserted.  No `Classical`, choice,
`native_decide`, `sorry`, new axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShell
import YMGap.Continuum.CompactDualSlabFaceStrandComponentWeakCompositionCode

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellEntropy

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceEdgeTail
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceFlow
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShell
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMoment
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceSimpleRouting
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeakCompositionCode
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteListIndexQuadraticBridge
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Finite-list reconstruction helpers -/

private theorem listGetD_mem_of_lt {Item : Type} (fallback : Item) :
    ∀ (items : List Item) (index : Nat),
      index < items.length → items.getD index fallback ∈ items
  | [], _, hindex => by simp at hindex
  | _head :: _tail, 0, _ => List.mem_cons_self
  | head :: tail, index + 1, hindex => by
      simp only [List.getD_cons_succ]
      exact List.mem_cons_of_mem head
        (listGetD_mem_of_lt fallback tail index (by
          simp only [List.length_cons] at hindex
          omega))

private theorem listGetD_injective_on_nodup {Item : Type}
    (fallback : Item) :
    ∀ (items : List Item), items.Nodup →
      ∀ left right,
        left < items.length → right < items.length →
        items.getD left fallback = items.getD right fallback →
        left = right
  | [], _, left, _, hleft, _, _ => by simp at hleft
  | _head :: _tail, _, 0, 0, _, _, _ => rfl
  | head :: tail, hnodup, 0, right + 1, _, hright, heq => by
      have hparts := List.nodup_cons.mp hnodup
      have hrightTail : right < tail.length := by
        simp only [List.length_cons] at hright
        omega
      have hmem := listGetD_mem_of_lt fallback tail right hrightTail
      simp only [List.getD_cons_zero, List.getD_cons_succ] at heq
      exfalso
      apply hparts.1
      rw [heq]
      exact hmem
  | head :: tail, hnodup, left + 1, 0, hleft, _, heq => by
      have hparts := List.nodup_cons.mp hnodup
      have hleftTail : left < tail.length := by
        simp only [List.length_cons] at hleft
        omega
      have hmem := listGetD_mem_of_lt fallback tail left hleftTail
      simp only [List.getD_cons_zero, List.getD_cons_succ] at heq
      exfalso
      apply hparts.1
      rw [← heq]
      exact hmem
  | _head :: tail, hnodup, left + 1, right + 1,
      hleft, hright, heq => by
      have hparts := List.nodup_cons.mp hnodup
      simp only [List.length_cons] at hleft hright
      simp only [List.getD_cons_succ] at heq
      exact congrArg Nat.succ
        (listGetD_injective_on_nodup fallback tail hparts.2
          left right (by omega) (by omega) heq)

private theorem map_functions_eq_on_mem_local
    {Item Value : Type} (left right : Item → Value) :
    ∀ items : List Item,
      items.map left = items.map right →
      ∀ item, item ∈ items → left item = right item
  | [], _, item, hmem => absurd hmem List.not_mem_nil
  | head :: tail, heq, item, hmem => by
      have hparts : left head = right head ∧
          tail.map left = tail.map right := by
        simpa only [List.map_cons, List.cons.injEq] using heq
      rcases List.mem_cons.mp hmem with hitem | hitem
      · subst item
        exact hparts.1
      · exact map_functions_eq_on_mem_local left right tail
          hparts.2 item hitem

private theorem edgeLabelling_eq_of_word_eq_of_supported_local
    (edges : List Nat) (left right : EdgeLabelling)
    (hleft : ∀ edge, edge ∉ edges → left edge = 0)
    (hright : ∀ edge, edge ∉ edges → right edge = 0)
    (hword : edges.map left = edges.map right) :
    left = right := by
  funext edge
  by_cases hedge : edge ∈ edges
  · exact map_functions_eq_on_mem_local left right edges
      hword edge hedge
  · rw [hleft edge hedge, hright edge hedge]

private theorem natListSum_map_eq_listNatWeight_local
    {Item : Type} (weight : Item → Nat) :
    ∀ items : List Item,
      natListSum (items.map weight) = listNatWeight weight items
  | [] => rfl
  | _head :: tail => by
      simp only [List.map_cons, natListSum, listNatWeight]
      rw [natListSum_map_eq_listNatWeight_local weight tail]

/-! ## 2. The literal 24-coordinate word and its injectivity -/

def centralLowerExcitedSpinCubeOffRayRootPhysicalWord
    (w : Q') (hw : (0 : Q') ≤ w) (K state : Nat) : List Nat :=
  (centralLowerFaceIds 0).map
    (centralPhysicalFiniteStateAt w hw K 0 state)

theorem centralLowerExcitedSpinCubeOffRayRootPhysicalWord_length
    (w : Q') (hw : (0 : Q') ≤ w) (K state : Nat) :
    (centralLowerExcitedSpinCubeOffRayRootPhysicalWord
      w hw K state).length = 24 := by
  unfold centralLowerExcitedSpinCubeOffRayRootPhysicalWord
  rw [List.length_map]
  decide

theorem centralLowerExcitedSpinCubeOffRayRootPhysicalWord_mass
    (w : Q') (hw : (0 : Q') ≤ w) (K state : Nat) :
    natListSum
        (centralLowerExcitedSpinCubeOffRayRootPhysicalWord
          w hw K state) =
      centralLowerExcitedSpinCubeOffRayRootStatePhysicalMass
        w hw K state := by
  unfold centralLowerExcitedSpinCubeOffRayRootPhysicalWord
    centralLowerExcitedSpinCubeOffRayRootStatePhysicalMass
  exact natListSum_map_eq_listNatWeight_local _ _

private theorem physicalMassShellState_mem_sector
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K source target shell state : Nat}
    (hstate : state ∈
      centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellStates
        w hw K source target shell) :
    state ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0 := by
  have hedge := (List.mem_filter.mp hstate).1
  have hoffRay :=
    (mem_centralLowerExcitedSpinCubeOffRayRootEdgeUsingStates_iff.mp
      hedge).1
  exact (List.mem_filter.mp hoffRay).1

private theorem centralLowerExcitedSpinCubeOffRayRootPhysicalWord_injective_on_shell
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K source target shell left right : Nat}
    (hleft : left ∈
      centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellStates
        w hw K source target shell)
    (hright : right ∈
      centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellStates
        w hw K source target shell)
    (hword : centralLowerExcitedSpinCubeOffRayRootPhysicalWord
        w hw K left =
      centralLowerExcitedSpinCubeOffRayRootPhysicalWord
        w hw K right) :
    left = right := by
  have hleftSector := physicalMassShellState_mem_sector hleft
  have hrightSector := physicalMassShellState_mem_sector hright
  have hleftLt := centralPhysicalFiniteVacuumSectorIndex_lt
    w hw K 0 hleftSector
  have hrightLt := centralPhysicalFiniteVacuumSectorIndex_lt
    w hw K 0 hrightSector
  have hleftPositive := centralPhysicalFiniteStateAt_mem_positive
    w hw K 0 hleftLt
  have hrightPositive := centralPhysicalFiniteStateAt_mem_positive
    w hw K 0 hrightLt
  have hleftHalf := (mem_centralPositiveHalfStates_iff.mp hleftPositive).1
  have hrightHalf := (mem_centralPositiveHalfStates_iff.mp hrightPositive).1
  have hleftSupport := (boundedEdgeLabellings_sound K
    (centralLowerFaceIds 0)
    (centralPhysicalFiniteStateAt w hw K 0 left)
    (by simpa [centralHalfStates] using hleftHalf)).2
  have hrightSupport := (boundedEdgeLabellings_sound K
    (centralLowerFaceIds 0)
    (centralPhysicalFiniteStateAt w hw K 0 right)
    (by simpa [centralHalfStates] using hrightHalf)).2
  have hstateEq : centralPhysicalFiniteStateAt w hw K 0 left =
      centralPhysicalFiniteStateAt w hw K 0 right := by
    apply edgeLabelling_eq_of_word_eq_of_supported_local
      (centralLowerFaceIds 0) _ _ hleftSupport hrightSupport
    simpa [centralLowerExcitedSpinCubeOffRayRootPhysicalWord] using hword
  apply listGetD_injective_on_nodup zeroEdgeLabelling
    (centralPositiveHalfStates w hw K 0)
    (centralPositiveHalfStates_nodup w hw K 0)
    left right hleftLt hrightLt
  simpa [centralPhysicalFiniteStateAt, finiteListStateAt] using hstateEq

/-! ## 3. Binary entropy injection and exact cardinality bound -/

def centralLowerExcitedSpinCubeOffRayRootPhysicalMassUnaryCode
    (w : Q') (hw : (0 : Q') ≤ w) (K state : Nat) : List Nat :=
  unarySeparatedNatWord
    (centralLowerExcitedSpinCubeOffRayRootPhysicalWord w hw K state)

private theorem unarySeparatedNatWord_injective_local :
    ∀ left right : List Nat,
      unarySeparatedNatWord left = unarySeparatedNatWord right → left = right := by
  intro left right heq
  have hdecoded := congrArg (decodeCompletedUnary 0) heq
  have hleft :=
    decodeCompletedUnary_unarySeparated_append_replicate_one left 0
  have hright :=
    decodeCompletedUnary_unarySeparated_append_replicate_one right 0
  simp only [List.replicate_zero, List.append_nil] at hleft hright
  exact hleft.symm.trans (hdecoded.trans hright)

private theorem centralLowerExcitedSpinCubeOffRayRootPhysicalMassUnaryCode_injective_on_shell
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K source target shell left right : Nat}
    (hleft : left ∈
      centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellStates
        w hw K source target shell)
    (hright : right ∈
      centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellStates
        w hw K source target shell)
    (hcode : centralLowerExcitedSpinCubeOffRayRootPhysicalMassUnaryCode
        w hw K left =
      centralLowerExcitedSpinCubeOffRayRootPhysicalMassUnaryCode
        w hw K right) :
    left = right := by
  apply centralLowerExcitedSpinCubeOffRayRootPhysicalWord_injective_on_shell
    hleft hright
  apply unarySeparatedNatWord_injective_local
  simpa [centralLowerExcitedSpinCubeOffRayRootPhysicalMassUnaryCode]
    using hcode

theorem centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellStates_length_le_binary
    (w : Q') (hw : (0 : Q') ≤ w) (K source target shell : Nat) :
    (centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellStates
        w hw K source target shell).length ≤
      2 ^ (shell + 24) := by
  let states :=
    centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellStates
      w hw K source target shell
  let encode :=
    centralLowerExcitedSpinCubeOffRayRootPhysicalMassUnaryCode w hw K
  let codes := states.map encode
  have hstatesNodup : states.Nodup := by
    unfold states
    exact List.filter_sublist.nodup
      (List.filter_sublist.nodup
        (List.filter_sublist.nodup
          (centralPhysicalFiniteVacuumSectorIndices_nodup w hw K 0)))
  have hcodesNodup : codes.Nodup := by
    apply nodup_map_of_injOn encode states hstatesNodup
    intro left hleft right hright heq
    exact
      centralLowerExcitedSpinCubeOffRayRootPhysicalMassUnaryCode_injective_on_shell
        hleft hright heq
  have hsubset : ∀ code, code ∈ codes →
      code ∈ allSeqs 2 (shell + 24) := by
    intro code hcode
    obtain ⟨state, hstate, rfl⟩ := List.mem_map.mp hcode
    apply mem_allSeqs 2 (shell + 24)
    · unfold encode
      rw [centralLowerExcitedSpinCubeOffRayRootPhysicalMassUnaryCode,
        unarySeparatedNatWord_length,
        centralLowerExcitedSpinCubeOffRayRootPhysicalWord_mass,
        centralLowerExcitedSpinCubeOffRayRootPhysicalWord_length]
      have hparts := List.mem_filter.mp hstate
      have hmass :
          centralLowerExcitedSpinCubeOffRayRootStatePhysicalMass
              w hw K state = shell :=
        of_decide_eq_true hparts.2
      omega
    · intro bit hbit
      exact unarySeparatedNatWord_entry_lt_two
        (centralLowerExcitedSpinCubeOffRayRootPhysicalWord w hw K state)
        bit hbit
  have hcount := nodup_subset_length_le
    codes (allSeqs 2 (shell + 24)) hcodesNodup hsubset
  unfold codes at hcount
  rw [List.length_map, length_allSeqs] at hcount
  exact hcount

/-! ## 4. Rational geometric entropy and the reduced physical input -/

def physicalMassShellEntropyAmplitude : Q' := Q'.ofNat (2 ^ 24)

def physicalMassShellEntropyBase : Q' := Q'.ofNat 2

private theorem ofNat_mul_eqv_local (left right : Nat) :
    Q'.ofNat (left * right) ≈ Q'.ofNat left * Q'.ofNat right := by
  show (left * right : Int) *
      ((Q'.ofNat left * Q'.ofNat right).den : Int) =
    (Q'.ofNat left * Q'.ofNat right).num * (1 : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Int.mul_one]

private theorem ofNat_pow_eqv_local (base : Nat) : ∀ exponent : Nat,
    Q'.ofNat (base ^ exponent) ≈ (Q'.ofNat base) ^ exponent
  | 0 => by
      rw [Nat.pow_zero, Q'.pow_zero]
      change ((1 : Q') ≈ (1 : Q'))
      exact Q'.eqv_refl _
  | exponent + 1 => by
      rw [Nat.pow_succ, Q'.pow_succ]
      refine Q'.eqv_trans _
        (Q'.ofNat (base ^ exponent) * Q'.ofNat base) _
        (ofNat_mul_eqv_local (base ^ exponent) base) ?_
      refine Q'.eqv_trans _
        (Q'.ofNat base * Q'.ofNat (base ^ exponent)) _
        (Q'.mul_comm_eqv _ _) ?_
      exact Q'.mul_eqv_congr_left _ _ _
        (ofNat_pow_eqv_local base exponent)

theorem centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellStates_cardinality_le_entropy
    (w : Q') (hw : (0 : Q') ≤ w) (K source target shell : Nat) :
    Q'.ofNat
        (centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellStates
          w hw K source target shell).length ≤
      physicalMassShellEntropyAmplitude *
        physicalMassShellEntropyBase ^ shell := by
  have hcount :=
    centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellStates_length_le_binary
      w hw K source target shell
  have hcast := Q'.ofNat_le_ofNat hcount
  have hnat : 2 ^ (shell + 24) = (2 ^ 24) * (2 ^ shell) := by
    rw [Nat.pow_add, Nat.mul_comm]
  rw [hnat] at hcast
  refine Q'.le_trans' _ _ _ hcast (Q'.le_of_eqv ?_)
  unfold physicalMassShellEntropyAmplitude physicalMassShellEntropyBase
  exact Q'.eqv_trans _ _ _
    (ofNat_mul_eqv_local (2 ^ 24) (2 ^ shell))
    (Q'.mul_eqv_congr_left _ _ _ (ofNat_pow_eqv_local 2 shell))

/-- After the unconditional entropy count, the sole remaining factorized
mass-shell input is pointwise decay of the actual stationary-resistance load.
-/
structure FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassStateLoadDecay
    {w : Q'} (hw : (0 : Q') < w) : Type 1 where
  start : Nat
  loadAmplitude : Q'
  loadRatio : Q'
  budget : Q'
  loadAmplitude_nonnegative : (0 : Q') ≤ loadAmplitude
  loadRatio_nonnegative : (0 : Q') ≤ loadRatio
  combinedRatio_lt_one :
    physicalMassShellEntropyBase * loadRatio < (1 : Q')
  budget_nonnegative : (0 : Q') ≤ budget
  geometric_step :
    physicalMassShellEntropyAmplitude * loadAmplitude +
        (physicalMassShellEntropyBase * loadRatio) * budget ≤ budget
  stateLoad_le : ∀ K, start ≤ K → ∀ source target (shell state : Nat),
    shell < centralLowerExcitedSpinCubeOffRayRootPhysicalMassShellCount
      w (Q'.le_of_lt hw) K →
    state ∈ centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellStates
      w (Q'.le_of_lt hw) K source target shell →
    centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad
        w (Q'.le_of_lt hw) K state ≤
      loadAmplitude * loadRatio ^ shell

namespace FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassStateLoadDecay

def toPhysicalMassShellBound
    {w : Q'} {hw : (0 : Q') < w}
    (decay :
      FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassStateLoadDecay
        hw) :
    FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassShellBound hw where
  start := decay.start
  entropyAmplitude := physicalMassShellEntropyAmplitude
  entropyBase := physicalMassShellEntropyBase
  loadAmplitude := decay.loadAmplitude
  loadRatio := decay.loadRatio
  budget := decay.budget
  entropyAmplitude_nonnegative := Q'.ofNat_le_ofNat (Nat.zero_le _)
  entropyBase_nonnegative := Q'.ofNat_le_ofNat (Nat.zero_le _)
  loadAmplitude_nonnegative := decay.loadAmplitude_nonnegative
  loadRatio_nonnegative := decay.loadRatio_nonnegative
  combinedRatio_lt_one := decay.combinedRatio_lt_one
  budget_nonnegative := decay.budget_nonnegative
  geometric_step := decay.geometric_step
  shellCardinality_le := fun K _hK source target shell _hshell =>
    centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellStates_cardinality_le_entropy
      w (Q'.le_of_lt hw) K source target shell
  stateLoad_le := decay.stateLoad_le

def toResistanceCongestionBound
    {w : Q'} {hw : (0 : Q') < w}
    (decay :
      FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassStateLoadDecay
        hw) :
    FixedNomeCofinalSpinCubeOffRayRootResistanceCongestionBound hw :=
  decay.toPhysicalMassShellBound.toResistanceCongestionBound

def toSimpleRootResistanceCongestionBound
    {w : Q'} {hw : (0 : Q') < w}
    (decay :
      FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassStateLoadDecay
        hw)
    (ray : FixedNomeCofinalSpinCubeRayCapacity hw) :
    FixedNomeCofinalVacuumSectorMassExactSimpleRootResistanceCongestionBound
      hw :=
  decay.toPhysicalMassShellBound.toSimpleRootResistanceCongestionBound ray

end FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassStateLoadDecay

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellEntropy

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellEntropy.centralLowerExcitedSpinCubeOffRayRootPhysicalWord_length
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellEntropy.centralLowerExcitedSpinCubeOffRayRootPhysicalWord_mass
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellEntropy.centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellStates_length_le_binary
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellEntropy.centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellStates_cardinality_le_entropy
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellEntropy.FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassStateLoadDecay.toPhysicalMassShellBound
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellEntropy.FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassStateLoadDecay.toResistanceCongestionBound
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellEntropy.FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassStateLoadDecay.toSimpleRootResistanceCongestionBound
