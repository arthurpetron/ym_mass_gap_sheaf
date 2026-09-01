/-
# Path-length shells for the BF4 off-ray root resistance load

The exact off-ray edge tail is local in the directed edge but still sums over
all off-ray source states whose canonical simple root path uses that edge.
This module partitions that literal source carrier by the actual edge length
of its canonical path to the vacuum.

The partition is exact.  Every selected path has length at most the finite
vacuum-sector carrier size, so all shells occur in one explicit finite range.
Consequently a cutoff-independent geometric bound on each concrete shell
implies a cutoff-independent bound on every local off-ray edge load.  Combined
with the explicit ray capacity, it constructs the full simple cofinal routing
certificate.

No geometric shell estimate is inhabited here.  That estimate is the named
physical analytic input: it must control the genuine stationary-resistance
load of the genuine BF4 path-length shell, uniformly in cutoff and edge.  No
continuum or Clay conclusion is asserted.  No `Classical`, choice,
`native_decide`, `sorry`, new axiom, or noncomputable declaration is used.
-/

import YMGap.Constructive.GeometricTail
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceEdgeTail
import YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayRootFlow

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceLengthShell

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceEdgeTail
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceFlow
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMoment
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceSimpleRouting
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayRootFlow
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Generic exact finite shell partition -/

private theorem listQSum_eqIndicator_eqv_zero_of_not_mem
    (index : Nat) (value : Q') :
    ∀ items : List Nat, index ∉ items →
      listQSum
          (fun item => if decide (index = item) then value else 0)
          items ≈ 0
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hnot => by
      have hhead : index ≠ head := by
        intro heq
        apply hnot
        exact List.mem_cons.mpr (Or.inl heq)
      have htail : index ∉ tail := by
        intro hmem
        exact hnot (List.mem_cons_of_mem head hmem)
      simp only [listQSum, hhead, decide_false]
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left 0 _ _
          (listQSum_eqIndicator_eqv_zero_of_not_mem
            index value tail htail))
        (Q'.eqv_of_eq (Q'.zero_add' 0))

private theorem listQSum_eqIndicator_eqv_value_of_mem_nodup
    (index : Nat) (value : Q') :
    ∀ items : List Nat, items.Nodup → index ∈ items →
      listQSum
          (fun item => if decide (index = item) then value else 0)
          items ≈ value
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, hnodup, hmem => by
      have hparts := List.nodup_cons.mp hnodup
      by_cases hhead : index = head
      · subst index
        have htailZero :=
          listQSum_eqIndicator_eqv_zero_of_not_mem
            head value tail hparts.1
        simp only [listQSum, decide_true, if_true]
        exact Q'.eqv_trans _ (value + 0) _
          (Q'.add_eqv_congr_left value _ _ htailZero)
          (Q'.eqv_of_eq (Q'.add_zero' value))
      · have htail : index ∈ tail :=
          (List.mem_cons.mp hmem).resolve_left hhead
        simp only [listQSum, hhead, decide_false]
        exact Q'.eqv_trans _ (0 + value) _
          (Q'.add_eqv_congr_left 0 _ _
            (listQSum_eqIndicator_eqv_value_of_mem_nodup
              index value tail hparts.2 htail))
          (Q'.eqv_of_eq (Q'.zero_add' value))

private theorem range_nodup_local :
    ∀ bound : Nat, (List.range bound).Nodup
  | 0 => List.nodup_nil
  | bound + 1 => by
      rw [List.range_succ]
      apply List.nodup_append.mpr
      refine ⟨range_nodup_local bound,
        List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro left hleft right hright heq
      have hrightEq : right = bound := List.mem_singleton.mp hright
      rw [heq, hrightEq] at hleft
      exact absurd (List.mem_range.mp hleft) (Nat.lt_irrefl bound)

private theorem listQSum_zero_local {Item : Type} :
    ∀ items : List Item, listQSum (fun _item => (0 : Q')) items ≈ 0
  | [] => Q'.eqv_refl 0
  | _head :: tail => by
      exact Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr_left 0 _ _ (listQSum_zero_local tail))
        (Q'.eqv_of_eq (Q'.zero_add' 0))

/-- Exact partition of a finite nonnegative-or-signed rational sum by any
natural-valued shell statistic with a supplied finite range. -/
theorem listQSum_shell_partition
    {Item : Type} (value : Item → Q') (shell : Item → Nat) :
    ∀ (items : List Item) (bound : Nat),
      (∀ item, item ∈ items → shell item < bound) →
      listQSum
          (fun shellId =>
            listQSum value
              (items.filter (fun item => decide (shell item = shellId))))
          (List.range bound) ≈
        listQSum value items
  | [], bound, _ => by
      exact Q'.eqv_trans _ _ _
        (listQSum_congr
          (fun _shellId => Q'.eqv_refl 0) (List.range bound))
        (listQSum_zero_local (List.range bound))
  | head :: tail, bound, hbound => by
      let headValue : Nat → Q' := fun shellId =>
        if decide (shell head = shellId) then value head else 0
      let tailValue : Nat → Q' := fun shellId =>
        listQSum value
          (tail.filter (fun item => decide (shell item = shellId)))
      have hpointwise :
          listQSum
              (fun shellId =>
                listQSum value
                  ((head :: tail).filter
                    (fun item => decide (shell item = shellId))))
              (List.range bound) ≈
            listQSum
              (fun shellId => headValue shellId + tailValue shellId)
              (List.range bound) := by
        apply listQSum_congr
        intro shellId
        by_cases hshell : shell head = shellId
        · simp only [List.filter_cons, hshell, decide_true, if_true,
            listQSum, headValue, tailValue]
          exact Q'.eqv_refl _
        · simp only [List.filter_cons, hshell, decide_false,
            headValue, tailValue]
          exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _))
      have hheadMem : shell head ∈ List.range bound :=
        List.mem_range.mpr (hbound head List.mem_cons_self)
      have hheadSum : listQSum headValue (List.range bound) ≈ value head := by
        unfold headValue
        exact listQSum_eqIndicator_eqv_value_of_mem_nodup
          (shell head) (value head) (List.range bound)
          (range_nodup_local bound) hheadMem
      have htailBound : ∀ item, item ∈ tail → shell item < bound := by
        intro item hitem
        exact hbound item (List.mem_cons_of_mem head hitem)
      have htailSum : listQSum tailValue (List.range bound) ≈
          listQSum value tail := by
        unfold tailValue
        exact listQSum_shell_partition value shell tail bound htailBound
      exact Q'.eqv_trans _ _ _ hpointwise
        (Q'.eqv_trans _ _ _
          (listQSum_add headValue tailValue (List.range bound))
          (Q'.add_eqv_congr' hheadSum htailSum))

theorem listQSum_range_eqv_finSum (value : Nat → Q') :
    ∀ count : Nat,
      listQSum value (List.range count) ≈ finSum value count
  | 0 => Q'.eqv_refl 0
  | count + 1 => by
      rw [List.range_succ, finSum_succ]
      exact Q'.eqv_trans _
        (listQSum value (List.range count) + listQSum value [count]) _
        (listQSum_append value (List.range count) [count])
        (Q'.add_eqv_congr'
          (listQSum_range_eqv_finSum value count)
          (Q'.eqv_of_eq (Q'.add_zero' (value count))))

/-! ## 2. Concrete canonical path-length shells -/

def centralLowerExcitedSpinCubeOffRayRootStatePathLength
    (w : Q') (hw : (0 : Q') ≤ w) (K state : Nat) : Nat :=
  if hstate : state ∈ centralLowerExcitedSpinCubeOffRayIndices w hw K then
    PositiveKernelChainIn.edgeLength
      (centralLowerExcitedSpinCubeOffRayRootPositivePath state hstate)
  else 0

def centralLowerExcitedSpinCubeOffRayRootLengthShellCount
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : Nat :=
  (centralPhysicalFiniteVacuumSectorIndices w hw K 0).length + 1

def centralLowerExcitedSpinCubeOffRayRootEdgeLengthShellStates
    (w : Q') (hw : (0 : Q') ≤ w)
    (K source target shell : Nat) : List Nat :=
  (centralLowerExcitedSpinCubeOffRayRootEdgeUsingStates
      w hw K source target).filter
    (fun state => decide
      (centralLowerExcitedSpinCubeOffRayRootStatePathLength
        w hw K state = shell))

def centralLowerExcitedSpinCubeOffRayRootResistanceEdgeLengthShellLoad
    (w : Q') (hw : (0 : Q') ≤ w)
    (K source target shell : Nat) : Q' :=
  listQSum
    (centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad w hw K)
    (centralLowerExcitedSpinCubeOffRayRootEdgeLengthShellStates
      w hw K source target shell)

theorem centralLowerExcitedSpinCubeOffRayRootStatePathLength_le_sectorLength
    (w : Q') (hw : (0 : Q') ≤ w) (K state : Nat)
    (hstate : state ∈ centralLowerExcitedSpinCubeOffRayIndices w hw K) :
    centralLowerExcitedSpinCubeOffRayRootStatePathLength w hw K state ≤
      (centralPhysicalFiniteVacuumSectorIndices w hw K 0).length := by
  unfold centralLowerExcitedSpinCubeOffRayRootStatePathLength
  rw [dif_pos hstate]
  unfold centralLowerExcitedSpinCubeOffRayRootPositivePath
  exact centralPhysicalFiniteVacuumSectorSimplePositivePath_edgeLength_le
    w hw K 0 state 0 (List.mem_filter.mp hstate).1
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw K 0)

theorem centralLowerExcitedSpinCubeOffRayRootResistanceEdgeTail_eqv_lengthShellSum
    (w : Q') (hw : (0 : Q') ≤ w) (K source target : Nat) :
    centralLowerExcitedSpinCubeOffRayRootResistanceEdgeTail
        w hw K source target ≈
      listQSum
        (centralLowerExcitedSpinCubeOffRayRootResistanceEdgeLengthShellLoad
          w hw K source target)
        (List.range
          (centralLowerExcitedSpinCubeOffRayRootLengthShellCount w hw K)) := by
  let items := centralLowerExcitedSpinCubeOffRayRootEdgeUsingStates
    w hw K source target
  let value := centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad
    w hw K
  let shell := centralLowerExcitedSpinCubeOffRayRootStatePathLength w hw K
  let bound := centralLowerExcitedSpinCubeOffRayRootLengthShellCount w hw K
  have hshellBound : ∀ state, state ∈ items → shell state < bound := by
    intro state hstate
    have hparts :=
      mem_centralLowerExcitedSpinCubeOffRayRootEdgeUsingStates_iff.mp hstate
    have hlength :=
      centralLowerExcitedSpinCubeOffRayRootStatePathLength_le_sectorLength
        w hw K state hparts.1
    unfold shell bound centralLowerExcitedSpinCubeOffRayRootLengthShellCount
    omega
  have hpartition :=
    listQSum_shell_partition value shell items bound hshellBound
  unfold centralLowerExcitedSpinCubeOffRayRootResistanceEdgeTail
    centralLowerExcitedSpinCubeOffRayRootResistanceEdgeLengthShellLoad
    centralLowerExcitedSpinCubeOffRayRootEdgeLengthShellStates
  exact Q'.eqv_symm hpartition

/-! ## 3. The named geometric shell producer and its compiler -/

/-- A genuine edge-local, path-length-shell estimate.  Unlike a free scalar
sequence, `shellLoad_le` is pinned to the literal BF4 off-ray state carrier,
canonical positive paths, stationary weights, and path resistances. -/
structure FixedNomeCofinalSpinCubeOffRayRootResistanceLengthShellBound
    {w : Q'} (hw : (0 : Q') < w) : Type 1 where
  start : Nat
  amplitude : Q'
  ratio : Q'
  budget : Q'
  amplitude_nonnegative : (0 : Q') ≤ amplitude
  ratio_nonnegative : (0 : Q') ≤ ratio
  ratio_lt_one : ratio < (1 : Q')
  budget_nonnegative : (0 : Q') ≤ budget
  geometric_step : amplitude + ratio * budget ≤ budget
  shellLoad_le : ∀ K, start ≤ K → ∀ source target (shell : Nat),
    shell < centralLowerExcitedSpinCubeOffRayRootLengthShellCount
      w (Q'.le_of_lt hw) K →
    centralLowerExcitedSpinCubeOffRayRootResistanceEdgeLengthShellLoad
        w (Q'.le_of_lt hw) K source target shell ≤
      amplitude * ratio ^ shell

namespace FixedNomeCofinalSpinCubeOffRayRootResistanceLengthShellBound

theorem flowLoad_le_budget
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalSpinCubeOffRayRootResistanceLengthShellBound hw)
    (K : Nat) (hK : family.start ≤ K) (source target : Nat) :
    centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad
        w (Q'.le_of_lt hw) K source target ≤ family.budget := by
  let count := centralLowerExcitedSpinCubeOffRayRootLengthShellCount
    w (Q'.le_of_lt hw) K
  let shellLoad :=
    centralLowerExcitedSpinCubeOffRayRootResistanceEdgeLengthShellLoad
      w (Q'.le_of_lt hw) K source target
  let geometric : Nat → Q' := fun shell =>
    family.amplitude * family.ratio ^ shell
  have hflow :=
    centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad_eqv_edgeTail
      w (Q'.le_of_lt hw) K source target
  have hpartition :=
    centralLowerExcitedSpinCubeOffRayRootResistanceEdgeTail_eqv_lengthShellSum
      w (Q'.le_of_lt hw) K source target
  have hshell : listQSum shellLoad (List.range count) ≤
      listQSum geometric (List.range count) := by
    apply listQSum_mono
    intro shell hshell
    exact family.shellLoad_le K hK source target shell
      (List.mem_range.mp hshell)
  have hgeometric : listQSum geometric (List.range count) ≈
      finSum geometric count :=
    listQSum_range_eqv_finSum geometric count
  have hbudget : finSum geometric count ≤ family.budget :=
    geometric_tail_closure family.amplitude family.ratio family.budget
      family.ratio_nonnegative family.budget_nonnegative
      family.geometric_step count
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hflow hpartition))
    (Q'.le_trans' _ _ _ hshell
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hgeometric) hbudget))

def toResistanceCongestionBound
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalSpinCubeOffRayRootResistanceLengthShellBound hw) :
    FixedNomeCofinalSpinCubeOffRayRootResistanceCongestionBound hw where
  start := family.start
  bound := family.budget
  bound_nonnegative := family.budget_nonnegative
  flowLoad_le := family.flowLoad_le_budget

/-- Combining the concrete geometric off-ray shell estimate with any cofinal
ray capacity yields the exact full-sector simple-routing certificate. -/
def toSimpleRootResistanceCongestionBound
    {w : Q'} {hw : (0 : Q') < w}
    (family :
      FixedNomeCofinalSpinCubeOffRayRootResistanceLengthShellBound hw)
    (ray : FixedNomeCofinalSpinCubeRayCapacity hw) :
    FixedNomeCofinalVacuumSectorMassExactSimpleRootResistanceCongestionBound
      hw :=
  fixedNomeCofinalSimpleRootResistanceCongestionBound_of_ray_offRay
    ray family.toResistanceCongestionBound

end FixedNomeCofinalSpinCubeOffRayRootResistanceLengthShellBound

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceLengthShell

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceLengthShell.centralLowerExcitedSpinCubeOffRayRootStatePathLength_le_sectorLength
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceLengthShell.centralLowerExcitedSpinCubeOffRayRootResistanceEdgeTail_eqv_lengthShellSum
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceLengthShell.FixedNomeCofinalSpinCubeOffRayRootResistanceLengthShellBound.flowLoad_le_budget
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceLengthShell.FixedNomeCofinalSpinCubeOffRayRootResistanceLengthShellBound.toResistanceCongestionBound
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceLengthShell.FixedNomeCofinalSpinCubeOffRayRootResistanceLengthShellBound.toSimpleRootResistanceCongestionBound
