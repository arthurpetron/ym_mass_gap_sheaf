/-
# Uniform local root-flow load of the explicit spin-cube ray

Every excited spin cube uses a different literal one-edge vacuum spoke under
the direct-ray routing.  This module records the doubled root-resistance
demand as a finite weighted occurrence list.  Its directed edge keys are
duplicate-free, so the load on any fixed edge is bounded by the largest one
spoke demand rather than by the number of spins.

At the concrete strong-coupling anchor, the existing return floor therefore
bounds the complete ray contribution on every directed edge by the same
cutoff-independent reciprocal-delta constant.  This says nothing yet about
the off-ray traffic or the resistance of its preceding edges.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayFiber
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMoment

namespace YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayRootFlow

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralSpinCubeUniformRayCapacity
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorResistanceCauchy
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceFlow
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMoment
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceEdgeTail
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceFlow
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceSimpleRouting
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeDemand
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayRouting
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem rangeNodupLocal :
    ∀ bound : Nat, (List.range bound).Nodup
  | 0 => List.nodup_nil
  | bound + 1 => by
      rw [List.range_succ]
      apply List.nodup_append.mpr
      refine ⟨rangeNodupLocal bound,
        List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro left hleft right hright heq
      have hrightEq : right = bound := List.mem_singleton.mp hright
      rw [heq, hrightEq] at hleft
      exact absurd (List.mem_range.mp hleft) (Nat.lt_irrefl bound)

private theorem listQSumPerm_local {Item : Type} (value : Item → Q') :
    ∀ {left right : List Item}, left.Perm right →
      listQSum value left ≈ listQSum value right
  | _, _, List.Perm.nil => Q'.eqv_refl 0
  | _, _, List.Perm.cons _ hperm =>
      Q'.add_eqv_congr_left _ _ _ (listQSumPerm_local value hperm)
  | _, _, List.Perm.swap first second rest => by
      change value second + (value first + listQSum value rest) ≈
        value first + (value second + listQSum value rest)
      refine Q'.eqv_trans _
        ((value second + value first) + listQSum value rest) _
        (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _
        ((value first + value second) + listQSum value rest) _
        (Q'.add_eqv_congr_right _ _ _
          (Q'.add_comm_eqv _ _)) ?_
      exact Q'.add_assoc_eqv _ _ _
  | _, _, List.Perm.trans hleft hright =>
      Q'.eqv_trans _ _ _
        (listQSumPerm_local value hleft)
        (listQSumPerm_local value hright)

/-! ## 1. A generic duplicate-free weighted-edge bound -/

private theorem weightedDirectedEdgeLoad_eqv_zero_of_not_mem_keys
    {State : Type} [DecidableEq State] :
    ∀ (occurrences : List (WeightedDirectedEdgeOccurrence State))
      (source target : State),
      (source, target) ∉ occurrences.map (fun occurrence => occurrence.1) →
        weightedDirectedEdgeLoad occurrences source target ≈ 0
  | [], _, _, _ => Q'.eqv_refl 0
  | occurrence :: tail, source, target, hnot => by
      have hhead : occurrence.1 ≠ (source, target) := by
        intro heq
        apply hnot
        exact List.mem_cons.mpr (Or.inl heq.symm)
      have htail : (source, target) ∉
          tail.map (fun item => item.1) := by
        intro hmem
        apply hnot
        exact List.mem_cons_of_mem occurrence.1 hmem
      unfold weightedDirectedEdgeLoad listQSum
      unfold weightedDirectedEdgeIndicator
      rw [if_neg hhead]
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left 0 _ _
          (weightedDirectedEdgeLoad_eqv_zero_of_not_mem_keys
            tail source target htail))
        (Q'.eqv_of_eq (Q'.zero_add' 0))

private theorem weightedDirectedEdgeLoad_le_of_keys_nodup
    {State : Type} [DecidableEq State]
    (bound : Q') (hbound0 : (0 : Q') ≤ bound) :
    ∀ (occurrences : List (WeightedDirectedEdgeOccurrence State)),
      (occurrences.map (fun occurrence => occurrence.1)).Nodup →
      (∀ occurrence, occurrence ∈ occurrences →
        (0 : Q') ≤ occurrence.2 ∧ occurrence.2 ≤ bound) →
      ∀ source target,
        weightedDirectedEdgeLoad occurrences source target ≤ bound
  | [], _, _, _, _ => hbound0
  | occurrence :: tail, hnodup, hloads, source, target => by
      have hparts := List.nodup_cons.mp hnodup
      by_cases hhead : occurrence.1 = (source, target)
      · have hnotTail : (source, target) ∉
            tail.map (fun item => item.1) := by
          intro hmem
          apply hparts.1
          simpa only [hhead] using hmem
        have htailZero :=
          weightedDirectedEdgeLoad_eqv_zero_of_not_mem_keys
            tail source target hnotTail
        have hheadBound := (hloads occurrence List.mem_cons_self).2
        unfold weightedDirectedEdgeLoad listQSum
        unfold weightedDirectedEdgeIndicator
        rw [if_pos hhead]
        exact Q'.le_trans' _ occurrence.2 _
          (Q'.le_of_eqv
            (Q'.eqv_trans _ (occurrence.2 + 0) _
              (Q'.add_eqv_congr_left occurrence.2 _ _ htailZero)
              (Q'.eqv_of_eq (Q'.add_zero' occurrence.2))))
          hheadBound
      · unfold weightedDirectedEdgeLoad listQSum
        unfold weightedDirectedEdgeIndicator
        rw [if_neg hhead]
        exact Q'.le_trans' _
          (weightedDirectedEdgeLoad tail source target) _
          (Q'.le_of_eqv (Q'.eqv_of_eq
            (Q'.zero_add' (weightedDirectedEdgeLoad tail source target))))
          (weightedDirectedEdgeLoad_le_of_keys_nodup
            bound hbound0 tail hparts.2
            (fun item hitem =>
              hloads item (List.mem_cons_of_mem occurrence hitem))
            source target)

private theorem weightedDirectedEdgeIndicator_eqv_of_load_eqv
    {State : Type} [DecidableEq State]
    (edge : State × State) (left right : Q')
    (source target : State) (hload : left ≈ right) :
    weightedDirectedEdgeIndicator (edge, left) source target ≈
      weightedDirectedEdgeIndicator (edge, right) source target := by
  unfold weightedDirectedEdgeIndicator
  by_cases hedge : edge = (source, target)
  · rw [if_pos hedge, if_pos hedge]
    exact hload
  · rw [if_neg hedge, if_neg hedge]
    exact Q'.eqv_refl 0

private theorem weightedDirectedEdgeLoad_constantMap_add_eqv_add
    {State : Type} [DecidableEq State]
    (edges : List (State × State)) (left right : Q')
    (source target : State) :
    weightedDirectedEdgeLoad
        (edges.map (fun edge => (edge, left + right))) source target ≈
      weightedDirectedEdgeLoad
          (edges.map (fun edge => (edge, left))) source target +
        weightedDirectedEdgeLoad
          (edges.map (fun edge => (edge, right))) source target := by
  unfold weightedDirectedEdgeLoad
  rw [listQSum_map, listQSum_map, listQSum_map]
  refine Q'.eqv_trans _
    (listQSum
      (fun edge =>
        weightedDirectedEdgeIndicator (edge, left) source target +
          weightedDirectedEdgeIndicator (edge, right) source target)
      edges) _ ?_ ?_
  · apply listQSum_congr
    intro edge
    unfold weightedDirectedEdgeIndicator
    by_cases hedge : edge = (source, target)
    · rw [if_pos hedge, if_pos hedge, if_pos hedge]
      exact Q'.eqv_refl _
    · rw [if_neg hedge, if_neg hedge, if_neg hedge]
      exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' 0))
  · exact listQSum_add _ _ edges

/-! ## 2. Literal direct-ray root occurrences -/

def centralLowerExcitedSpinCubeDirectRootResistanceDemandAt
    {w : Q'} (hw : (0 : Q') < w) (K offset : Nat) : Q' :=
  if hoffset : offset < K then
    centralLowerExcitedSpinCubeDirectRootResistanceDemand hw hoffset
  else 0

def centralLowerExcitedSpinCubeDirectRootResistanceOccurrences
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) :
    List (WeightedDirectedEdgeOccurrence Nat) :=
  (List.range K).map (fun offset =>
    ((centralLowerExcitedSpinCubeIndex
        w (Q'.le_of_lt hw) K offset, 0),
      centralLowerExcitedSpinCubeDirectRootResistanceDemandAt hw K offset))

def centralLowerExcitedSpinCubeDirectRootResistanceFlowLoad
    {w : Q'} (hw : (0 : Q') < w) (K source target : Nat) : Q' :=
  weightedDirectedEdgeLoad
    (centralLowerExcitedSpinCubeDirectRootResistanceOccurrences hw K)
    source target

theorem centralLowerExcitedSpinCubeDirectRootResistanceOccurrenceKeys_nodup
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) :
    ((centralLowerExcitedSpinCubeDirectRootResistanceOccurrences hw K).map
      (fun occurrence => occurrence.1)).Nodup := by
  unfold centralLowerExcitedSpinCubeDirectRootResistanceOccurrences
  rw [List.map_map]
  apply nodup_map_of_injOn
  · exact rangeNodupLocal K
  · intro left hleft right hright heq
    have hindex : centralLowerExcitedSpinCubeIndex
        w (Q'.le_of_lt hw) K left =
      centralLowerExcitedSpinCubeIndex
        w (Q'.le_of_lt hw) K right := congrArg Prod.fst heq
    exact centralLowerExcitedSpinCubeIndex_injective_on hw
      (List.mem_range.mp hleft) (List.mem_range.mp hright) hindex

theorem centralLowerExcitedSpinCubeDirectRootResistanceDemandAt_nonnegative
    {w : Q'} (hw : (0 : Q') < w) (K offset : Nat) :
    (0 : Q') ≤
      centralLowerExcitedSpinCubeDirectRootResistanceDemandAt hw K offset := by
  unfold centralLowerExcitedSpinCubeDirectRootResistanceDemandAt
  by_cases hoffset : offset < K
  · rw [dif_pos hoffset]
    unfold centralLowerExcitedSpinCubeDirectRootResistanceDemand
    exact Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _
        (Q'.le_of_lt
          (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
            (centralLowerExcitedSpinCubeIndices_subset_vacuumSector hw K _
              (List.mem_map.mpr
                ⟨offset, List.mem_range.mpr hoffset, rfl⟩))))
        (Q'.le_of_lt (Q'.recipPos_pos _ _)))
      (Q'.mul_nonneg _ _
        (Q'.le_of_lt
          (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
            (centralLowerExcitedSpinCubeIndices_subset_vacuumSector hw K _
              (List.mem_map.mpr
                ⟨offset, List.mem_range.mpr hoffset, rfl⟩))))
        (Q'.le_of_lt (Q'.recipPos_pos _ _)))
  · rw [dif_neg hoffset]
    exact Q'.le_refl' 0

/-! ## 3. Identification with the routed ray-state load -/

theorem centralLowerExcitedSpinCubeIndex_routedRootResistanceStateEdgeLoad_eqv_indicator
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hoffset : offset < K) (source target : Nat) :
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad
        (centralLowerExcitedSpinCubeRayDirectRootRoutingAt hw K)
        (centralLowerExcitedSpinCubeIndex
          w (Q'.le_of_lt hw) K offset)
        source target ≈
      weightedDirectedEdgeIndicator
        ((centralLowerExcitedSpinCubeIndex
            w (Q'.le_of_lt hw) K offset, 0),
          centralLowerExcitedSpinCubeDirectRootResistanceDemand hw hoffset)
        source target := by
  let index := centralLowerExcitedSpinCubeIndex
    w (Q'.le_of_lt hw) K offset
  let hindex := centralLowerExcitedSpinCubeIndices_subset_vacuumSector
    hw K index
      (List.mem_map.mpr
        ⟨offset, List.mem_range.mpr hoffset, rfl⟩)
  let spoke := centralLowerSpinCubeToVacuumSpoke hw
    (show offset + 1 ≤ K by omega)
  let weight := centralPhysicalFiniteWeight w (Q'.le_of_lt hw) K 0 index
  let actualSingle := weight * PositiveKernelChainIn.resistance spoke
  let directSingle := weight *
    Q'.recipPos
      (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0 index 0)
      (centralPhysicalFiniteKernel_spinCubeIndex_zero_pos hw (by omega))
  have hsingle : actualSingle ≈ directSingle := by
    unfold actualSingle directSingle
    exact Q'.mul_eqv_congr_left weight _ _
      (centralLowerExcitedSpinCubeToVacuumSpoke_resistance_eqv_reciprocal
        hw hoffset)
  have hdoubled : actualSingle + actualSingle ≈
      directSingle + directSingle :=
    Q'.add_eqv_congr' hsingle hsingle
  unfold centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceWeightedPathOccurrences
  rw [dif_pos hindex]
  rw [centralLowerExcitedSpinCubeRayDirectRootRoutingAt_path_ray_eq
    hw hoffset]
  change weightedDirectedEdgeLoad
      [((index, 0), actualSingle + actualSingle)] source target ≈
    weightedDirectedEdgeIndicator
      ((index, 0), directSingle + directSingle) source target
  unfold weightedDirectedEdgeLoad listQSum
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_of_eq
      (Q'.add_zero'
        (weightedDirectedEdgeIndicator
          ((index, 0), actualSingle + actualSingle) source target)))
    (weightedDirectedEdgeIndicator_eqv_of_load_eqv
      (index, 0) (actualSingle + actualSingle)
      (directSingle + directSingle) source target hdoubled)

theorem centralLowerExcitedSpinCubeDirectRootResistanceFlowLoad_eqv_routedRayStateEdgeLoadSum
    {w : Q'} (hw : (0 : Q') < w) (K source target : Nat) :
    centralLowerExcitedSpinCubeDirectRootResistanceFlowLoad
        hw K source target ≈
      listQSum
        (fun state =>
          centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad
            (centralLowerExcitedSpinCubeRayDirectRootRoutingAt hw K)
            state source target)
        (centralLowerExcitedSpinCubeIndices
          w (Q'.le_of_lt hw) K) := by
  unfold centralLowerExcitedSpinCubeDirectRootResistanceFlowLoad
    centralLowerExcitedSpinCubeDirectRootResistanceOccurrences
    centralLowerExcitedSpinCubeIndices weightedDirectedEdgeLoad
  rw [listQSum_map, listQSum_map]
  apply listQSum_congr_on
  intro offset hoffsetMem
  have hoffset : offset < K := List.mem_range.mp hoffsetMem
  unfold centralLowerExcitedSpinCubeDirectRootResistanceDemandAt
  rw [dif_pos hoffset]
  exact Q'.eqv_symm
    (centralLowerExcitedSpinCubeIndex_routedRootResistanceStateEdgeLoad_eqv_indicator
      hw hoffset source target)

/-! ## 4. Uniform anchor load on every directed edge -/

theorem anchorDirectRootResistanceDemandAt_le_uniformBound
    (K offset : Nat) :
    centralLowerExcitedSpinCubeDirectRootResistanceDemandAt
        (w := anchorCoupling) (by decide) K offset ≤
      Q'.divPos 1 anchorCentralSpinCubeCofinalRayCapacity.delta
        anchorCentralSpinCubeCofinalRayCapacity.delta_pos := by
  unfold centralLowerExcitedSpinCubeDirectRootResistanceDemandAt
  by_cases hoffset : offset < K
  · rw [dif_pos hoffset]
    exact anchorDirectRootResistanceDemand_le_uniformBound hoffset
  · rw [dif_neg hoffset]
    exact Q'.le_of_lt
      (Q'.divPos_pos 1 anchorCentralSpinCubeCofinalRayCapacity.delta
        anchorCentralSpinCubeCofinalRayCapacity.delta_pos (by decide))

theorem anchorDirectRootResistanceFlowLoad_le_uniformBound
    (K source target : Nat) :
    centralLowerExcitedSpinCubeDirectRootResistanceFlowLoad
        (w := anchorCoupling) (by decide) K source target ≤
      Q'.divPos 1 anchorCentralSpinCubeCofinalRayCapacity.delta
        anchorCentralSpinCubeCofinalRayCapacity.delta_pos := by
  unfold centralLowerExcitedSpinCubeDirectRootResistanceFlowLoad
  apply weightedDirectedEdgeLoad_le_of_keys_nodup
  · exact Q'.le_of_lt
      (Q'.divPos_pos 1 anchorCentralSpinCubeCofinalRayCapacity.delta
        anchorCentralSpinCubeCofinalRayCapacity.delta_pos (by decide))
  · exact centralLowerExcitedSpinCubeDirectRootResistanceOccurrenceKeys_nodup
      (w := anchorCoupling) (by decide) K
  · intro occurrence hoccurrence
    obtain ⟨offset, hoffset, rfl⟩ := List.mem_map.mp hoccurrence
    exact ⟨
      centralLowerExcitedSpinCubeDirectRootResistanceDemandAt_nonnegative
        (w := anchorCoupling) (by decide) K offset,
      anchorDirectRootResistanceDemandAt_le_uniformBound K offset⟩

theorem anchorRoutedDirectRayStateEdgeLoadSum_le_uniformBound
    (K source target : Nat) :
    listQSum
        (fun state =>
          centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad
            (centralLowerExcitedSpinCubeRayDirectRootRoutingAt
              (w := anchorCoupling) (by decide) K)
            state source target)
        (centralLowerExcitedSpinCubeIndices anchorCoupling (by decide) K) ≤
      Q'.divPos 1 anchorCentralSpinCubeCofinalRayCapacity.delta
        anchorCentralSpinCubeCofinalRayCapacity.delta_pos := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (centralLowerExcitedSpinCubeDirectRootResistanceFlowLoad_eqv_routedRayStateEdgeLoadSum
          (w := anchorCoupling) (by decide) K source target)))
    (anchorDirectRootResistanceFlowLoad_le_uniformBound K source target)

/-! ## 5. Exact full-flow split and the remaining off-ray load -/

def centralLowerExcitedSpinCubeDirectRootOffRayResistanceFlowLoad
    {w : Q'} (hw : (0 : Q') < w) (K source target : Nat) : Q' :=
  listQSum
    (fun state =>
      centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad
        (centralLowerExcitedSpinCubeRayDirectRootRoutingAt hw K)
        state source target)
    (centralLowerExcitedSpinCubeOffRayIndices
      w (Q'.le_of_lt hw) K)

theorem centralLowerExcitedSpinCubeDirectRootResistanceFlowLoad_eqv_ray_add_offRay
    {w : Q'} (hw : (0 : Q') < w) (K source target : Nat) :
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad
        (centralLowerExcitedSpinCubeRayDirectRootRoutingAt hw K)
        source target ≈
      centralLowerExcitedSpinCubeDirectRootResistanceFlowLoad
          hw K source target +
        centralLowerExcitedSpinCubeDirectRootOffRayResistanceFlowLoad
          hw K source target := by
  let routing := centralLowerExcitedSpinCubeRayDirectRootRoutingAt hw K
  let value := fun state =>
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad
      routing state source target
  let sector := centralPhysicalFiniteVacuumSectorIndices
    w (Q'.le_of_lt hw) K 0
  let test := centralLowerExcitedSpinCubeRayMembershipTest
    w (Q'.le_of_lt hw) K
  have hfull :=
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad_eqv_stateEdgeLoad_sum
      routing source target
  have hpartition : listQSum value sector ≈
      listQSum value
          (centralLowerExcitedSpinCubeFilteredRayIndices
            w (Q'.le_of_lt hw) K) +
        listQSum value
          (centralLowerExcitedSpinCubeOffRayIndices
            w (Q'.le_of_lt hw) K) := by
    simpa only [sector, test,
      centralLowerExcitedSpinCubeFilteredRayIndices,
      centralLowerExcitedSpinCubeOffRayIndices] using
      (listQSum_filter_partition value test sector)
  have hrayPerm :=
    centralLowerExcitedSpinCubeFilteredRayIndices_perm_rayIndices hw K
  have hrayReindex : listQSum value
        (centralLowerExcitedSpinCubeFilteredRayIndices
          w (Q'.le_of_lt hw) K) ≈
      listQSum value
        (centralLowerExcitedSpinCubeIndices
          w (Q'.le_of_lt hw) K) :=
    listQSumPerm_local value hrayPerm
  have hrayFlow :=
    centralLowerExcitedSpinCubeDirectRootResistanceFlowLoad_eqv_routedRayStateEdgeLoadSum
      hw K source target
  exact Q'.eqv_trans _ _ _ hfull
    (Q'.eqv_trans _ _ _ hpartition
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ hrayReindex (Q'.eqv_symm hrayFlow))
        (Q'.eqv_refl _)))

theorem anchorDirectRootResistanceFlowLoad_le_uniformBound_add_offRay
    (K source target : Nat) :
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad
        (centralLowerExcitedSpinCubeRayDirectRootRoutingAt
          (w := anchorCoupling) (by decide) K)
        source target ≤
      Q'.divPos 1 anchorCentralSpinCubeCofinalRayCapacity.delta
          anchorCentralSpinCubeCofinalRayCapacity.delta_pos +
        centralLowerExcitedSpinCubeDirectRootOffRayResistanceFlowLoad
          (w := anchorCoupling) (by decide) K source target := by
  have hsplit :=
    centralLowerExcitedSpinCubeDirectRootResistanceFlowLoad_eqv_ray_add_offRay
      (w := anchorCoupling) (by decide) K source target
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit)
    (Q'.add_le_add
      (anchorDirectRootResistanceFlowLoad_le_uniformBound K source target)
      (Q'.le_refl'
        (centralLowerExcitedSpinCubeDirectRootOffRayResistanceFlowLoad
          (w := anchorCoupling) (by decide) K source target)))

/-! ## 6. The remainder is exactly the doubled canonical off-ray flow -/

private theorem not_mem_excitedRay_of_mem_offRay
    {w : Q'} (hw : (0 : Q') < w) {K state : Nat}
    (hstate : state ∈ centralLowerExcitedSpinCubeOffRayIndices
      w (Q'.le_of_lt hw) K) :
    state ∉ centralLowerExcitedSpinCubeIndices
      w (Q'.le_of_lt hw) K := by
  have htest := (List.mem_filter.mp hstate).2
  intro hray
  unfold centralLowerExcitedSpinCubeRayMembershipTest at htest
  have hdecide : decide
      (state ∈ centralLowerExcitedSpinCubeIndices
        w (Q'.le_of_lt hw) K) = true := decide_eq_true hray
  rw [hdecide] at htest
  cases htest

theorem centralLowerExcitedSpinCubeRayDirectRootPath_offRay_eq_canonical
    {w : Q'} (hw : (0 : Q') < w) {K state : Nat}
    (hstate : state ∈ centralLowerExcitedSpinCubeOffRayIndices
      w (Q'.le_of_lt hw) K)
    (hsector : state ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (hzero : 0 ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0) :
    centralLowerExcitedSpinCubeRayDirectRootPath
        hw K state 0 hsector hzero =
      centralLowerExcitedSpinCubeOffRayRootPositivePath state hstate := by
  unfold centralLowerExcitedSpinCubeRayDirectRootPath
  rw [dif_pos rfl]
  unfold centralLowerExcitedSpinCubeRayDirectPathToVacuum
  rw [dif_neg (not_mem_excitedRay_of_mem_offRay hw hstate)]
  rfl

def centralLowerExcitedSpinCubeCanonicalOffRayRootResistanceStateEdgeLoad
    (w : Q') (hw : (0 : Q') ≤ w) (K state source target : Nat) : Q' :=
  weightedDirectedEdgeLoad
    (centralLowerExcitedSpinCubeOffRayRootResistanceWeightedPathOccurrences
      w hw K state)
    source target

theorem centralLowerExcitedSpinCubeDirectRootOffRayStateEdgeLoad_eqv_twice_canonical
    {w : Q'} (hw : (0 : Q') < w) {K state : Nat}
    (hstate : state ∈ centralLowerExcitedSpinCubeOffRayIndices
      w (Q'.le_of_lt hw) K)
    (source target : Nat) :
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad
        (centralLowerExcitedSpinCubeRayDirectRootRoutingAt hw K)
        state source target ≈
      centralLowerExcitedSpinCubeCanonicalOffRayRootResistanceStateEdgeLoad
          w (Q'.le_of_lt hw) K state source target +
        centralLowerExcitedSpinCubeCanonicalOffRayRootResistanceStateEdgeLoad
          w (Q'.le_of_lt hw) K state source target := by
  let hsector := (List.mem_filter.mp hstate).1
  let hzero := zero_mem_centralPhysicalFiniteVacuumSectorIndices
    w (Q'.le_of_lt hw) K 0
  let path := centralLowerExcitedSpinCubeOffRayRootPositivePath state hstate
  let singleLoad := centralPhysicalFiniteWeight
    w (Q'.le_of_lt hw) K 0 state * PositiveKernelChainIn.resistance path
  have hpath :
      (centralLowerExcitedSpinCubeRayDirectRootRoutingAt hw K).path
          state 0 hsector hzero = path := by
    exact centralLowerExcitedSpinCubeRayDirectRootPath_offRay_eq_canonical
      hw hstate hsector hzero
  unfold centralPhysicalFiniteVacuumSectorRoutedRootResistanceStateEdgeLoad
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceWeightedPathOccurrences
    centralLowerExcitedSpinCubeCanonicalOffRayRootResistanceStateEdgeLoad
    centralLowerExcitedSpinCubeOffRayRootResistanceWeightedPathOccurrences
  rw [dif_pos hsector, dif_pos hstate]
  rw [hpath]
  exact weightedDirectedEdgeLoad_constantMap_add_eqv_add
    (PositiveKernelChainIn.directedEdges path)
    singleLoad singleLoad source target

theorem centralLowerExcitedSpinCubeDirectRootOffRayResistanceFlowLoad_eqv_twice_canonical
    {w : Q'} (hw : (0 : Q') < w) (K source target : Nat) :
    centralLowerExcitedSpinCubeDirectRootOffRayResistanceFlowLoad
        hw K source target ≈
      centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad
          w (Q'.le_of_lt hw) K source target +
        centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad
          w (Q'.le_of_lt hw) K source target := by
  let offRay := centralLowerExcitedSpinCubeOffRayIndices
    w (Q'.le_of_lt hw) K
  let canonicalValue := fun state =>
    centralLowerExcitedSpinCubeCanonicalOffRayRootResistanceStateEdgeLoad
      w (Q'.le_of_lt hw) K state source target
  have hpointwise :
      centralLowerExcitedSpinCubeDirectRootOffRayResistanceFlowLoad
          hw K source target ≈
        listQSum
          (fun state => canonicalValue state + canonicalValue state)
          offRay := by
    unfold centralLowerExcitedSpinCubeDirectRootOffRayResistanceFlowLoad
    apply listQSum_congr_on
    intro state hstate
    exact
      centralLowerExcitedSpinCubeDirectRootOffRayStateEdgeLoad_eqv_twice_canonical
        hw hstate source target
  have hsplit : listQSum
        (fun state => canonicalValue state + canonicalValue state)
        offRay ≈
      listQSum canonicalValue offRay + listQSum canonicalValue offRay :=
    listQSum_add canonicalValue canonicalValue offRay
  have hcanonical :=
    centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad_eqv_stateLoadSum
      w (Q'.le_of_lt hw) K source target
  exact Q'.eqv_trans _ _ _ hpointwise
    (Q'.eqv_trans _ _ _ hsplit
      (Q'.add_eqv_congr'
        (Q'.eqv_symm hcanonical) (Q'.eqv_symm hcanonical)))

theorem anchorDirectRootResistanceFlowLoad_le_uniformBound_add_twice_canonicalOffRay
    (K source target : Nat) :
    centralPhysicalFiniteVacuumSectorRoutedRootResistanceFlowLoad
        (centralLowerExcitedSpinCubeRayDirectRootRoutingAt
          (w := anchorCoupling) (by decide) K)
        source target ≤
      Q'.divPos 1 anchorCentralSpinCubeCofinalRayCapacity.delta
          anchorCentralSpinCubeCofinalRayCapacity.delta_pos +
        (centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad
            anchorCoupling (by decide) K source target +
          centralLowerExcitedSpinCubeOffRayRootResistanceFlowLoad
            anchorCoupling (by decide) K source target) := by
  have hfirst :=
    anchorDirectRootResistanceFlowLoad_le_uniformBound_add_offRay
      K source target
  have hoffRay :=
    centralLowerExcitedSpinCubeDirectRootOffRayResistanceFlowLoad_eqv_twice_canonical
      (w := anchorCoupling) (by decide) K source target
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.le_of_eqv
      (Q'.add_eqv_congr_left
        (Q'.divPos 1 anchorCentralSpinCubeCofinalRayCapacity.delta
          anchorCentralSpinCubeCofinalRayCapacity.delta_pos)
        _ _ hoffRay))

end YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayRootFlow

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayRootFlow.centralLowerExcitedSpinCubeDirectRootResistanceOccurrenceKeys_nodup
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayRootFlow.centralLowerExcitedSpinCubeDirectRootResistanceDemandAt_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayRootFlow.centralLowerExcitedSpinCubeIndex_routedRootResistanceStateEdgeLoad_eqv_indicator
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayRootFlow.centralLowerExcitedSpinCubeDirectRootResistanceFlowLoad_eqv_routedRayStateEdgeLoadSum
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayRootFlow.anchorDirectRootResistanceDemandAt_le_uniformBound
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayRootFlow.anchorDirectRootResistanceFlowLoad_le_uniformBound
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayRootFlow.anchorRoutedDirectRayStateEdgeLoadSum_le_uniformBound
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayRootFlow.centralLowerExcitedSpinCubeDirectRootResistanceFlowLoad_eqv_ray_add_offRay
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayRootFlow.anchorDirectRootResistanceFlowLoad_le_uniformBound_add_offRay
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayRootFlow.centralLowerExcitedSpinCubeRayDirectRootPath_offRay_eq_canonical
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayRootFlow.centralLowerExcitedSpinCubeDirectRootOffRayStateEdgeLoad_eqv_twice_canonical
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayRootFlow.centralLowerExcitedSpinCubeDirectRootOffRayResistanceFlowLoad_eqv_twice_canonical
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeRayRootFlow.anchorDirectRootResistanceFlowLoad_le_uniformBound_add_twice_canonicalOffRay
