/-
# Global geometric decay of the paired-support connected residue

The terminal/mass partition reduces the complete connected residue to one
finite geometric series at the exact global rate `16/25`.  This module sums
that series.  At observable separation `d`, the result is

  connectedWeight <= (25/9) * (16/25)^(d+1) * partition^2.

Equivalently, the literal normalized two-replica connected residue obeys the
same dimensionless bound.  The estimate is independent of the cutoff and
finite slab volume in its displayed coefficient and rate, but it remains a
theorem at the fixed production coupling `1/400`; no continuum or all-beta
claim is made.

Constructive contract: exact finite geometric summation and positive rational
normalization only.  No `Classical.*`, choice, `native_decide`, `sorry`, custom
axiom, noncomputable declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalPartition

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalDecay

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CharacterTail
open YMGap.Constructive.RationalTail
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalPartition
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalWeight
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Finite shifted geometric series at rate `16/25` -/

private theorem listQSum_range_eqv_finSum (value : Nat → Q') :
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

private theorem listQSum_range_floor_eqv_shifted_finSum
    (value : Nat → Q') (floor : Nat) : ∀ count : Nat,
    listQSum
        (fun index => if floor ≤ index then value index else 0)
        (List.range count) ≈
      finSum (fun offset => value (floor + offset)) (count - floor)
  | 0 => by
      rw [Nat.zero_sub, finSum_zero]
      exact Q'.eqv_refl 0
  | count + 1 => by
      let killed : Nat → Q' := fun index =>
        if floor ≤ index then value index else 0
      have happend :
          listQSum killed (List.range (count + 1)) ≈
            listQSum killed (List.range count) + killed count := by
        rw [List.range_succ]
        exact Q'.eqv_trans _ _ _
          (listQSum_append killed (List.range count) [count])
          (Q'.add_eqv_congr' (Q'.eqv_refl _)
            (Q'.eqv_of_eq (Q'.add_zero' (killed count))))
      refine Q'.eqv_trans _ _ _ happend ?_
      by_cases hfloor : floor ≤ count
      · have hsub : count + 1 - floor = (count - floor) + 1 := by
          omega
        rw [hsub, finSum_succ]
        refine Q'.add_eqv_congr'
          (listQSum_range_floor_eqv_shifted_finSum
            value floor count) ?_
        unfold killed
        rw [if_pos hfloor]
        have hindex : floor + (count - floor) = count := by omega
        rw [hindex]
        exact Q'.eqv_refl _
      · have hsubLeft : count - floor = 0 := by omega
        have hsubRight : count + 1 - floor = 0 := by omega
        rw [hsubRight, finSum_zero]
        unfold killed
        rw [if_neg hfloor]
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr'
            (listQSum_range_floor_eqv_shifted_finSum
              value floor count)
            (Q'.eqv_refl 0)) ?_
        rw [hsubLeft, finSum_zero]
        exact Q'.eqv_of_eq (Q'.add_zero' 0)

private theorem listQSum_filter_eqv_killed
    {A : Type} (value : A → Q') (test : A → Bool) : ∀ items,
    listQSum value (items.filter test) ≈
      listQSum (fun item => if test item then value item else 0) items
  | [] => Q'.eqv_refl 0
  | head :: tail => by
      cases htest : test head with
      | false =>
          simp only [List.filter_cons, htest, Bool.false_eq_true,
            if_false, listQSum]
          exact Q'.eqv_trans _
            (listQSum
              (fun item => if test item then value item else 0) tail) _
            (listQSum_filter_eqv_killed value test tail)
            (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _)))
      | true =>
          simp only [List.filter_cons, htest, if_true, listQSum]
          exact Q'.add_eqv_congr' (Q'.eqv_refl _)
            (listQSum_filter_eqv_killed value test tail)

/-- Every finite initial geometric sum at rate `16/25` is at most
`25/9 = 1/(1-16/25)`. -/
theorem slabObservablePairedGlobalEntropyAnchorRatio_fullTail_le
    (count : Nat) :
    listQSum
        (fun index => slabObservablePairedGlobalEntropyAnchorRatio ^ index)
        (List.range count) ≤ Q'.mkPos 25 9 (by decide) := by
  have hfinite : finSum
      (fun index => slabObservablePairedGlobalEntropyAnchorRatio ^ index)
      count ≤ Q'.mkPos 25 9 (by decide) := by
    apply geom_series_le
      (fun index => slabObservablePairedGlobalEntropyAnchorRatio ^ index)
      1 slabObservablePairedGlobalEntropyAnchorRatio
      (Q'.mkPos 25 9 (by decide))
    · decide
    · decide
    · rw [Q'.pow_zero]
      exact Q'.le_refl' 1
    · intro index
      rw [show index + 1 = index + 1 by rfl, Q'.pow_succ]
      exact Q'.le_refl' _
    · decide
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (listQSum_range_eqv_finSum
        (fun index =>
          slabObservablePairedGlobalEntropyAnchorRatio ^ index)
        count))
    hfinite

/-- The finite tail beginning at `floor` is bounded by the exact shifted
geometric envelope. -/
theorem slabObservablePairedGlobalEntropyAnchorRatio_shiftedTail_le
    (floor count : Nat) :
    listQSum
        (fun index =>
          if floor ≤ index then
            slabObservablePairedGlobalEntropyAnchorRatio ^ index
          else 0)
        (List.range count) ≤
      Q'.mkPos 25 9 (by decide) *
        slabObservablePairedGlobalEntropyAnchorRatio ^ floor := by
  let shiftedCount := count - floor
  have hshift := listQSum_range_floor_eqv_shifted_finSum
    (fun index => slabObservablePairedGlobalEntropyAnchorRatio ^ index)
    floor count
  have hback := Q'.eqv_symm
    (listQSum_range_eqv_finSum
      (fun offset =>
        slabObservablePairedGlobalEntropyAnchorRatio ^ (floor + offset))
      shiftedCount)
  have hsplit :
      listQSum
          (fun offset =>
            slabObservablePairedGlobalEntropyAnchorRatio ^
              (floor + offset))
          (List.range shiftedCount) ≈
        listQSum
          (fun offset =>
            slabObservablePairedGlobalEntropyAnchorRatio ^ floor *
              slabObservablePairedGlobalEntropyAnchorRatio ^ offset)
          (List.range shiftedCount) := by
    apply listQSum_congr
    intro offset
    exact Q'.pow_add_eqv
      slabObservablePairedGlobalEntropyAnchorRatio floor offset
  have hfactor := listQSum_mul_left
    (slabObservablePairedGlobalEntropyAnchorRatio ^ floor)
    (fun offset => slabObservablePairedGlobalEntropyAnchorRatio ^ offset)
    (List.range shiftedCount)
  have hbase :=
    slabObservablePairedGlobalEntropyAnchorRatio_fullTail_le shiftedCount
  have hscaled :
      slabObservablePairedGlobalEntropyAnchorRatio ^ floor *
          listQSum
            (fun offset =>
              slabObservablePairedGlobalEntropyAnchorRatio ^ offset)
            (List.range shiftedCount) ≤
        slabObservablePairedGlobalEntropyAnchorRatio ^ floor *
          Q'.mkPos 25 9 (by decide) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hbase
      (Q'.pow_nonneg slabObservablePairedGlobalEntropyAnchorRatio
        (by decide) floor)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _ hshift
        (Q'.eqv_trans _ _ _ hback
          (Q'.eqv_trans _ _ _ hsplit hfactor))))
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv
        (Q'.mul_comm_eqv
          (slabObservablePairedGlobalEntropyAnchorRatio ^ floor)
          (Q'.mkPos 25 9 (by decide)))))

/-- The actual filtered paid-mass carrier obeys the same shifted tail. -/
theorem slabObservablePairedSupportPaidMasses_weight_le
    (D : SlabPhysicalData) (floor : Nat) :
    listQSum
        (fun mass => slabObservablePairedGlobalEntropyAnchorRatio ^ mass)
        (slabObservablePairedSupportPaidMasses D floor) ≤
      Q'.mkPos 25 9 (by decide) *
        slabObservablePairedGlobalEntropyAnchorRatio ^ floor := by
  unfold slabObservablePairedSupportPaidMasses
  have hfilter := listQSum_filter_eqv_killed
    (fun mass => slabObservablePairedGlobalEntropyAnchorRatio ^ mass)
    (fun mass => decide (floor ≤ mass))
    (List.range (2 * slabObservableRemovalMaxSize D + 1))
  have hconvert :
      listQSum
          (fun mass =>
            if decide (floor ≤ mass) then
              slabObservablePairedGlobalEntropyAnchorRatio ^ mass
            else 0)
          (List.range (2 * slabObservableRemovalMaxSize D + 1)) ≈
        listQSum
          (fun mass =>
            if floor ≤ mass then
              slabObservablePairedGlobalEntropyAnchorRatio ^ mass
            else 0)
          (List.range (2 * slabObservableRemovalMaxSize D + 1)) := by
    apply listQSum_congr
    intro mass
    by_cases hfloor : floor ≤ mass
    · simp only [hfloor, decide_true, if_true]
      exact Q'.eqv_refl _
    · simp only [hfloor, decide_false, if_false]
      exact Q'.eqv_refl 0
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hfilter hconvert))
    (slabObservablePairedGlobalEntropyAnchorRatio_shiftedTail_le
      floor (2 * slabObservableRemovalMaxSize D + 1))

/-! ## 2. Global connected-residue decay -/

/-- Explicit dimensionless decay envelope for the full paired-support
connected residue. -/
def slabObservablePairedSupportGlobalAnchorRate
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) : Q' :=
  Q'.mkPos 25 9 (by decide) *
    slabObservablePairedGlobalEntropyAnchorRatio ^
      (linfDist
        (slabPlaquetteAt D.extent rootFaceId)
        (slabPlaquetteAt D.extent targetFaceId) + 1)

/-- The complete unnormalized paired-support connected residue is bounded by
the global geometric rate times the exact two-replica partition. -/
theorem slabObservablePairedSupportConnectedFourCellSourcePairs_weight_le_partitionSquare
    (cutoff half rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈
      slabPhysicalFaceEdges (anchorSlabPhysicalData cutoff half).extent) :
    let D := anchorSlabPhysicalData cutoff half
    listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservablePairedSupportConnectedFourCellSourcePairs
          D rootFaceId targetFaceId) ≤
      slabObservablePairedSupportGlobalAnchorRate
          D rootFaceId targetFaceId *
        (D.physicalPartition * D.physicalPartition) := by
  let D := anchorSlabPhysicalData cutoff half
  let floor := linfDist
    (slabPlaquetteAt D.extent rootFaceId)
    (slabPlaquetteAt D.extent targetFaceId) + 1
  have hpartition :=
    slabObservablePairedSupportConnectedFourCellSourcePairs_weight_le_massSum
      cutoff half rootFaceId targetFaceId htarget
  have hmass := slabObservablePairedSupportPaidMasses_weight_le D floor
  have hpartitionNonnegative :
      (0 : Q') ≤ D.physicalPartition * D.physicalPartition :=
    Q'.mul_nonneg _ _
      (Q'.le_of_lt (slabParametricKPhysicalPartition_pos
        D.coupling_nonnegative D.cutoff D.extent))
      (Q'.le_of_lt (slabParametricKPhysicalPartition_pos
        D.coupling_nonnegative D.cutoff D.extent))
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _
    (D.physicalPartition * D.physicalPartition)
    hmass hpartitionNonnegative
  exact Q'.le_trans' _ _ _ hpartition hscaled

/-- Normalized mass of the literal two-replica paired-support connected
residue. -/
def slabObservablePairedSupportConnectedMass
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) : Q' :=
  Q'.divPos
    (listQSum (slabObservableTwoReplicaPairWeight D)
      (slabObservablePairedSupportConnectedFourCellSourcePairs
        D rootFaceId targetFaceId))
    (D.physicalPartition * D.physicalPartition)
    (YMGap.Continuum.HKPos.q_mul_pos
      (slabParametricKPhysicalPartition_pos
        D.coupling_nonnegative D.cutoff D.extent)
      (slabParametricKPhysicalPartition_pos
        D.coupling_nonnegative D.cutoff D.extent))

/-- **Finite global paired connected decay.**  The normalized two-replica
residue has the cutoff- and volume-independent displayed rate. -/
theorem slabObservablePairedSupportConnectedMass_le_anchorRate
    (cutoff half rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈
      slabPhysicalFaceEdges (anchorSlabPhysicalData cutoff half).extent) :
    slabObservablePairedSupportConnectedMass
        (anchorSlabPhysicalData cutoff half)
        rootFaceId targetFaceId ≤
      slabObservablePairedSupportGlobalAnchorRate
        (anchorSlabPhysicalData cutoff half)
        rootFaceId targetFaceId := by
  unfold slabObservablePairedSupportConnectedMass
  apply Q'.divPos_le_of_le_mul
  exact
    slabObservablePairedSupportConnectedFourCellSourcePairs_weight_le_partitionSquare
      cutoff half rootFaceId targetFaceId htarget

#print axioms slabObservablePairedGlobalEntropyAnchorRatio_fullTail_le
#print axioms slabObservablePairedGlobalEntropyAnchorRatio_shiftedTail_le
#print axioms slabObservablePairedSupportPaidMasses_weight_le
#print axioms slabObservablePairedSupportGlobalAnchorRate
#print axioms slabObservablePairedSupportConnectedFourCellSourcePairs_weight_le_partitionSquare
#print axioms slabObservablePairedSupportConnectedMass
#print axioms slabObservablePairedSupportConnectedMass_le_anchorRate

end YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalDecay
