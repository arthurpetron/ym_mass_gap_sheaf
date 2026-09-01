/-
# Aggregate raw mass of the low-spin growing-volume carrier

The reflected low-spin family contains `volume + 1` distinct lower states,
and every selected state has the same volume-independent positive raw-row
floor.  This file sums those pointwise floors constructively and injects the
selected list into the complete lower-state carrier.  Consequently the
corrected-slab physical partition dominates

  `(volume + 1) * (coeffW w 1)^6`.

This is the exact aggregate consequence of the current production theorem.
It also records why an absolute row floor alone is not yet a replication
ratio: the normalising partition is forced to grow by the same selected
family.  A common target/source row comparison remains necessary for a
divergent effective multiplicity, cofinal gap, continuum limit, or Clay
conclusion.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeRawRowFloor
import YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayReplicationGate

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeAggregateRawMass

set_option maxRecDepth 300000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawRowFloor
open YMGap.Continuum.BF4LowSpinGrowingVolumeReflectedCarrier
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayReplicationGate
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_mono_local {A : Type}
    (lower upper : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → lower item ≤ upper item) →
        listQSum lower items ≤ listQSum upper items
  | [], _ => Q'.le_refl' 0
  | first :: rest, hterm =>
      Q'.add_le_add
        (hterm first List.mem_cons_self)
        (listQSum_mono_local lower upper rest
          (fun item hitem =>
            hterm item (List.mem_cons_of_mem first hitem)))

private theorem listQSum_const_local {A : Type} (constant : Q') :
    ∀ items : List A,
      listQSum (fun _item => constant) items ≈
        Q'.ofNat items.length * constant
  | [] => Q'.eqv_symm (Q'.zero_mul_eqv constant)
  | _first :: rest => by
      refine Q'.eqv_trans _
        (constant + Q'.ofNat rest.length * constant) _ ?_ ?_
      · exact Q'.add_eqv_congr_left constant _ _
          (listQSum_const_local constant rest)
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _
        ((Q'.ofNat rest.length + 1) * constant) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ constant
          (Q'.ofNat_add_eqv rest.length 1)
      refine Q'.eqv_trans _
        (Q'.ofNat rest.length * constant + (1 : Q') * constant) _
        (Q'.add_mul_eqv (Q'.ofNat rest.length) 1 constant) ?_
      exact Q'.eqv_trans _
        (Q'.ofNat rest.length * constant + constant) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv constant))
        (Q'.add_comm_eqv
          (Q'.ofNat rest.length * constant) constant)

/-! ## 1. Selected aggregate raw source mass -/

/-- Sum of the complete positive raw rows over the selected low-spin family. -/
def lowSpinCentralSelectedPositiveRawSourceMass
    (w : Q') (hw : (0 : Q') ≤ w) (volume : Nat) : Q' :=
  listQSum
    (centralPhysicalPositiveRawRowMass w hw 1 (volume + 1))
    (lowSpinCentralLowerStates volume)

/-- Summing the common pointwise row floor over the duplicate-free selected
family yields the exact linear cardinality factor. -/
theorem lowSpinCentralCommonFloor_mul_count_le_selectedRawSourceMass
    {w : Q'} (hw : (0 : Q') < w) (volume : Nat) :
    (coeffW w 1) ^ 6 * Q'.ofNat (volume + 1) ≤
      lowSpinCentralSelectedPositiveRawSourceMass
        w (Q'.le_of_lt hw) volume := by
  let floor := (coeffW w 1) ^ 6
  let states := lowSpinCentralLowerStates volume
  let row := centralPhysicalPositiveRawRowMass
    w (Q'.le_of_lt hw) 1 (volume + 1)
  have hfloorSum :
      listQSum (fun _state : EdgeLabelling => floor) states ≤
        listQSum row states := by
    apply listQSum_mono_local
    intro state hstate
    unfold states lowSpinCentralLowerStates at hstate
    obtain ⟨index, _hindex, rfl⟩ := List.mem_map.mp hstate
    exact lowSpinCentralCommonFloor_le_positiveRawRow hw index
  have hconstant :
      floor * Q'.ofNat (volume + 1) ≈
        listQSum (fun _state : EdgeLabelling => floor) states := by
    refine Q'.eqv_trans _
      (Q'.ofNat (volume + 1) * floor) _
      (Q'.mul_comm_eqv floor (Q'.ofNat (volume + 1))) ?_
    exact Q'.eqv_symm (by
      simpa only [states, lowSpinCentralLowerStates_length] using
        (listQSum_const_local floor states))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hconstant)
    (by
      unfold lowSpinCentralSelectedPositiveRawSourceMass
      exact hfloorSum)

/-! ## 2. Injection into the complete source budget -/

/-- The selected raw source mass is part of the complete lower-state raw
source budget. -/
theorem lowSpinCentralSelectedPositiveRawSourceMass_le_full
    (w : Q') (hw : (0 : Q') ≤ w) (volume : Nat) :
    lowSpinCentralSelectedPositiveRawSourceMass w hw volume ≤
      centralPhysicalPositiveRawSourceMass w hw 1 (volume + 1) := by
  unfold lowSpinCentralSelectedPositiveRawSourceMass
    centralPhysicalPositiveRawSourceMass
  apply listQSum_le_of_injective_nodup
    (lowSpinCentralLowerStates volume)
    (centralHalfStates 1 (volume + 1))
    (centralPhysicalPositiveRawRowMass w hw 1 (volume + 1))
    (centralPhysicalPositiveRawRowMass w hw 1 (volume + 1))
    (fun state => state)
  · exact lowSpinCentralLowerStates_nodup volume
  · exact centralHalfStates_nodup 1 (volume + 1)
  · intro state hstate
    exact lowSpinCentralLowerStates_mem hstate
  · intro left _hleft right _hright heq
    exact heq
  · intro state _hstate
    exact Q'.le_refl' _
  · intro state _hstate
    exact centralPhysicalPositiveRawRowMass_nonnegative
      hw 1 (volume + 1) state

/-- The corrected-slab partition must pay the aggregate linear low-spin raw
mass.  This is an honest partition lower bound, not a normalized
effective-multiplicity estimate. -/
theorem lowSpinCentralCommonFloor_mul_count_le_partition
    {w : Q'} (hw : (0 : Q') < w) (volume : Nat) :
    (coeffW w 1) ^ 6 * Q'.ofNat (volume + 1) ≤
      slabParametricKPhysicalPartition
        w 1 (centralExtent (volume + 1)) := by
  exact Q'.le_trans' _ _ _
    (lowSpinCentralCommonFloor_mul_count_le_selectedRawSourceMass
      hw volume)
    (Q'.le_trans' _ _ _
      (lowSpinCentralSelectedPositiveRawSourceMass_le_full
        w (Q'.le_of_lt hw) volume)
      (Q'.le_of_eqv
        (centralPhysicalPositiveRawSourceMass_eqv_partition
          w (Q'.le_of_lt hw) 1 (volume + 1))))

/-! ## 3. The normalized absolute-floor fraction is capped -/

/-- The aggregate absolute floor divided by the physical partition.  This is
the strongest normalized factor obtained from the absolute production floor
without a reference-row comparison. -/
def lowSpinCentralAbsoluteFloorFraction
    (w : Q') (hw : (0 : Q') < w) (volume : Nat) : Q' :=
  Q'.divPos
    ((coeffW w 1) ^ 6 * Q'.ofNat (volume + 1))
    (slabParametricKPhysicalPartition
      w 1 (centralExtent (volume + 1)))
    (slabParametricKPhysicalPartition_pos
      (Q'.le_of_lt hw) 1 (centralExtent (volume + 1)))

/-- Counting the selected rows against only their absolute floor cannot
produce a divergent normalized multiplicity: the same rows force the
partition denominator to dominate the aggregate numerator. -/
theorem lowSpinCentralAbsoluteFloorFraction_le_one
    (w : Q') (hw : (0 : Q') < w) (volume : Nat) :
    lowSpinCentralAbsoluteFloorFraction w hw volume ≤ 1 := by
  unfold lowSpinCentralAbsoluteFloorFraction
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _ _ _
    (lowSpinCentralCommonFloor_mul_count_le_partition hw volume)
    (Q'.ge_of_eqv
      (Q'.one_mul_eqv
        (slabParametricKPhysicalPartition
          w 1 (centralExtent (volume + 1)))))

end YMGap.Continuum.BF4LowSpinGrowingVolumeAggregateRawMass

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeAggregateRawMass.lowSpinCentralCommonFloor_mul_count_le_selectedRawSourceMass
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeAggregateRawMass.lowSpinCentralSelectedPositiveRawSourceMass_le_full
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeAggregateRawMass.lowSpinCentralCommonFloor_mul_count_le_partition
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeAggregateRawMass.lowSpinCentralAbsoluteFloorFraction_le_one
