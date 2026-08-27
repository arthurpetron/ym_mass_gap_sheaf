/-
# A cutoff-uniform spin-summed tail for the canonical face cylinder

The canonical support gas is also the exact support marginal of the finite
SU(2) spin-foam law at every representation cutoff.  Its single-polymer
activity is then the complete spin sum on that connected support.  The
cutoff-uniform decorated-face KP estimate bounds the discarded pinned layer
by

  `2 * anchorDecoratedEffectiveRatio ^ sizeFloor`,

where the effective ratio is exactly `1/4`.

This file lifts that activity estimate to the normalized compatible-support
probability.  Unlike the earlier cutoff-one face tail, this is the same law
used by the simultaneous representation-cutoff/volume thermodynamic
sequence.
-/

import YMGap.Continuum.Z4CanonicalFaceEventPinnedTail
import YMGap.Continuum.Z4SpinSummedPinnedLayerDeletion

namespace YMGap.Continuum.Z4SpinSummedCanonicalFaceEventPinnedTail

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteCompatibilityMarkedBound
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalFaceEventPinnedTail
open YMGap.Continuum.Z4CanonicalFiniteCompatibilityGas
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4SpinSummedCompatibleGas
open YMGap.Continuum.Z4SpinSummedSupportComponentUpper
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4SpinSummedPinnedLayerDeletion

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The large pinned layer at arbitrary representation cutoff -/

def parametricKCanonicalPinnedLargeActivity
    (cutoff n face sizeFloor : Nat) : Q' :=
  markedActivitySum (parametricKSupportActivity cutoff n)
    (canonicalPinnedLargeMark face sizeFloor)
    (canonicalSurfacePolymers n)

private theorem listQSum_range_eqv_finSum_local (value : Nat → Q') :
    ∀ cutoff : Nat,
      listQSum value (List.range cutoff) ≈ finSum value cutoff
  | 0 => Q'.eqv_refl 0
  | cutoff + 1 => by
      rw [List.range_succ, finSum_succ]
      exact Q'.eqv_trans _ _ _
        (listQSum_append value (List.range cutoff) [cutoff])
        (Q'.add_eqv_congr'
          (listQSum_range_eqv_finSum_local value cutoff)
          (Q'.eqv_of_eq (Q'.add_zero' (value cutoff))))

theorem parametricKCanonicalPinnedLargeSizeLayers_activity_eqv
    (cutoff n face sizeFloor : Nat) :
    listQSum (parametricKSupportActivity cutoff n)
        (canonicalPinnedLargeSizeLayers n face sizeFloor) ≈
      parametricKCanonicalPinnedShiftedActivitySum
        cutoff n face sizeFloor ((physicalFaceEdges n).length + 1) := by
  unfold canonicalPinnedLargeSizeLayers
    parametricKCanonicalPinnedShiftedActivitySum
  exact Q'.eqv_trans _ _ _
    (listQSum_flatMap (parametricKSupportActivity cutoff n)
      (fun offset =>
        canonicalPinnedSizePolymers n face (sizeFloor + offset))
      (List.range ((physicalFaceEdges n).length + 1)))
    (listQSum_range_eqv_finSum_local
      (fun offset =>
        parametricKPinnedSizeActivitySum
          cutoff n face (sizeFloor + offset))
      ((physicalFaceEdges n).length + 1))

theorem parametricKCanonicalPinnedLargeActivity_le_shifted
    (cutoff n face sizeFloor : Nat) :
    parametricKCanonicalPinnedLargeActivity cutoff n face sizeFloor ≤
      parametricKCanonicalPinnedShiftedActivitySum
        cutoff n face sizeFloor ((physicalFaceEdges n).length + 1) := by
  have hinjection :
      listQSum (parametricKSupportActivity cutoff n)
          (canonicalPinnedLargePolymers n face sizeFloor) ≤
        listQSum (parametricKSupportActivity cutoff n)
          (canonicalPinnedLargeSizeLayers n face sizeFloor) := by
    apply listQSum_le_of_injective
      (canonicalPinnedLargePolymers n face sizeFloor)
      (canonicalPinnedLargeSizeLayers n face sizeFloor)
      (parametricKSupportActivity cutoff n)
      (parametricKSupportActivity cutoff n)
      (fun polymer => polymer)
    · unfold canonicalPinnedLargePolymers
      exact List.filter_sublist.nodup (canonicalSurfacePolymers_nodup n)
    · intro polymer hpolymer
      exact canonicalPinnedLargePolymer_mem_sizeLayers hpolymer
    · intro left _ right _ heq
      exact heq
    · intro polymer _
      exact Q'.le_refl' _
    · intro polymer _
      exact parametricKSupportActivity_nonnegative cutoff n polymer
  change listQSum (parametricKSupportActivity cutoff n)
      (canonicalPinnedLargePolymers n face sizeFloor) ≤ _
  exact Q'.le_trans' _ _ _ hinjection
    (Q'.le_of_eqv
      (parametricKCanonicalPinnedLargeSizeLayers_activity_eqv
        cutoff n face sizeFloor))

/-- The discarded connected-support activity is geometric uniformly in the
representation cutoff, finite box, and pinned face. -/
theorem parametricKCanonicalPinnedLargeActivity_le_tail
    (cutoff n face sizeFloor : Nat) :
    parametricKCanonicalPinnedLargeActivity cutoff n face sizeFloor ≤
      Q'.ofNat 2 * anchorDecoratedEffectiveRatio ^ sizeFloor := by
  exact Q'.le_trans' _ _ _
    (parametricKCanonicalPinnedLargeActivity_le_shifted
      cutoff n face sizeFloor)
    (Q'.le_trans' _ _ _
      (parametricKCanonicalPinnedShiftedActivitySum_le_KPSum
        cutoff n face sizeFloor ((physicalFaceEdges n).length + 1))
      (parametricKPinnedShiftedKPSum_le_tail
        cutoff n face sizeFloor ((physicalFaceEdges n).length + 1)))

/-! ## 2. Exact generic-gas identification -/

private theorem familyWeight_eq_parametricKSupportFamilyActivity
    (cutoff n : Nat) : ∀ family : List (List Nat),
    familyWeight (parametricKSupportActivity cutoff n) family =
      parametricKSupportFamilyActivity cutoff n family
  | [] => rfl
  | support :: family => by
      change parametricKSupportActivity cutoff n support *
          familyWeight (parametricKSupportActivity cutoff n) family =
        parametricKSupportActivity cutoff n support *
          parametricKSupportFamilyActivity cutoff n family
      rw [familyWeight_eq_parametricKSupportFamilyActivity cutoff n family]

private theorem genericParametricKPartition_eqv
    (cutoff n : Nat) :
    partition (canonicalPolymerCompatibleB n)
        (parametricKSupportActivity cutoff n)
        (canonicalSurfacePolymers n) ≈
      parametricKCompatibleSupportGasPartition cutoff n := by
  unfold partition parametricKCompatibleSupportGasPartition
  rw [genericCompatibleFamilies_eq_canonical]
  exact listQSum_congr
    (fun family => Q'.eqv_of_eq
      (familyWeight_eq_parametricKSupportFamilyActivity
        cutoff n family)) _

private theorem genericParametricKEventNumerator_eqv
    (cutoff n : Nat) (event : List (List Nat) → Bool) :
    eventNumerator (canonicalPolymerCompatibleB n)
        (parametricKSupportActivity cutoff n)
        (canonicalSurfacePolymers n) event ≈
      parametricKCompatibleSupportEventNumerator cutoff n event := by
  unfold eventNumerator parametricKCompatibleSupportEventNumerator
  rw [genericCompatibleFamilies_eq_canonical]
  exact listQSum_congr
    (fun family => Q'.eqv_of_eq
      (familyWeight_eq_parametricKSupportFamilyActivity
        cutoff n family)) _

/-! ## 3. The normalized cutoff-uniform face tail -/

private theorem parametricKCompatibleSupportEventProbability_mono
    (cutoff n : Nat) (first second : List (List Nat) → Bool)
    (himp : ∀ family,
      family ∈ canonicalCompatibleAmbientFamilies n →
      first family = true → second family = true) :
    parametricKCompatibleSupportEventProbability cutoff n first ≤
      parametricKCompatibleSupportEventProbability cutoff n second := by
  have hnumerator :
      parametricKCompatibleSupportEventNumerator cutoff n first ≤
        parametricKCompatibleSupportEventNumerator cutoff n second := by
    unfold parametricKCompatibleSupportEventNumerator
    apply listQSum_le_of_injective
      ((canonicalCompatibleAmbientFamilies n).filter first)
      ((canonicalCompatibleAmbientFamilies n).filter second)
      (parametricKSupportFamilyActivity cutoff n)
      (parametricKSupportFamilyActivity cutoff n)
      (fun family => family)
    · exact List.filter_sublist.nodup
        (canonicalCompatibleAmbientFamilies_nodup n)
    · intro family hfamily
      have hparts := List.mem_filter.mp hfamily
      exact List.mem_filter.mpr
        ⟨hparts.1, himp family hparts.1 hparts.2⟩
    · intro left _ right _ heq
      exact heq
    · intro family _
      exact Q'.le_refl' _
    · intro family _
      exact parametricKSupportFamilyActivity_nonnegative cutoff n family
  unfold parametricKCompatibleSupportEventProbability Q'.divPos
  exact Q'.mul_le_mul_of_nonneg_right _ _ _ hnumerator
    (Q'.le_of_lt
      (Q'.recipPos_pos
        (parametricKCompatibleSupportGasPartition cutoff n)
        (parametricKCompatibleSupportGasPartition_pos cutoff n)))

theorem parametricKPinnedLargeFamilyEventProbability_le_activity
    (cutoff n face sizeFloor : Nat) :
    parametricKCompatibleSupportEventProbability cutoff n
        (canonicalPinnedLargeFamilyEvent face sizeFloor) ≤
      parametricKCanonicalPinnedLargeActivity
        cutoff n face sizeFloor := by
  have hnumerator := markedEventNumerator_le_activitySum_mul_partition
    (canonicalPolymerCompatibleB n)
    (parametricKSupportActivity cutoff n)
    (parametricKSupportActivity_nonnegative cutoff n)
    (canonicalPinnedLargeMark face sizeFloor)
    (canonicalSurfacePolymers n)
  apply Q'.divPos_le_of_le_mul
  have hnumEq := genericParametricKEventNumerator_eqv cutoff n
    (canonicalPinnedLargeFamilyEvent face sizeFloor)
  have hpartitionEq := genericParametricKPartition_eqv cutoff n
  have hrightEq :
      parametricKCanonicalPinnedLargeActivity cutoff n face sizeFloor *
          partition (canonicalPolymerCompatibleB n)
            (parametricKSupportActivity cutoff n)
            (canonicalSurfacePolymers n) ≈
        parametricKCanonicalPinnedLargeActivity cutoff n face sizeFloor *
          parametricKCompatibleSupportGasPartition cutoff n :=
    Q'.mul_eqv_congr_left _ _ _ hpartitionEq
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hnumEq)
    (Q'.le_trans' _ _ _ hnumerator (Q'.le_of_eqv hrightEq))

/-- Uniform in representation cutoff, finite volume, pinned face, and
truncation floor. -/
theorem parametricKPinnedLargeFamilyEventProbability_le_tail
    (cutoff n face sizeFloor : Nat) :
    parametricKCompatibleSupportEventProbability cutoff n
        (canonicalPinnedLargeFamilyEvent face sizeFloor) ≤
      Q'.ofNat 2 * anchorDecoratedEffectiveRatio ^ sizeFloor := by
  exact Q'.le_trans' _ _ _
    (parametricKPinnedLargeFamilyEventProbability_le_activity
      cutoff n face sizeFloor)
    (parametricKCanonicalPinnedLargeActivity_le_tail
      cutoff n face sizeFloor)

theorem parametricKFaceTruncationRemainderProbability_le_tail
    (cutoff n face sizeFloor : Nat) :
    parametricKCompatibleSupportEventProbability cutoff n
        (canonicalFaceTruncationRemainderEvent n face sizeFloor) ≤
      Q'.ofNat 2 * anchorDecoratedEffectiveRatio ^ sizeFloor := by
  exact Q'.le_trans' _ _ _
    (parametricKCompatibleSupportEventProbability_mono cutoff n _ _
      (fun _family hfamily hremainder =>
        canonicalFaceTruncationRemainder_implies_large
          hfamily hremainder))
    (parametricKPinnedLargeFamilyEventProbability_le_tail
      cutoff n face sizeFloor)

#print axioms parametricKCanonicalPinnedLargeSizeLayers_activity_eqv
#print axioms parametricKCanonicalPinnedLargeActivity_le_tail
#print axioms parametricKPinnedLargeFamilyEventProbability_le_tail
#print axioms parametricKFaceTruncationRemainderProbability_le_tail

end YMGap.Continuum.Z4SpinSummedCanonicalFaceEventPinnedTail
