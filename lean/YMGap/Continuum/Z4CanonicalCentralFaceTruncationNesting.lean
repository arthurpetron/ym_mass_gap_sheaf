/-
# Common-box nesting of central face truncations

For `smallFloor <= largeFloor`, uniformly pad the smaller fixed chart by the
difference of the floors.  Its distinguished plaquette then becomes exactly
the distinguished plaquette of the larger source box.  Consequently the
size-`< smallFloor` event is a literal subevent of the size-`< largeFloor`
event in one common compatible-support law.

The difference event is contained in the previously bounded false-negative
remainder at `smallFloor`.  Thus, at every representation cutoff and every
explicit coupling in the proved strong-coupling interval, the two common-box
probabilities differ one-sidedly by at most the geometric pinned tail.
-/

import YMGap.Continuum.Z4CanonicalCentralFaceFixedCylinder
import YMGap.Continuum.Z4CouplingParametricCanonicalFaceEventPinnedTail
import YMGap.Continuum.Z4CouplingParametricCylinderJointFunctional

namespace YMGap.Continuum.Z4CanonicalCentralFaceTruncationNesting

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4CanonicalCentralFaceFixedCylinder
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalFaceEventCylinderCompiler
open YMGap.Continuum.Z4CanonicalFaceEventPinnedTail
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4CouplingParametricCanonicalFaceEventPinnedTail
open YMGap.Continuum.Z4CouplingParametricCylinderJointFunctional
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UniformShiftPhysicalTransport

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The smaller chart centered in the larger source box -/

def pinnedFaceFloorPadding (smallFloor largeFloor : Nat) : Nat :=
  largeFloor - smallFloor

theorem pinnedFaceStageBase_floorPadding
    {smallFloor largeFloor : Nat} (hfloor : smallFloor ≤ largeFloor) :
    pinnedFaceStageBase smallFloor
        (pinnedFaceFloorPadding smallFloor largeFloor) =
      pinnedFaceSourceBase largeFloor := by
  unfold pinnedFaceFloorPadding pinnedFaceStageBase pinnedFaceSourceBase
    uniformPaddedBase
  omega

theorem pinnedFacePlaquette_floorPadding
    {smallFloor largeFloor : Nat} (hfloor : smallFloor ≤ largeFloor) :
    pinnedFacePlaquette smallFloor
        (pinnedFaceFloorPadding smallFloor largeFloor) =
      pinnedFacePlaquette largeFloor 0 := by
  unfold pinnedFaceFloorPadding pinnedFacePlaquette
  rw [Nat.add_sub_of_le hfloor]
  simp only [Nat.add_zero]

theorem pinnedFaceId_floorPadding
    {smallFloor largeFloor : Nat} (hfloor : smallFloor ≤ largeFloor) :
    pinnedFaceId smallFloor
        (pinnedFaceFloorPadding smallFloor largeFloor) =
      pinnedFaceId largeFloor 0 := by
  let padding := pinnedFaceFloorPadding smallFloor largeFloor
  have hbase := pinnedFaceStageBase_floorPadding hfloor
  have hplaquette := pinnedFacePlaquette_floorPadding hfloor
  have hsmallPhysical :
      pinnedFaceId smallFloor padding ∈
        physicalFaceEdges (pinnedFaceSourceBase largeFloor) := by
    rw [← hbase]
    exact pinnedFaceId_physical smallFloor padding
  have hlargePhysical :
      pinnedFaceId largeFloor 0 ∈
        physicalFaceEdges (pinnedFaceSourceBase largeFloor) := by
    simpa [pinnedFaceStageBase, uniformPaddedBase] using
      pinnedFaceId_physical largeFloor 0
  apply boxPlaquetteAt_injective_on_physical
    hsmallPhysical hlargePhysical
  have hsmallPoint :
      boxPlaquetteAt (pinnedFaceSourceBase largeFloor)
          (pinnedFaceId smallFloor padding) =
        pinnedFacePlaquette largeFloor 0 := by
    rw [← hbase, boxPlaquetteAt_pinnedFaceId]
    simpa [padding] using hplaquette
  have hlargePoint :
      boxPlaquetteAt (pinnedFaceSourceBase largeFloor)
          (pinnedFaceId largeFloor 0) =
        pinnedFacePlaquette largeFloor 0 := by
    simpa [pinnedFaceStageBase, uniformPaddedBase] using
      boxPlaquetteAt_pinnedFaceId largeFloor 0
  exact hsmallPoint.trans hlargePoint.symm

def pinnedFaceCommonSmallRoots
    (smallFloor largeFloor : Nat) : List (List Nat) :=
  pinnedFaceStageRoots smallFloor
    (pinnedFaceFloorPadding smallFloor largeFloor)

def pinnedFaceCommonSmallEvent
    (smallFloor largeFloor : Nat) : List (List Nat) → Bool :=
  sourceCylinderEvent
    (pinnedFaceCommonSmallRoots smallFloor largeFloor)
    canonicalFaceCylinderPredicate

def pinnedFaceCommonLargeEvent
    (largeFloor : Nat) : List (List Nat) → Bool :=
  sourceCylinderEvent (pinnedFaceFixedRoots largeFloor)
    canonicalFaceCylinderPredicate

theorem pinnedFaceCommonSmallEvent_eq_truncated
    {smallFloor largeFloor : Nat} (hfloor : smallFloor ≤ largeFloor)
    (family : List (List Nat)) :
    pinnedFaceCommonSmallEvent smallFloor largeFloor family =
      canonicalFaceTruncatedCylinderEvent
        (pinnedFaceSourceBase largeFloor)
        (pinnedFaceId largeFloor 0) smallFloor family := by
  unfold pinnedFaceCommonSmallEvent pinnedFaceCommonSmallRoots
  rw [← pinnedFaceTruncatedCylinderEvent_eq_fixedStage
    smallFloor (pinnedFaceFloorPadding smallFloor largeFloor) family]
  rw [pinnedFaceStageBase_floorPadding hfloor,
    pinnedFaceId_floorPadding hfloor]

theorem pinnedFaceCommonLargeEvent_eq_truncated
    (largeFloor : Nat) (family : List (List Nat)) :
    pinnedFaceCommonLargeEvent largeFloor family =
      canonicalFaceTruncatedCylinderEvent
        (pinnedFaceSourceBase largeFloor)
        (pinnedFaceId largeFloor 0) largeFloor family := by
  unfold pinnedFaceCommonLargeEvent pinnedFaceFixedRoots
  rfl

/-! ## 2. Exact event nesting and its difference remainder -/

theorem canonicalFaceTruncatedCylinderEvent_mono_size
    {n face smallFloor largeFloor : Nat}
    (hfloor : smallFloor ≤ largeFloor)
    (family : List (List Nat))
    (hsmall : canonicalFaceTruncatedCylinderEvent
      n face smallFloor family = true) :
    canonicalFaceTruncatedCylinderEvent
      n face largeFloor family = true := by
  unfold canonicalFaceTruncatedCylinderEvent at hsmall ⊢
  rw [sourceCanonicalFaceCylinderEvent_true_iff] at hsmall ⊢
  obtain ⟨root, hroot, hfamily⟩ := hsmall
  refine ⟨root, ?_, hfamily⟩
  have hparts := mem_canonicalPinnedBelowSizePolymers_iff.mp hroot
  exact mem_canonicalPinnedBelowSizePolymers_iff.mpr
    ⟨hparts.1, hparts.2.1, Nat.lt_of_lt_of_le hparts.2.2 hfloor⟩

theorem pinnedFaceCommonSmallEvent_implies_large
    {smallFloor largeFloor : Nat} (hfloor : smallFloor ≤ largeFloor)
    (family : List (List Nat))
    (hsmall : pinnedFaceCommonSmallEvent
      smallFloor largeFloor family = true) :
    pinnedFaceCommonLargeEvent largeFloor family = true := by
  rw [pinnedFaceCommonSmallEvent_eq_truncated hfloor] at hsmall
  rw [pinnedFaceCommonLargeEvent_eq_truncated]
  exact canonicalFaceTruncatedCylinderEvent_mono_size
    hfloor family hsmall

def pinnedFaceCommonTruncationDifferenceEvent
    (smallFloor largeFloor : Nat) : List (List Nat) → Bool :=
  fun family =>
    pinnedFaceCommonLargeEvent largeFloor family &&
      !(pinnedFaceCommonSmallEvent smallFloor largeFloor family)

theorem pinnedFaceCommonDifference_implies_remainder
    {smallFloor largeFloor : Nat} (hfloor : smallFloor ≤ largeFloor)
    {family : List (List Nat)}
    (hdifference : pinnedFaceCommonTruncationDifferenceEvent
      smallFloor largeFloor family = true) :
    canonicalFaceTruncationRemainderEvent
        (pinnedFaceSourceBase largeFloor)
        (pinnedFaceId largeFloor 0) smallFloor family = true := by
  have hparts := (Bool.and_eq_true _ _).mp hdifference
  have hlarge := hparts.1
  have hsmallFalse : pinnedFaceCommonSmallEvent
      smallFloor largeFloor family = false := by
    cases hsmall : pinnedFaceCommonSmallEvent
        smallFloor largeFloor family with
    | false => rfl
    | true =>
        rw [hsmall] at hparts
        cases hparts.2
  have hface : familyContainsFaceB
      (pinnedFaceId largeFloor 0) family = true := by
    rw [pinnedFaceCommonLargeEvent_eq_truncated] at hlarge
    exact canonicalFaceTruncatedCylinderEvent_implies_face hlarge
  have htruncatedFalse : canonicalFaceTruncatedCylinderEvent
      (pinnedFaceSourceBase largeFloor)
      (pinnedFaceId largeFloor 0) smallFloor family = false := by
    rw [← pinnedFaceCommonSmallEvent_eq_truncated hfloor]
    exact hsmallFalse
  unfold canonicalFaceTruncationRemainderEvent
  rw [hface, htruncatedFalse]
  rfl

theorem pinnedFaceCommonLargeEvent_eq_small_or_difference
    {smallFloor largeFloor : Nat} (hfloor : smallFloor ≤ largeFloor)
    (family : List (List Nat)) :
    pinnedFaceCommonLargeEvent largeFloor family =
      (pinnedFaceCommonSmallEvent smallFloor largeFloor family ||
        pinnedFaceCommonTruncationDifferenceEvent
          smallFloor largeFloor family) := by
  cases hsmall : pinnedFaceCommonSmallEvent
      smallFloor largeFloor family with
  | false =>
      unfold pinnedFaceCommonTruncationDifferenceEvent
      simp only [hsmall, Bool.not_false, Bool.and_true,
        Bool.false_or]
  | true =>
      have hlarge := pinnedFaceCommonSmallEvent_implies_large
        hfloor family hsmall
      rw [hlarge]
      simp only [Bool.true_or]

theorem pinnedFaceCommonSmall_difference_disjoint
    (smallFloor largeFloor : Nat) (family : List (List Nat))
    (hsmall : pinnedFaceCommonSmallEvent
      smallFloor largeFloor family = true) :
    pinnedFaceCommonTruncationDifferenceEvent
      smallFloor largeFloor family = false := by
  unfold pinnedFaceCommonTruncationDifferenceEvent
  rw [hsmall]
  simp only [Bool.not_true, Bool.and_false]

/-! ## 3. Same-law cutoff-uniform probability comparison -/

theorem couplingParametricKPinnedFaceCommonDifferenceProbability_le_tail
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (cutoff : Nat) {smallFloor largeFloor : Nat}
    (hfloor : smallFloor ≤ largeFloor) :
    couplingParametricKCompatibleSupportEventProbability
        coupling hcoupling cutoff (pinnedFaceSourceBase largeFloor)
        (pinnedFaceCommonTruncationDifferenceEvent
          smallFloor largeFloor) ≤
      Q'.ofNat 2 * anchorDecoratedEffectiveRatio ^ smallFloor := by
  exact Q'.le_trans' _ _ _
    (couplingParametricKCompatibleSupportEventProbability_mono
      hcoupling cutoff (pinnedFaceSourceBase largeFloor) _ _
      (fun _family _hfamily hdifference =>
        pinnedFaceCommonDifference_implies_remainder
          hfloor hdifference))
    (couplingParametricKFaceTruncationRemainderProbability_le_tail
      hcoupling hle cutoff (pinnedFaceSourceBase largeFloor)
      (pinnedFaceId largeFloor 0) smallFloor)

theorem couplingParametricKPinnedFaceCommonSmallProbability_le_large
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {smallFloor largeFloor : Nat}
    (hfloor : smallFloor ≤ largeFloor) :
    couplingParametricKCompatibleSupportEventProbability
        coupling hcoupling cutoff (pinnedFaceSourceBase largeFloor)
        (pinnedFaceCommonSmallEvent smallFloor largeFloor) ≤
      couplingParametricKCompatibleSupportEventProbability
        coupling hcoupling cutoff (pinnedFaceSourceBase largeFloor)
        (pinnedFaceCommonLargeEvent largeFloor) := by
  exact couplingParametricKCompatibleSupportEventProbability_mono
    hcoupling cutoff (pinnedFaceSourceBase largeFloor) _ _
    (fun family _hfamily hsmall =>
      pinnedFaceCommonSmallEvent_implies_large hfloor family hsmall)

theorem couplingParametricKPinnedFaceCommonLargeProbability_le_small_add_tail
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (cutoff : Nat) {smallFloor largeFloor : Nat}
    (hfloor : smallFloor ≤ largeFloor) :
    couplingParametricKCompatibleSupportEventProbability
        coupling hcoupling cutoff (pinnedFaceSourceBase largeFloor)
        (pinnedFaceCommonLargeEvent largeFloor) ≤
      couplingParametricKCompatibleSupportEventProbability
          coupling hcoupling cutoff (pinnedFaceSourceBase largeFloor)
          (pinnedFaceCommonSmallEvent smallFloor largeFloor) +
        Q'.ofNat 2 * anchorDecoratedEffectiveRatio ^ smallFloor := by
  have hevent :
      couplingParametricKCompatibleSupportEventProbability
          coupling hcoupling cutoff (pinnedFaceSourceBase largeFloor)
          (pinnedFaceCommonLargeEvent largeFloor) ≈
        couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff (pinnedFaceSourceBase largeFloor)
            (fun family =>
              pinnedFaceCommonSmallEvent smallFloor largeFloor family ||
                pinnedFaceCommonTruncationDifferenceEvent
                  smallFloor largeFloor family) := by
    unfold couplingParametricKCompatibleSupportEventProbability
      couplingParametricKCompatibleSupportEventNumerator
    rw [show (canonicalCompatibleAmbientFamilies
        (pinnedFaceSourceBase largeFloor)).filter
          (pinnedFaceCommonLargeEvent largeFloor) =
        (canonicalCompatibleAmbientFamilies
          (pinnedFaceSourceBase largeFloor)).filter
          (fun family =>
            pinnedFaceCommonSmallEvent smallFloor largeFloor family ||
              pinnedFaceCommonTruncationDifferenceEvent
                smallFloor largeFloor family) by
      apply List.filter_congr
      intro family _
      exact pinnedFaceCommonLargeEvent_eq_small_or_difference
        hfloor family]
    exact Q'.eqv_refl _
  have hadd := couplingParametricKCompatibleEventProbability_union_eqv_add
    hcoupling cutoff (pinnedFaceSourceBase largeFloor)
    (pinnedFaceCommonSmallEvent smallFloor largeFloor)
    (pinnedFaceCommonTruncationDifferenceEvent smallFloor largeFloor)
    (pinnedFaceCommonSmall_difference_disjoint smallFloor largeFloor)
  have hdecomposition := Q'.eqv_trans _ _ _ hevent hadd
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hdecomposition)
    (Q'.add_le_add_left _ _ _
      (couplingParametricKPinnedFaceCommonDifferenceProbability_le_tail
        hcoupling hle cutoff hfloor))

#print axioms pinnedFaceStageBase_floorPadding
#print axioms pinnedFacePlaquette_floorPadding
#print axioms pinnedFaceId_floorPadding
#print axioms canonicalFaceTruncatedCylinderEvent_mono_size
#print axioms pinnedFaceCommonDifference_implies_remainder
#print axioms couplingParametricKPinnedFaceCommonDifferenceProbability_le_tail
#print axioms couplingParametricKPinnedFaceCommonSmallProbability_le_large
#print axioms couplingParametricKPinnedFaceCommonLargeProbability_le_small_add_tail

end YMGap.Continuum.Z4CanonicalCentralFaceTruncationNesting
