/-
# A volume-uniform occurrence floor for the dyadic unit cube

The contact-layer deletion estimate controls the full finite-volume
partition by `2^600` times the partition of polymers compatible with the
transported 24-face cube.  The finite root-insertion theorem injects every
compatible deleted family into the cube-occurrence numerator.  Combining the
two estimates gives one explicit positive rational lower bound, independent
of the containing box.

This closes the finite-volume normalization bottleneck for this particular
local excitation.  It is not an RG comparison or a continuum-limit theorem.
-/

import YMGap.Continuum.FiniteCompatibilityRootInsertion
import YMGap.Continuum.Z4CanonicalContactLayerDeletion

namespace YMGap.Continuum.Z4DyadicUnitCubeUniformOccurrenceFloor

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteCompatibilityLayerDeletion
open YMGap.Continuum.FiniteCompatibilityRootInsertion
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.Z4CanonicalContactLayerDeletion
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalFiniteCompatibilityGas
open YMGap.Continuum.Z4CanonicalIncompatibilityWalk
open YMGap.Continuum.Z4CanonicalPinnedLayerDeletion
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicUnitCubeActivity
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The contact-deleted ambient supports exact root insertion -/

theorem dyadicUnitCubeContactDeletedAmbient_nodup (n : Nat) :
    (dyadicUnitCubeContactDeletedAmbient n).Nodup := by
  unfold dyadicUnitCubeContactDeletedAmbient
    canonicalContactDeletedAmbient
  exact deleteMarkedLayers_nodup
    (fun face polymer => canonicalContainsFaceB face polymer)
    (canonicalContactFaceCandidates n
      (dyadicUnitCubeSupportIdsAt n))
    (canonicalSurfacePolymers_nodup n)

theorem dyadicUnitCubeContactDeletedAmbient_mem_source
    {n : Nat} {polymer : List Nat}
    (hpolymer : polymer ∈ dyadicUnitCubeContactDeletedAmbient n) :
    polymer ∈ canonicalSurfacePolymers n := by
  unfold dyadicUnitCubeContactDeletedAmbient
    canonicalContactDeletedAmbient at hpolymer
  exact mem_deleteMarkedLayers_source
    (fun face atom => canonicalContainsFaceB face atom)
    (canonicalContactFaceCandidates n
      (dyadicUnitCubeSupportIdsAt n))
    (canonicalSurfacePolymers n) polymer hpolymer

theorem dyadicUnitCubeSupportIdsAt_not_mem_contactDeleted
    {n : Nat} (hn : 4 ≤ n) :
    dyadicUnitCubeSupportIdsAt n ∉
      dyadicUnitCubeContactDeletedAmbient n := by
  intro hrootDeleted
  have hrootAmbient :=
    dyadicUnitCubeSupportIdsAt_mem_canonicalSurfacePolymers hn
  obtain ⟨face, hface⟩ := canonicalSurfacePolymers_allNonempty n
    (dyadicUnitCubeSupportIdsAt n) hrootAmbient
  have hfalse : canonicalPolymerCompatibleB n
      (dyadicUnitCubeSupportIdsAt n)
      (dyadicUnitCubeSupportIdsAt n) = false :=
    canonicalPolymerCompatibleB_false_of_contact hface hface
      (Or.inl rfl)
  have htrue := canonicalContactDeletedAmbient_survivor_compatible
    hrootDeleted
  rw [hfalse] at htrue
  cases htrue

/-- Before normalization, the cube activity times the deleted partition is
bounded by the exact anchor occurrence numerator. -/
theorem dyadicUnitCube_activity_mul_deletedPartition_le_numerator
    {n : Nat} (hn : 4 ≤ n) :
    canonicalSurfaceActivity anchorCoupling n
        (dyadicUnitCubeSupportIdsAt n) *
      canonicalPolymerPartition anchorCoupling n
        (dyadicUnitCubeContactDeletedAmbient n) ≤
      anchorEventNumerator n
        (familyContainsPolymerB (dyadicUnitCubeSupportIdsAt n)) := by
  have hgeneric := root_weight_mul_partition_le_occurrenceNumerator
    (canonicalPolymerCompatibleB n)
    (canonicalPolymerCompatibleB_symm n)
    (canonicalSurfaceActivity anchorCoupling n)
    (canonicalSurfacePolymer_activity_nonnegative n)
    (canonicalSurfacePolymers n)
    (dyadicUnitCubeContactDeletedAmbient n)
    (dyadicUnitCubeSupportIdsAt n)
    (canonicalSurfacePolymers_nodup n)
    (dyadicUnitCubeContactDeletedAmbient_nodup n)
    (dyadicUnitCubeSupportIdsAt_mem_canonicalSurfacePolymers hn)
    (dyadicUnitCubeSupportIdsAt_not_mem_contactDeleted hn)
    (fun atom hatom =>
      dyadicUnitCubeContactDeletedAmbient_mem_source hatom)
    (fun atom hatom =>
      canonicalContactDeletedAmbient_survivor_compatible hatom)
  have hcanonicalMember :
      canonicalSurfaceActivity anchorCoupling n
          (dyadicUnitCubeSupportIdsAt n) *
        canonicalPolymerPartition anchorCoupling n
          (dyadicUnitCubeContactDeletedAmbient n) ≤
        canonicalPolymerEventNumerator anchorCoupling n
          (canonicalSurfacePolymers n)
          (fun family => memberB family
            (dyadicUnitCubeSupportIdsAt n)) := by
    simpa only [canonicalPolymerPartition,
      canonicalPolymerEventNumerator] using hgeneric
  have hevent :
      (fun family => memberB family (dyadicUnitCubeSupportIdsAt n)) =
        familyContainsPolymerB (dyadicUnitCubeSupportIdsAt n) := by
    funext family
    apply Bool.eq_iff_iff.mpr
    simp [memberB, familyContainsPolymerB]
  rw [hevent] at hcanonicalMember
  have hcanonical := hcanonicalMember
  exact Q'.le_trans' _ _ _ hcanonical
    (Q'.le_of_eqv
      (canonicalPolymerEventNumerator_eqv_anchor n
        (familyContainsPolymerB (dyadicUnitCubeSupportIdsAt n))))

/-! ## 2. One explicit positive rational floor -/

def dyadicUnitCubeOccurrenceCost : Q' :=
  (Q'.ofNat 2) ^ 600

theorem dyadicUnitCubeOccurrenceCost_pos :
    (0 : Q') < dyadicUnitCubeOccurrenceCost := by
  unfold dyadicUnitCubeOccurrenceCost
  exact YMGap.Continuum.HKPos.pow_pos (by decide) 600

/-- A closed exact rational independent of the finite box. -/
def dyadicUnitCubeUniformOccurrenceFloor : Q' :=
  Q'.divPos
    (canonicalSurfaceActivity anchorCoupling 4
      dyadicUnitCubeSupportIds)
    dyadicUnitCubeOccurrenceCost
    dyadicUnitCubeOccurrenceCost_pos

theorem dyadicUnitCubeUniformOccurrenceFloor_pos :
    (0 : Q') < dyadicUnitCubeUniformOccurrenceFloor := by
  unfold dyadicUnitCubeUniformOccurrenceFloor
  exact Q'.divPos_pos _ _ dyadicUnitCubeOccurrenceCost_pos
    dyadicUnitCube_anchorActivity_pos

private theorem dyadicUnitCube_anchorPartition_le_cost_mul_deleted
    {n : Nat} (hn : 4 ≤ n) :
    anchorCanonicalPartition n ≤
      dyadicUnitCubeOccurrenceCost *
        canonicalPolymerPartition anchorCoupling n
          (dyadicUnitCubeContactDeletedAmbient n) := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (anchorCanonicalPartition_eqv_generic n))
    (by
      unfold dyadicUnitCubeOccurrenceCost
      exact dyadicUnitCubePartition_le_two_pow_six_hundred_mul_deleted hn)

/-- Uniform finite-volume non-triviality of the transported local cube: the
same strictly positive exact rational lower-bounds its normalized occurrence
probability in every containing canonical box. -/
theorem dyadicUnitCubeUniformOccurrenceFloor_le_probability
    {n : Nat} (hn : 4 ≤ n) :
    dyadicUnitCubeUniformOccurrenceFloor ≤
      anchorPolymerOccurrenceProbability n
        (dyadicUnitCubeSupportIdsAt n) := by
  let baseActivity := canonicalSurfaceActivity anchorCoupling 4
    dyadicUnitCubeSupportIds
  let transportedActivity := canonicalSurfaceActivity anchorCoupling n
    (dyadicUnitCubeSupportIdsAt n)
  let deletedPartition := canonicalPolymerPartition anchorCoupling n
    (dyadicUnitCubeContactDeletedAmbient n)
  let numerator := anchorEventNumerator n
    (familyContainsPolymerB (dyadicUnitCubeSupportIdsAt n))
  have htransport : baseActivity ≈ transportedActivity := by
    unfold baseActivity transportedActivity dyadicUnitCubeSupportIdsAt
    exact canonicalSurfaceActivity_transport anchorCoupling hn
      dyadicUnitCubeSupportIds_mem_cutoffOneFaceSupports
  have hdeleted0 : (0 : Q') ≤ deletedPartition := by
    unfold deletedPartition
    exact anchorCanonicalPolymerPartition_nonnegative n _
  have hpartition : anchorCanonicalPartition n ≤
      dyadicUnitCubeOccurrenceCost * deletedPartition := by
    unfold deletedPartition
    exact dyadicUnitCube_anchorPartition_le_cost_mul_deleted hn
  have hinsertion : transportedActivity * deletedPartition ≤
      numerator := by
    unfold transportedActivity deletedPartition numerator
    exact dyadicUnitCube_activity_mul_deletedPartition_le_numerator hn
  have hfloor0 : (0 : Q') ≤
      dyadicUnitCubeUniformOccurrenceFloor :=
    Q'.le_of_lt dyadicUnitCubeUniformOccurrenceFloor_pos
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _
    hpartition hfloor0
  have hcollapse :
      dyadicUnitCubeUniformOccurrenceFloor *
          (dyadicUnitCubeOccurrenceCost * deletedPartition) ≈
        baseActivity * deletedPartition := by
    refine Q'.eqv_trans _
      ((dyadicUnitCubeUniformOccurrenceFloor *
          dyadicUnitCubeOccurrenceCost) * deletedPartition) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    apply Q'.mul_eqv_congr_right
    unfold dyadicUnitCubeUniformOccurrenceFloor baseActivity
    exact Q'.divPos_mul_eqv _ _ dyadicUnitCubeOccurrenceCost_pos
  have hactivityScaled : baseActivity * deletedPartition ≤
      transportedActivity * deletedPartition :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.le_of_eqv htransport) hdeleted0
  have hmul : dyadicUnitCubeUniformOccurrenceFloor *
      anchorCanonicalPartition n ≤ numerator :=
    Q'.le_trans' _ _ _ hscaled
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcollapse)
        (Q'.le_trans' _ _ _ hactivityScaled hinsertion))
  unfold anchorPolymerOccurrenceProbability anchorEventProbability
  exact Q'.le_divPos_of_mul_le numerator (anchorCanonicalPartition n)
    (anchorCanonicalPartition_pos n) hmul

end YMGap.Continuum.Z4DyadicUnitCubeUniformOccurrenceFloor

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4DyadicUnitCubeUniformOccurrenceFloor.dyadicUnitCubeContactDeletedAmbient_nodup
#print axioms YMGap.Continuum.Z4DyadicUnitCubeUniformOccurrenceFloor.dyadicUnitCubeSupportIdsAt_not_mem_contactDeleted
#print axioms YMGap.Continuum.Z4DyadicUnitCubeUniformOccurrenceFloor.dyadicUnitCube_activity_mul_deletedPartition_le_numerator
#print axioms YMGap.Continuum.Z4DyadicUnitCubeUniformOccurrenceFloor.dyadicUnitCubeOccurrenceCost_pos
#print axioms YMGap.Continuum.Z4DyadicUnitCubeUniformOccurrenceFloor.dyadicUnitCubeUniformOccurrenceFloor_pos
#print axioms YMGap.Continuum.Z4DyadicUnitCubeUniformOccurrenceFloor.dyadicUnitCubeUniformOccurrenceFloor_le_probability
