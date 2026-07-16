/-
# A volume-uniform cutoff-one activity-matched block defect

The shifted coarse unit cube and the refined dyadic unit cube now both have
explicit occurrence floors in the same physical cutoff-one law.  Their
constructive minimum is therefore one exact positive rational common lower
bound for both block coordinates.

For two probabilities in `[epsilon, 1]`, their absolute difference is at most
`1 - epsilon`.  Applying this elementary exact-rational estimate gives the
first volume-independent quantitative defect bound for the coupling-shifted
unit-cube block.  It is a cutoff-one, fixed-spacing estimate: no summable
multiscale defect or continuum statement is asserted here.
-/

import YMGap.Continuum.Z4ActivityMatchedUnitCubeOccurrence
import YMGap.Continuum.Z4CouplingParametricContactOccurrenceFloor
import YMGap.Continuum.Z4SpinSummedDyadicUnitCubeUniformOccurrenceFloor

namespace YMGap.Continuum.Z4CutoffOneActivityMatchedDefectFloor

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.Z4ActivityMatchedUnitCubeOccurrence
open YMGap.Continuum.Z4CanonicalOccurrenceCofinal
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4CouplingParametricContactOccurrenceFloor
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4DyadicUnitCubeActivity
open YMGap.Continuum.Z4DyadicUnitCubeUniformOccurrenceFloor
open YMGap.Continuum.Z4SpinSummedCutoffEventBridge
open YMGap.Continuum.Z4SpinSummedDyadicUnitCubeUniformOccurrenceFloor
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UnitCubeBareCouplingShift

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. One exact positive common floor -/

def activityMatchedUnitCubeUniformOccurrenceFloor : Q' :=
  Q'.min'
    activityMatchedCoarseUnitCubeUniformOccurrenceFloor
    dyadicUnitCubeUniformOccurrenceFloor

theorem activityMatchedUnitCubeUniformOccurrenceFloor_pos :
    (0 : Q') < activityMatchedUnitCubeUniformOccurrenceFloor := by
  unfold activityMatchedUnitCubeUniformOccurrenceFloor Q'.min'
  by_cases h :
      activityMatchedCoarseUnitCubeUniformOccurrenceFloor ≤
        dyadicUnitCubeUniformOccurrenceFloor
  · rw [if_pos h]
    exact activityMatchedCoarseUnitCubeUniformOccurrenceFloor_pos
  · rw [if_neg h]
    exact dyadicUnitCubeUniformOccurrenceFloor_pos

theorem activityMatchedUnitCubeUniformOccurrenceFloor_le_coarse :
    activityMatchedUnitCubeUniformOccurrenceFloor ≤
      activityMatchedCoarseUnitCubeUniformOccurrenceFloor := by
  unfold activityMatchedUnitCubeUniformOccurrenceFloor
  exact Q'.min_le_left

theorem activityMatchedUnitCubeUniformOccurrenceFloor_le_refined :
    activityMatchedUnitCubeUniformOccurrenceFloor ≤
      dyadicUnitCubeUniformOccurrenceFloor := by
  unfold activityMatchedUnitCubeUniformOccurrenceFloor
  exact Q'.min_le_right

/-! ## 2. A common physical-law floor for both block coordinates -/

theorem uniformFloor_le_activityMatchedCoarseBlockProbability
    {volume : Nat} (hvolume : 4 ≤ volume) :
    activityMatchedUnitCubeUniformOccurrenceFloor ≤
      couplingKUnitCubeBlockCoarseProbability
        (unitCubeBlockCoupling anchorCoupling)
        (unitCubeBlockCoupling_nonnegative (by decide))
        1 volume := by
  have hroot :
      coarseUnitCubeBlockRootAt volume =
        transportPolymer 2 volume coarseUnitCubeSupportIds := by
    unfold coarseUnitCubeBlockRootAt
    exact transportPolymer_trans (by omega) hvolume
      coarseUnitCubeSupportIds_mem_canonicalSurfacePolymers
  refine Q'.le_trans' _ _ _
    activityMatchedUnitCubeUniformOccurrenceFloor_le_coarse ?_
  unfold couplingKUnitCubeBlockCoarseProbability
  rw [unitCubeBlock_targetCoarse_eq_occurrence, hroot]
  exact
    activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_physicalProbability
      (n := volume) (by omega)

theorem uniformFloor_le_activityMatchedRefinedBlockProbability
    {volume : Nat} (hvolume : 4 ≤ volume) :
    activityMatchedUnitCubeUniformOccurrenceFloor ≤
      couplingKUnitCubeBlockRefinedProbability
        anchorCoupling (by decide) 1 volume := by
  have hcompatible :=
    dyadicUnitCubeUniformOccurrenceFloor_le_parametricK_probability
      (cutoff := 1) (n := volume) (by omega) hvolume
  have hphysical :=
    couplingKFamilyEventProbability_anchor_eqv_compatible
      1 volume
      (familyContainsPolymerB (dyadicUnitCubeSupportIdsAt volume))
  unfold couplingKUnitCubeBlockRefinedProbability
  rw [unitCubeBlock_targetRefined_eq_occurrence]
  exact Q'.le_trans' _ _ _
    activityMatchedUnitCubeUniformOccurrenceFloor_le_refined
    (Q'.le_trans' _ _ _ hcompatible (Q'.ge_of_eqv hphysical))

/-! ## 3. Exact-rational probability separation -/

private theorem neg_one_sub_eqv_floor_sub_one (floor : Q') :
    -(1 + -floor) ≈ floor + -(1 : Q') := by
  exact Q'.eqv_trans _ _ _
    (Q'.neg_add_eqv 1 (-floor))
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (-1) _ _
        (Q'.neg_neg_eqv floor))
      (Q'.add_comm_eqv (-1) floor))

theorem abs_difference_le_one_sub_floor
    {floor left right : Q'}
    (hfloorLeft : floor ≤ left) (hfloorRight : floor ≤ right)
    (hleftOne : left ≤ (1 : Q'))
    (hrightOne : right ≤ (1 : Q')) :
    Q'.abs (left + -right) ≤ (1 : Q') + -floor := by
  have hnegRight : -(1 : Q') ≤ -right :=
    Q'.neg_le_neg hrightOne
  have hlowerRaw : floor + -(1 : Q') ≤ left + -right :=
    Q'.add_le_add hfloorLeft hnegRight
  have hlower : -((1 : Q') + -floor) ≤ left + -right :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (neg_one_sub_eqv_floor_sub_one floor))
      hlowerRaw
  have hnegFloor : -right ≤ -floor :=
    Q'.neg_le_neg hfloorRight
  have hupper : left + -right ≤ (1 : Q') + -floor :=
    Q'.add_le_add hleftOne hnegFloor
  exact Q'.abs_le hlower hupper

/-! ## 4. The explicit uniform cutoff-one defect bound -/

def activityMatchedUnitCubeUniformDefectBound : Q' :=
  (1 : Q') + -activityMatchedUnitCubeUniformOccurrenceFloor

theorem activityMatchedUnitCubeUniformDefectBound_lt_one :
    activityMatchedUnitCubeUniformDefectBound < (1 : Q') := by
  unfold activityMatchedUnitCubeUniformDefectBound
  exact YMGap.Continuum.CubeRatioBounds.sub_lt_self_of_pos
    activityMatchedUnitCubeUniformOccurrenceFloor_pos

/-- The activity-matched cutoff-one block defect is bounded away from one by
the same positive exact rational in every containing volume. -/
theorem activityMatchedUnitCubeBlockDefect_le_uniformBound
    {volume : Nat} (hvolume : 4 ≤ volume) :
    activityMatchedUnitCubeBlockDefect
        anchorCoupling (by decide) 1 volume ≤
      activityMatchedUnitCubeUniformDefectBound := by
  unfold activityMatchedUnitCubeBlockDefect
    couplingKUnitCubeBlockDefect
    activityMatchedUnitCubeUniformDefectBound
  exact abs_difference_le_one_sub_floor
    (uniformFloor_le_activityMatchedCoarseBlockProbability hvolume)
    (uniformFloor_le_activityMatchedRefinedBlockProbability hvolume)
    (couplingKUnitCubeBlockCoarseProbability_le_one
      (unitCubeBlockCoupling anchorCoupling)
      (unitCubeBlockCoupling_nonnegative (by decide)) 1 volume)
    (couplingKUnitCubeBlockRefinedProbability_le_one
      anchorCoupling (by decide) 1 volume)

theorem activityMatchedUnitCubeBlockDefect_uniform_lt_one
    {volume : Nat} (hvolume : 4 ≤ volume) :
    activityMatchedUnitCubeBlockDefect
        anchorCoupling (by decide) 1 volume < (1 : Q') :=
  Q'.lt_of_le_of_lt
    (activityMatchedUnitCubeBlockDefect_le_uniformBound hvolume)
    activityMatchedUnitCubeUniformDefectBound_lt_one

#print axioms activityMatchedUnitCubeUniformOccurrenceFloor_pos
#print axioms activityMatchedUnitCubeUniformOccurrenceFloor_le_coarse
#print axioms activityMatchedUnitCubeUniformOccurrenceFloor_le_refined
#print axioms uniformFloor_le_activityMatchedCoarseBlockProbability
#print axioms uniformFloor_le_activityMatchedRefinedBlockProbability
#print axioms abs_difference_le_one_sub_floor
#print axioms activityMatchedUnitCubeUniformDefectBound_lt_one
#print axioms activityMatchedUnitCubeBlockDefect_le_uniformBound
#print axioms activityMatchedUnitCubeBlockDefect_uniform_lt_one

end YMGap.Continuum.Z4CutoffOneActivityMatchedDefectFloor
