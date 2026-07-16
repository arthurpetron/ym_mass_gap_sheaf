/-
# A cutoff-uniform activity-matched block defect

The shifted coarse cube now has a positive occurrence floor in the full
spin-summed physical law at every representation cutoff at least one.  The
existing dyadic refined-cube floor already has the same cutoff uniformity at
the strong-coupling anchor.  Their constructive minimum is therefore a
single exact positive rational lower bound for both production block
coordinates, uniformly in cutoff and containing volume.

Combining these two floors with the exact-rational probability-separation
lemma gives the all-cutoff extension of the cutoff-one defect estimate.  This
is still a fixed-spacing finite-cylinder result; it does not itself assert a
summable multiscale defect or continuum limit.
-/

import YMGap.Continuum.Z4CouplingParametricSpinSummedCoarseOccurrenceFloor
import YMGap.Continuum.Z4CutoffOneActivityMatchedDefectFloor

namespace YMGap.Continuum.Z4AllCutoffActivityMatchedDefectFloor

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.Z4ActivityMatchedUnitCubeOccurrence
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4CouplingParametricSpinSummedCoarseOccurrenceFloor
open YMGap.Continuum.Z4CutoffOneActivityMatchedDefectFloor
open YMGap.Continuum.Z4DyadicUnitCubeActivity
open YMGap.Continuum.Z4SpinSummedDyadicUnitCubeUniformOccurrenceFloor
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UnitCubeBareCouplingShift

/-! ## 1. One common all-cutoff floor for both production coordinates -/

theorem uniformFloor_le_activityMatchedCoarseBlockProbability_allCutoff
    {cutoff volume : Nat} (hcutoff : 1 ≤ cutoff)
    (hvolume : 4 ≤ volume) :
    activityMatchedUnitCubeUniformOccurrenceFloor ≤
      couplingKUnitCubeBlockCoarseProbability
        (unitCubeBlockCoupling anchorCoupling)
        (unitCubeBlockCoupling_nonnegative (by decide))
        cutoff volume := by
  exact Q'.le_trans' _ _ _
    activityMatchedUnitCubeUniformOccurrenceFloor_le_coarse
    (activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_blockCoarseProbability
      hcutoff hvolume)

theorem uniformFloor_le_activityMatchedRefinedBlockProbability_allCutoff
    {cutoff volume : Nat} (hcutoff : 1 ≤ cutoff)
    (hvolume : 4 ≤ volume) :
    activityMatchedUnitCubeUniformOccurrenceFloor ≤
      couplingKUnitCubeBlockRefinedProbability
        anchorCoupling (by decide) cutoff volume := by
  have hcompatible :=
    dyadicUnitCubeUniformOccurrenceFloor_le_parametricK_probability
      hcutoff hvolume
  have hphysical :=
    couplingKFamilyEventProbability_anchor_eqv_compatible
      cutoff volume
      (familyContainsPolymerB (dyadicUnitCubeSupportIdsAt volume))
  unfold couplingKUnitCubeBlockRefinedProbability
  rw [unitCubeBlock_targetRefined_eq_occurrence]
  exact Q'.le_trans' _ _ _
    activityMatchedUnitCubeUniformOccurrenceFloor_le_refined
    (Q'.le_trans' _ _ _ hcompatible (Q'.ge_of_eqv hphysical))

/-! ## 2. Uniform separation of the activity-matched block laws -/

/-- At every cutoff at least one, the production activity-matched block
defect is bounded by `1 - epsilon`, where `epsilon` is the same explicit
positive exact rational used in the cutoff-one theorem. -/
theorem activityMatchedUnitCubeBlockDefect_le_uniformBound_allCutoff
    {cutoff volume : Nat} (hcutoff : 1 ≤ cutoff)
    (hvolume : 4 ≤ volume) :
    activityMatchedUnitCubeBlockDefect
        anchorCoupling (by decide) cutoff volume ≤
      activityMatchedUnitCubeUniformDefectBound := by
  unfold activityMatchedUnitCubeBlockDefect
    couplingKUnitCubeBlockDefect
    activityMatchedUnitCubeUniformDefectBound
  exact abs_difference_le_one_sub_floor
    (uniformFloor_le_activityMatchedCoarseBlockProbability_allCutoff
      hcutoff hvolume)
    (uniformFloor_le_activityMatchedRefinedBlockProbability_allCutoff
      hcutoff hvolume)
    (couplingKUnitCubeBlockCoarseProbability_le_one
      (unitCubeBlockCoupling anchorCoupling)
      (unitCubeBlockCoupling_nonnegative (by decide)) cutoff volume)
    (couplingKUnitCubeBlockRefinedProbability_le_one
      anchorCoupling (by decide) cutoff volume)

/-- The requested two-part all-cutoff estimate, packaged without hiding the
strict positive margin behind transitivity. -/
theorem activityMatchedUnitCubeBlockDefect_uniformBound_and_lt_one_allCutoff
    {cutoff volume : Nat} (hcutoff : 1 ≤ cutoff)
    (hvolume : 4 ≤ volume) :
    activityMatchedUnitCubeBlockDefect
          anchorCoupling (by decide) cutoff volume ≤
        activityMatchedUnitCubeUniformDefectBound ∧
      activityMatchedUnitCubeUniformDefectBound < (1 : Q') := by
  exact ⟨
    activityMatchedUnitCubeBlockDefect_le_uniformBound_allCutoff
      hcutoff hvolume,
    activityMatchedUnitCubeUniformDefectBound_lt_one⟩

theorem activityMatchedUnitCubeBlockDefect_uniform_lt_one_allCutoff
    {cutoff volume : Nat} (hcutoff : 1 ≤ cutoff)
    (hvolume : 4 ≤ volume) :
    activityMatchedUnitCubeBlockDefect
        anchorCoupling (by decide) cutoff volume < (1 : Q') :=
  Q'.lt_of_le_of_lt
    (activityMatchedUnitCubeBlockDefect_le_uniformBound_allCutoff
      hcutoff hvolume)
    activityMatchedUnitCubeUniformDefectBound_lt_one

#print axioms uniformFloor_le_activityMatchedCoarseBlockProbability_allCutoff
#print axioms uniformFloor_le_activityMatchedRefinedBlockProbability_allCutoff
#print axioms activityMatchedUnitCubeBlockDefect_le_uniformBound_allCutoff
#print axioms activityMatchedUnitCubeBlockDefect_uniformBound_and_lt_one_allCutoff
#print axioms activityMatchedUnitCubeBlockDefect_uniform_lt_one_allCutoff

end YMGap.Continuum.Z4AllCutoffActivityMatchedDefectFloor
