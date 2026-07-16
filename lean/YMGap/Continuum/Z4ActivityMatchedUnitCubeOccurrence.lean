/-
# Non-vacuity of the activity-matched unit-cube block law

The coarse six-face root is transported into the common box-four block
presentation and then into every larger finite volume.  Its activity at the
derived coupling `2*w^4` is exactly the activity of the transported refined
24-face root at coupling `w`.  At positive coupling both coordinates
therefore have strictly positive probability at every physical cutoff at
least one.

As a first genuinely nontrivial defect consequence, the exact finite block
defect is strictly smaller than one.  No volume-independent distance from one
is claimed here; that quantitative strengthening is the deletion/KP task.
-/

import YMGap.Continuum.CubeRatioBounds
import YMGap.Continuum.Z4ParametricCanonicalRootOccurrence

namespace YMGap.Continuum.Z4ActivityMatchedUnitCubeOccurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CoarseUnitCubeActivity
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicUnitCubeActivity
open YMGap.Continuum.Z4DyadicUnitCubeBlockCylinderIntertwining
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4ParametricCanonicalRootOccurrence
open YMGap.Continuum.Z4UnitCubeBareCouplingShift

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The two transported block roots -/

/-- The coarse root in the common box-four presentation, transported onward
to the target finite volume. -/
def coarseUnitCubeBlockRootAt (volume : Nat) : List Nat :=
  transportPolymer 4 volume
    (transportPolymer 2 4 coarseUnitCubeSupportIds)

theorem coarseUnitCubeBlockRootAt_mem_canonicalSurfacePolymers
    {volume : Nat} (hvolume : 4 ≤ volume) :
    coarseUnitCubeBlockRootAt volume ∈ canonicalSurfacePolymers volume := by
  unfold coarseUnitCubeBlockRootAt
  apply transportPolymer_mem_canonicalSurfacePolymers hvolume
  exact transportPolymer_mem_canonicalSurfacePolymers (by omega)
    coarseUnitCubeSupportIds_mem_canonicalSurfacePolymers

theorem unitCubeBlock_targetCoarse_eq_occurrence (volume : Nat) :
    targetCylinderEvent 4 volume unitCubeBlockCylinderRoots
        unitCubeBlockCoarseOccurrencePredicate =
      familyContainsPolymerB (coarseUnitCubeBlockRootAt volume) := by
  rw [unitCubeBlock_targetCoarse_eq_singleton]
  rfl

theorem unitCubeBlock_targetRefined_eq_occurrence (volume : Nat) :
    targetCylinderEvent 4 volume unitCubeBlockCylinderRoots
        unitCubeBlockRefinedOccurrencePredicate =
      familyContainsPolymerB (dyadicUnitCubeSupportIdsAt volume) := by
  rw [unitCubeBlock_targetRefined_eq_singleton]
  rfl

/-! ## 2. Exact activity matching after arbitrary containing-volume transport -/

theorem coarseUnitCubeBlockRootAt_activity_eqv_base
    (coupling : Q') {volume : Nat} (hvolume : 4 ≤ volume) :
    canonicalSurfaceActivity coupling volume
        (coarseUnitCubeBlockRootAt volume) ≈
      canonicalSurfaceActivity coupling 2
        coarseUnitCubeSupportIds := by
  have hcoarseSupport : coarseUnitCubeSupportIds ∈
      cutoffOneFaceSupports 2 :=
    canonicalSurfacePolymer_mem_faceSupports
      coarseUnitCubeSupportIds_mem_canonicalSurfacePolymers
  have hrootFour : transportPolymer 2 4 coarseUnitCubeSupportIds ∈
      canonicalSurfacePolymers 4 :=
    transportPolymer_mem_canonicalSurfacePolymers (by omega)
      coarseUnitCubeSupportIds_mem_canonicalSurfacePolymers
  have hfirst := canonicalSurfaceActivity_transport coupling
    (n := 2) (m := 4) (by omega) hcoarseSupport
  have hsecond := canonicalSurfaceActivity_transport coupling
    (n := 4) (m := volume) hvolume
    (canonicalSurfacePolymer_mem_faceSupports hrootFour)
  unfold coarseUnitCubeBlockRootAt
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hsecond)
    (Q'.eqv_symm hfirst)

theorem dyadicUnitCubeSupportIdsAt_activity_eqv_base
    (coupling : Q') {volume : Nat} (hvolume : 4 ≤ volume) :
    canonicalSurfaceActivity coupling 4 dyadicUnitCubeSupportIds ≈
      canonicalSurfaceActivity coupling volume
        (dyadicUnitCubeSupportIdsAt volume) := by
  unfold dyadicUnitCubeSupportIdsAt
  exact canonicalSurfaceActivity_transport coupling hvolume
    dyadicUnitCubeSupportIds_mem_cutoffOneFaceSupports

/-- The exact bare activity identity survives both canonical transports into
the common target volume. -/
theorem transported_activityMatched_rootActivities_eqv
    (fineCoupling : Q') {volume : Nat} (hvolume : 4 ≤ volume) :
    canonicalSurfaceActivity (unitCubeBlockCoupling fineCoupling) volume
        (coarseUnitCubeBlockRootAt volume) ≈
      canonicalSurfaceActivity fineCoupling volume
        (dyadicUnitCubeSupportIdsAt volume) := by
  exact Q'.eqv_trans _ _ _
    (coarseUnitCubeBlockRootAt_activity_eqv_base
      (unitCubeBlockCoupling fineCoupling) hvolume)
    (Q'.eqv_trans _ _ _
      (coarse_shifted_activity_eqv_dyadic_activity fineCoupling)
      (dyadicUnitCubeSupportIdsAt_activity_eqv_base
        fineCoupling hvolume))

theorem coarseUnitCubeBlockRootAt_shiftedActivity_pos
    {fineCoupling : Q'} (hfine : (0 : Q') < fineCoupling)
    {volume : Nat} (hvolume : 4 ≤ volume) :
    (0 : Q') <
      canonicalSurfaceActivity (unitCubeBlockCoupling fineCoupling) volume
        (coarseUnitCubeBlockRootAt volume) := by
  exact Q'.pos_of_lt_of_le
    (coarse_shifted_activity_pos hfine)
    (Q'.ge_of_eqv
      (coarseUnitCubeBlockRootAt_activity_eqv_base
        (unitCubeBlockCoupling fineCoupling) hvolume))

theorem dyadicUnitCubeSupportIdsAt_activity_pos
    {fineCoupling : Q'} (hfine : (0 : Q') < fineCoupling)
    {volume : Nat} (hvolume : 4 ≤ volume) :
    (0 : Q') < canonicalSurfaceActivity fineCoupling volume
      (dyadicUnitCubeSupportIdsAt volume) :=
  Q'.pos_of_lt_of_le
    (dyadicUnitCube_canonicalSurfaceActivity_pos hfine)
    (Q'.le_of_eqv
      (dyadicUnitCubeSupportIdsAt_activity_eqv_base
        fineCoupling hvolume))

/-! ## 3. Positive coarse and refined coordinates -/

theorem couplingKUnitCubeBlockCoarseProbability_eq_occurrence
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) :
    couplingKUnitCubeBlockCoarseProbability
        coupling hcoupling cutoff volume =
      couplingKCanonicalPolymerOccurrenceProbability
        coupling hcoupling cutoff volume
          (coarseUnitCubeBlockRootAt volume) := by
  unfold couplingKUnitCubeBlockCoarseProbability
    couplingKCanonicalPolymerOccurrenceProbability
  rw [unitCubeBlock_targetCoarse_eq_occurrence]

theorem couplingKUnitCubeBlockRefinedProbability_eq_occurrence
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) :
    couplingKUnitCubeBlockRefinedProbability
        coupling hcoupling cutoff volume =
      couplingKCanonicalPolymerOccurrenceProbability
        coupling hcoupling cutoff volume
          (dyadicUnitCubeSupportIdsAt volume) := by
  unfold couplingKUnitCubeBlockRefinedProbability
    couplingKCanonicalPolymerOccurrenceProbability
  rw [unitCubeBlock_targetRefined_eq_occurrence]

theorem activityMatchedUnitCubeBlockCoarseProbability_pos
    {fineCoupling : Q'} (hfine0 : (0 : Q') ≤ fineCoupling)
    (hfine : (0 : Q') < fineCoupling)
    {cutoff volume : Nat} (hcutoff : 1 ≤ cutoff)
    (hvolume : 4 ≤ volume) :
    (0 : Q') < couplingKUnitCubeBlockCoarseProbability
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine0) cutoff volume := by
  rw [couplingKUnitCubeBlockCoarseProbability_eq_occurrence]
  exact couplingKCanonicalPolymerOccurrenceProbability_pos_of_activity
    (unitCubeBlockCoupling_nonnegative hfine0) hcutoff
    (coarseUnitCubeBlockRootAt_mem_canonicalSurfacePolymers hvolume)
    (coarseUnitCubeBlockRootAt_shiftedActivity_pos hfine hvolume)

theorem activityMatchedUnitCubeBlockRefinedProbability_pos
    {fineCoupling : Q'} (hfine0 : (0 : Q') ≤ fineCoupling)
    (hfine : (0 : Q') < fineCoupling)
    {cutoff volume : Nat} (hcutoff : 1 ≤ cutoff)
    (hvolume : 4 ≤ volume) :
    (0 : Q') < couplingKUnitCubeBlockRefinedProbability
      fineCoupling hfine0 cutoff volume := by
  rw [couplingKUnitCubeBlockRefinedProbability_eq_occurrence]
  exact couplingKCanonicalPolymerOccurrenceProbability_pos_of_activity
    hfine0 hcutoff
    (dyadicUnitCubeSupportIdsAt_mem_canonicalSurfacePolymers hvolume)
    (dyadicUnitCubeSupportIdsAt_activity_pos hfine hvolume)

/-! ## 4. A strict finite-volume defect fence -/

private theorem abs_difference_lt_one_of_pos_le_one
    {left right : Q'}
    (hleft0 : (0 : Q') < left) (hleft1 : left ≤ (1 : Q'))
    (hright0 : (0 : Q') < right) (hright1 : right ≤ (1 : Q')) :
    Q'.abs (left + -right) < (1 : Q') := by
  unfold Q'.abs
  by_cases hdiff : (0 : Q') ≤ left + -right
  · rw [if_pos hdiff]
    exact YMGap.Continuum.CubeRatioBounds.q_lt_of_lt_of_le
      (YMGap.Continuum.CubeRatioBounds.sub_lt_self_of_pos hright0)
      hleft1
  · rw [if_neg hdiff]
    have hswap : -(left + -right) ≈ right + -left := by
      exact Q'.eqv_trans _ _ _
        (Q'.neg_add_eqv left (-right))
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left (-left) _ _
            (Q'.neg_neg_eqv right))
          (Q'.add_comm_eqv (-left) right))
    have hrightMinusLeft : right + -left < (1 : Q') :=
      YMGap.Continuum.CubeRatioBounds.q_lt_of_lt_of_le
        (YMGap.Continuum.CubeRatioBounds.sub_lt_self_of_pos hleft0)
        hright1
    exact Q'.lt_of_le_of_lt (Q'.le_of_eqv hswap) hrightMinusLeft

/-- Positive coupling makes both activity-matched coordinates non-vacuous,
so their exact finite-volume discrepancy cannot attain the universal value
one.  A uniform quantitative margin remains open. -/
theorem activityMatchedUnitCubeBlockDefect_lt_one
    {fineCoupling : Q'} (hfine0 : (0 : Q') ≤ fineCoupling)
    (hfine : (0 : Q') < fineCoupling)
    {cutoff volume : Nat} (hcutoff : 1 ≤ cutoff)
    (hvolume : 4 ≤ volume) :
    activityMatchedUnitCubeBlockDefect
        fineCoupling hfine0 cutoff volume < (1 : Q') := by
  unfold activityMatchedUnitCubeBlockDefect
    couplingKUnitCubeBlockDefect
  exact abs_difference_lt_one_of_pos_le_one
    (activityMatchedUnitCubeBlockCoarseProbability_pos
      hfine0 hfine hcutoff hvolume)
    (couplingKUnitCubeBlockCoarseProbability_le_one
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine0) cutoff volume)
    (activityMatchedUnitCubeBlockRefinedProbability_pos
      hfine0 hfine hcutoff hvolume)
    (couplingKUnitCubeBlockRefinedProbability_le_one
      fineCoupling hfine0 cutoff volume)

#print axioms coarseUnitCubeBlockRootAt_mem_canonicalSurfacePolymers
#print axioms unitCubeBlock_targetCoarse_eq_occurrence
#print axioms transported_activityMatched_rootActivities_eqv
#print axioms activityMatchedUnitCubeBlockCoarseProbability_pos
#print axioms activityMatchedUnitCubeBlockRefinedProbability_pos
#print axioms activityMatchedUnitCubeBlockDefect_lt_one

end YMGap.Continuum.Z4ActivityMatchedUnitCubeOccurrence
