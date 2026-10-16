/-
# Finite-volume length bound for matched all-cutoff block trajectories

The exact dyadic slab geometry in `SlabScalePair` points from a larger fine
slab to a smaller coarse slab.  Written in half-size coordinates, every step
satisfies

  fine.half = 2 * coarse.half + 1.

Consequently a matched trajectory at fixed initial finite volume cannot have
arbitrary length.  This module proves the stronger invariant

  stepCount + finalCoarseHalf <= initialFineHalf.

Thus the continuum iteration cannot be represented by one infinite matched
finite-volume trajectory.  It must use a cofinal family of finite trajectories
whose initial fine volumes grow, together with bounds uniform over that family.

Constructive contract: definitional geometry and natural-number arithmetic
only; no choice, `Classical`, `native_decide`, `sorry`, noncomputable
declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingRemainderSplit

namespace YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingTrajectoryFiniteVolume

set_option autoImplicit false

open YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingIteration
open YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingIteration.AllCutoffOriginalActionTrajectory
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.Z4DyadicSlabReflectionParityKernel
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. Exact half-size reduction in one block step -/

theorem scalePair_fine_half_eq_two_coarse_add_one
    (S : SlabScalePair) :
    S.fine.half = 2 * S.coarse.half + 1 := by
  have hextent := S.fine_extent
  unfold SlabPhysicalData.extent centralExtent
    dyadicSlabFineExtent at hextent
  omega

theorem scalePair_coarse_half_lt_fine_half
    (S : SlabScalePair) :
    S.coarse.half < S.fine.half := by
  have hhalf := scalePair_fine_half_eq_two_coarse_add_one S
  omega

/-! ## 2. Every fixed-volume matched trajectory has bounded length -/

namespace AllCutoffOriginalActionTrajectory

def firstStep : AllCutoffOriginalActionTrajectory →
    AllCutoffOriginalActionStep
  | .single step => step
  | .append prior _ => firstStep prior

def stepCount : AllCutoffOriginalActionTrajectory → Nat
  | .single _ => 1
  | .append prior _ => stepCount prior + 1

/-- Each consumed block step uses at least one unit of the initial fine
half-size budget. -/
theorem stepCount_add_lastCoarseHalf_le_firstFineHalf
    (trajectory : AllCutoffOriginalActionTrajectory)
    (hmatched : Matched trajectory) :
    stepCount trajectory +
        (lastStep trajectory).pair.coarse.half ≤
      (firstStep trajectory).pair.fine.half := by
  induction trajectory with
  | single step =>
      change 1 + step.pair.coarse.half ≤ step.pair.fine.half
      have hdecrease :=
        scalePair_coarse_half_lt_fine_half step.pair
      omega
  | append prior next ih =>
      change Matched prior ∧
        (lastStep prior).pair.coarse = next.pair.fine at hmatched
      rcases hmatched with ⟨hpriorMatched, hmatch⟩
      have hprior := ih hpriorMatched
      have hnext := scalePair_coarse_half_lt_fine_half next.pair
      have hhalfMatch :
          (lastStep prior).pair.coarse.half = next.pair.fine.half :=
        congrArg (fun data : SlabPhysicalData => data.half) hmatch
      change stepCount prior + 1 + next.pair.coarse.half ≤
        (firstStep prior).pair.fine.half
      omega

/-- In particular, no matched trajectory beginning at one fixed finite slab
can contain more block steps than its initial fine half-size. -/
theorem stepCount_le_firstFineHalf
    (trajectory : AllCutoffOriginalActionTrajectory)
    (hmatched : Matched trajectory) :
    stepCount trajectory ≤
      (firstStep trajectory).pair.fine.half := by
  have hbudget :=
    stepCount_add_lastCoarseHalf_le_firstFineHalf trajectory hmatched
  omega

end AllCutoffOriginalActionTrajectory

/-! ## Axiom audit -/

#print axioms scalePair_fine_half_eq_two_coarse_add_one
#print axioms scalePair_coarse_half_lt_fine_half
#print axioms AllCutoffOriginalActionTrajectory.firstStep
#print axioms AllCutoffOriginalActionTrajectory.stepCount
#print axioms AllCutoffOriginalActionTrajectory.stepCount_add_lastCoarseHalf_le_firstFineHalf
#print axioms AllCutoffOriginalActionTrajectory.stepCount_le_firstFineHalf

end YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingTrajectoryFiniteVolume
