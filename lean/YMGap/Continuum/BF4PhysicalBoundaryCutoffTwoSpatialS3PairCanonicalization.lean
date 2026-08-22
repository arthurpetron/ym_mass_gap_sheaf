/-
# Physical-kernel transport to cutoff-two spatial S3 pair representatives

The finite canonicalizer chooses a least-code unordered pair in each orbit of
the checked six-element spatial action.  This module transports the genuine
production reflected kernel first across the spatial action and then, when
needed, across kernel symmetry to the normalized unordered representative.

This remains a cutoff-two equality.  It introduces no spectral, uniform-cutoff,
completion, thermodynamic-limit, or continuum claim.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3PairCanonicalizationData
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSKernelSymmetry

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3PairCanonicalization

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorRowClosure
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialAxisKernelInvariance
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3KernelAction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3PairCanonicalizationData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSKernelSymmetry

local infix:50 " ≈ " => Q'.eqv

/-- Normalizing an unordered sector pair preserves the genuine reflected
kernel, using physical-kernel symmetry only in the reversed branch. -/
theorem centralPhysicalReflectedKernel_cutoffTwo_pairNormalize_eqv
    (pair : CutoffTwoSectorPair) :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        (cutoffTwoSectorStateAt pair.row)
        (cutoffTwoSectorStateAt pair.column) ≈
      centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        (cutoffTwoSectorStateAt
          (cutoffTwoSectorPairNormalize pair).row)
        (cutoffTwoSectorStateAt
          (cutoffTwoSectorPairNormalize pair).column) := by
  unfold cutoffTwoSectorPairNormalize
  by_cases horder : pair.row.val ≤ pair.column.val
  · simpa [horder] using
      (Q'.eqv_refl
        (centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
          (cutoffTwoSectorStateAt pair.row)
          (cutoffTwoSectorStateAt pair.column)))
  · simpa [horder] using
      (centralPhysicalReflectedKernel_symm cutoffTwoHalfCoupling
        (cutoffTwoCubeSectorState_mem_halfStates
          (cutoffTwoSectorStateAt_mem pair.row))
        (cutoffTwoCubeSectorState_mem_halfStates
          (cutoffTwoSectorStateAt_mem pair.column)))

/-- Applying any checked spatial action and then normalizing the resulting
unordered pair preserves the genuine reflected kernel.  Keeping the action
abstract prevents elaboration from reducing a concrete six-word fold. -/
theorem centralPhysicalReflectedKernel_cutoffTwo_pairActionNormalized_eqv
    (action : CutoffTwoSpatialS3) (pair : CutoffTwoSectorPair) :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        (cutoffTwoSectorStateAt pair.row)
        (cutoffTwoSectorStateAt pair.column) ≈
      centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        (cutoffTwoSectorStateAt
          (cutoffTwoSectorPairActionNormalized action pair).row)
        (cutoffTwoSectorStateAt
          (cutoffTwoSectorPairActionNormalized action pair).column) := by
  exact Q'.eqv_trans _ _ _
    (centralPhysicalReflectedKernel_cutoffTwo_spatialS3_eqv
      action pair.row pair.column)
    (by
      rw [cutoffTwoSectorPairActionNormalized]
      exact centralPhysicalReflectedKernel_cutoffTwo_pairNormalize_eqv
        (cutoffTwoSectorPairAction action pair))

/-- Every genuine cutoff-two physical-kernel entry equals the entry at its
deterministic least-code unordered spatial-S3 representative. -/
theorem centralPhysicalReflectedKernel_cutoffTwo_pairCanonical_eqv
    (pair : CutoffTwoSectorPair) :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        (cutoffTwoSectorStateAt pair.row)
        (cutoffTwoSectorStateAt pair.column) ≈
      centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        (cutoffTwoSectorStateAt
          (cutoffTwoSectorPairCanonical pair).row)
        (cutoffTwoSectorStateAt
          (cutoffTwoSectorPairCanonical pair).column) := by
  rw [cutoffTwoSectorPairCanonical]
  exact centralPhysicalReflectedKernel_cutoffTwo_pairActionNormalized_eqv
    (cutoffTwoSectorPairCanonicalAction pair) pair

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3PairCanonicalization

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3PairCanonicalization.centralPhysicalReflectedKernel_cutoffTwo_pairNormalize_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3PairCanonicalization.centralPhysicalReflectedKernel_cutoffTwo_pairActionNormalized_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3PairCanonicalization.centralPhysicalReflectedKernel_cutoffTwo_pairCanonical_eqv
