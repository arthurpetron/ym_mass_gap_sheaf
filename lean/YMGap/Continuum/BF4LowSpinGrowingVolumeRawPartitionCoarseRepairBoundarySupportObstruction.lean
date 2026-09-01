/-
# Boundary-support obstruction to the growing-reference posterior floor

The coarse growing repair requires the fixed slice-zero spin-one marginal to
be bounded by a common multiple of the posterior probability of one selected
growing-volume low-spin reference state at every retained positive boundary.
This module isolates the exact finite witness that refutes that producer:

* a retained boundary channel;
* strictly positive total retained half-amplitude at that channel; and
* zero half-amplitude for the selected growing reference state.

The selected posterior is then exactly zero, while the fixed spin-one
marginal is strictly positive at every positive coupling and cutoff at least
one.  Hence no finite posterior-floor ceiling works at that scale.  The same
witness also refutes the division-free positive-boundary cross-bound, and one
matched-scale witness refutes the corresponding all-scale matched packages.

This is a no-go compiler, not an inhabitant of the support-mismatch data.  The
remaining geometric task is to construct such a retained boundary or else
prove that the selected reference has sufficiently uniform support.  No
cofinal gap, continuum limit, or Clay conclusion is asserted.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairBoundaryPosterior

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairBoundarySupportObstruction

set_option maxRecDepth 500000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4DyadicCubeVacuumCalibration
open YMGap.Continuum.BF4LowSpinGrowingVolumePositiveRawReplication
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairBoundaryPosterior
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairPositiveBoundaryAmplitude
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4PhysicalBoundaryPosterior
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact finite support-mismatch witness -/

/-- A retained positive boundary on which the selected growing-volume
reference half-amplitude vanishes. -/
structure CoarseGrowingReferenceBoundarySupportMismatch
    (w : Q') (hw : (0 : Q') < w) (K : Nat) (hK : 1 ≤ K)
    (volume : Nat) : Type where
  boundary : EdgeLabelling
  boundary_mem :
    boundary ∈ centralBoundaryChannels K (volume + 1)
  positive_total :
    (0 : Q') <
      centralPositiveBoundaryTotalHalfAmplitude
        w (Q'.le_of_lt hw) K (volume + 1) boundary
  reference_amplitude_zero :
    centralHalfAmplitude
        w K (volume + 1)
        (lowSpinCentralReferenceState volume) boundary ≈
      0

/-- At a support-mismatch boundary, the selected reference posterior is
exactly zero. -/
theorem CoarseGrowingReferenceBoundarySupportMismatch.referencePosterior_eqv_zero
    {w : Q'} {hw : (0 : Q') < w} {K : Nat} {hK : 1 ≤ K}
    {volume : Nat}
    (mismatch : CoarseGrowingReferenceBoundarySupportMismatch
      w hw K hK volume) :
    centralTargetGivenBoundary
        w (Q'.le_of_lt hw) K (volume + 1)
        mismatch.boundary mismatch.positive_total
        (lowSpinCentralReferenceState volume) ≈
      0 := by
  unfold centralTargetGivenBoundary finiteStateGivenChannel Q'.divPos
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ 0 _
      mismatch.reference_amplitude_zero)
    (Q'.zero_mul_eqv _)

/-- A single retained support mismatch refutes every finite ceiling for the
growing-reference posterior-floor producer at that scale. -/
theorem CoarseGrowingReferenceBoundarySupportMismatch.noReferenceBoundaryPosteriorFloor
    {w : Q'} {hw : (0 : Q') < w} {K : Nat} {hK : 1 ≤ K}
    {volume : Nat}
    (mismatch : CoarseGrowingReferenceBoundarySupportMismatch
      w hw K hK volume)
    (ceiling : Q') :
    CoarseGrowingReferenceBoundaryPosteriorFloor
        w hw K hK volume ceiling → False := by
  intro bound
  have hfloor := bound.reference_posterior_floor
    mismatch.boundary mismatch.boundary_mem mismatch.positive_total
  have hposteriorZero := mismatch.referencePosterior_eqv_zero
  have hscaledZero :
      ceiling *
          centralTargetGivenBoundary
            w (Q'.le_of_lt hw) K (volume + 1)
            mismatch.boundary mismatch.positive_total
            (lowSpinCentralReferenceState volume) ≈
        0 := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left ceiling _ _ hposteriorZero)
      (Q'.mul_zero_eqv ceiling)
  have hnonpositive :
      centralPhysicalRowMarginal
          w (Q'.le_of_lt hw) K 0
          (centralLowerSpinCubeState 1) ≤
        0 :=
    Q'.le_trans' _ _ _ hfloor (Q'.le_of_eqv hscaledZero)
  have hpositive :
      (0 : Q') <
        centralPhysicalRowMarginal
          w (Q'.le_of_lt hw) K 0
          (centralLowerSpinCubeState 1) :=
    centralLowerSpinCubeRowMarginal_pos hw hK
  exact (Int.not_lt_of_ge hnonpositive) hpositive

/-- The same witness refutes the division-free positive-boundary amplitude
cross-bound whenever its ceiling has the normalization needed for the exact
posterior translation. -/
theorem CoarseGrowingReferenceBoundarySupportMismatch.noPositiveBoundaryHalfAmplitudeCrossBound
    {w : Q'} {hw : (0 : Q') < w} {K : Nat} {hK : 1 ≤ K}
    {volume : Nat}
    (mismatch : CoarseGrowingReferenceBoundarySupportMismatch
      w hw K hK volume)
    (ceiling : Q') (hone : (1 : Q') ≤ ceiling) :
    CoarseGrowingPositiveBoundaryHalfAmplitudeCrossBound
        w hw K hK volume ceiling → False := by
  intro bound
  exact mismatch.noReferenceBoundaryPosteriorFloor ceiling
    (CoarseGrowingPositiveBoundaryHalfAmplitudeCrossBound.toReferenceBoundaryPosteriorFloor
      bound hone)

/-! ## 2. One-scale obstruction to matched all-scale packages -/

/-- A support mismatch at one scale of a matched physical trajectory. -/
structure MatchedDyadicCoarseGrowingReferenceBoundarySupportMismatch
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (bridge : MatchedDyadicSameActionAFBridge
      family law spacing coupling) : Type where
  scale : Nat
  mismatch :
    CoarseGrowingReferenceBoundarySupportMismatch
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_pos family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
      (one_le_matchedAllSpinCutoff bridge scale)
      scale

/-- One matched-scale support mismatch refutes an all-scale common posterior
floor. -/
theorem MatchedDyadicCoarseGrowingReferenceBoundarySupportMismatch.noReferenceBoundaryPosteriorFloor
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge : MatchedDyadicSameActionAFBridge
      family law spacing coupling}
    (obstruction :
      MatchedDyadicCoarseGrowingReferenceBoundarySupportMismatch bridge) :
    MatchedDyadicCoarseGrowingReferenceBoundaryPosteriorFloor bridge → False := by
  intro bound
  exact obstruction.mismatch.noReferenceBoundaryPosteriorFloor
    bound.ceiling (bound.posteriorFloor obstruction.scale)

/-- One matched-scale support mismatch also refutes the normalized
positive-boundary amplitude package. -/
theorem MatchedDyadicCoarseGrowingReferenceBoundarySupportMismatch.noPositiveBoundaryHalfAmplitudeCrossBound
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge : MatchedDyadicSameActionAFBridge
      family law spacing coupling}
    (obstruction :
      MatchedDyadicCoarseGrowingReferenceBoundarySupportMismatch bridge) :
    MatchedDyadicCoarseGrowingPositiveBoundaryHalfAmplitudeCrossBound
        bridge → False := by
  intro bound
  exact obstruction.mismatch.noPositiveBoundaryHalfAmplitudeCrossBound
    bound.ceiling bound.one_le_ceiling
    (bound.positiveBoundaryBound obstruction.scale)

end YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairBoundarySupportObstruction

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairBoundarySupportObstruction.CoarseGrowingReferenceBoundarySupportMismatch.referencePosterior_eqv_zero
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairBoundarySupportObstruction.CoarseGrowingReferenceBoundarySupportMismatch.noReferenceBoundaryPosteriorFloor
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairBoundarySupportObstruction.CoarseGrowingReferenceBoundarySupportMismatch.noPositiveBoundaryHalfAmplitudeCrossBound
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairBoundarySupportObstruction.MatchedDyadicCoarseGrowingReferenceBoundarySupportMismatch.noReferenceBoundaryPosteriorFloor
