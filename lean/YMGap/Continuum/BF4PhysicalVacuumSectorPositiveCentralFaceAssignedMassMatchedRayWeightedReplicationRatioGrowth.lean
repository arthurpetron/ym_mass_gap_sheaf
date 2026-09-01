/-
# Weighted ray replication forces assigned-ratio growth

The calibrated matched tail requires

  1/6 <= assignedRatioCeiling * rayMass.

Weighted raw-row replication supplies `rayMass <= 1 / effectiveMultiplicity`.
This file closes the elementary but load-bearing feedback loop:

  (1/6) * effectiveMultiplicity <= assignedRatioCeiling.

Thus a replica construction with divergent effective multiplicity cannot be
compatible with a cutoff-uniform assigned-ratio ceiling.  The theorem is
quantitative at every finite cutoff and along the matched family; it does not
construct the missing replicas or claim ray-mass decay.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayWeightedReplicationGate
import YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedTailGate

namespace YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayWeightedReplicationRatioGrowth

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4DyadicCubeVacuumCalibration
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorStationaryPosterior
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassAggregateGate
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedCofinalGate
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayWeightedReplicationGate
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedTailGate
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassReturnReduction
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Finite quantitative feedback -/

/-- The algebraic feedback step: any `1/6 <= ceiling * rayMass` bound and any
weighted replication force the ceiling to pay one sixth of the effective
multiplicity. -/
theorem oneSixth_mul_effectiveMultiplicity_le_finiteCeiling_of_productFloor
    {w : Q'} (hw0 : (0 : Q') < w) (K : Nat)
    (replication :
      CentralLowerExcitedSpinCubeWeightedRawReplication w hw0 K)
    (hproductFloor :
      Q'.mkPos 1 6 (by decide) ≤
        positiveCentralFaceAssignedStationaryRatioFiniteCeiling hw0 K *
          centralLowerExcitedSpinCubeRayMass
            w (Q'.le_of_lt hw0) K) :
    Q'.mkPos 1 6 (by decide) * replication.effectiveMultiplicity ≤
      positiveCentralFaceAssignedStationaryRatioFiniteCeiling hw0 K := by
  let ceiling :=
    positiveCentralFaceAssignedStationaryRatioFiniteCeiling hw0 K
  let rayMass :=
    centralLowerExcitedSpinCubeRayMass w (Q'.le_of_lt hw0) K
  let effective := replication.effectiveMultiplicity
  let heffective : (0 : Q') < effective :=
    replication.effectiveMultiplicity_pos
  let reciprocal := Q'.divPos 1 effective heffective
  have hfloor : Q'.mkPos 1 6 (by decide) ≤ ceiling * rayMass :=
    hproductFloor
  have hray : rayMass ≤ reciprocal :=
    replication.rayMass_le_reciprocalEffectiveMultiplicity
  have hceiling : (0 : Q') ≤ ceiling :=
    positiveCentralFaceAssignedStationaryRatioFiniteCeiling_nonnegative hw0 K
  have hscaled : ceiling * rayMass ≤ ceiling * reciprocal :=
    Q'.mul_le_mul_of_nonneg_left _ _ ceiling hray hceiling
  have hdivBound :
      Q'.mkPos 1 6 (by decide) ≤ ceiling * reciprocal :=
    Q'.le_trans' _ _ _ hfloor hscaled
  have hmul := Q'.mul_le_mul_of_nonneg_right _ _ effective
    hdivBound (Q'.le_of_lt heffective)
  have hcollapse : (ceiling * reciprocal) * effective ≈ ceiling := by
    unfold reciprocal Q'.divPos
    refine Q'.eqv_trans _
      ((ceiling * Q'.recipPos effective heffective) * effective) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ effective
        (Q'.mul_eqv_congr_left ceiling _ _
          (Q'.one_mul_eqv (Q'.recipPos effective heffective)))
    · refine Q'.eqv_trans _
        (ceiling *
          (Q'.recipPos effective heffective * effective)) _
        (Q'.mul_assoc_eqv _ _ _) ?_
      refine Q'.eqv_trans _
        (ceiling *
          (effective * Q'.recipPos effective heffective)) _
        (Q'.mul_eqv_congr_left ceiling _ _
          (Q'.mul_comm_eqv
            (Q'.recipPos effective heffective) effective)) ?_
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left ceiling _ _
          (Q'.mul_recipPos_eqv effective heffective))
        (Q'.mul_one_eqv ceiling)
  exact Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hcollapse)

/-- At one calibrated finite cutoff, weighted replication forces the sharp
assigned-ratio ceiling to pay one sixth of its effective multiplicity. -/
theorem oneSixth_mul_effectiveMultiplicity_le_finiteCeiling
    {w : Q'} (hw0 : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    (replication :
      CentralLowerExcitedSpinCubeWeightedRawReplication w hw0 K)
    (hvacuum :
      centralPhysicalRowMarginal
          w (Q'.le_of_lt hw0) K 0 zeroEdgeLabelling ≤
        Q'.mkPos 5 6 (by decide)) :
    Q'.mkPos 1 6 (by decide) * replication.effectiveMultiplicity ≤
      positiveCentralFaceAssignedStationaryRatioFiniteCeiling hw0 K := by
  exact
    oneSixth_mul_effectiveMultiplicity_le_finiteCeiling_of_productFloor
      hw0 K replication
      (oneSixth_le_finiteCeiling_mul_rayMass_of_vacuumMass_le_fiveSixths
        hw0 hK hvacuum)

/-! ## 2. Matched specialization -/

/-- Every calibrated matched finite scale obeys the same explicit growth
lower bound. -/
theorem oneSixth_mul_matchedEffectiveMultiplicity_le_finiteCeiling
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling)
    {scale : Nat} (hscale : 2 ≤ scale)
    (replication :
      CentralLowerExcitedSpinCubeWeightedRawReplication
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_pos family coupling scale)
        (matchedAllSpinCutoff family coupling scale)) :
    Q'.mkPos 1 6 (by decide) * replication.effectiveMultiplicity ≤
      positiveCentralFaceAssignedStationaryRatioFiniteCeiling
        (matchedAllSpinWeight_pos family coupling scale)
        (matchedAllSpinCutoff family coupling scale) := by
  exact
    oneSixth_mul_effectiveMultiplicity_le_finiteCeiling_of_productFloor
      (matchedAllSpinWeight_pos family coupling scale)
      (matchedAllSpinCutoff family coupling scale) replication
      (oneSixth_le_matchedAssignedRatioFiniteCeiling_mul_rayMass_tail
        bridge hscale)

/-! ## 3. Consequence for a proposed cofinal ratio bound -/

/-- If a common matched assigned-ratio bound and a weighted replication both
exist at a late scale, the common bound is at least one sixth of that scale's
effective multiplicity. -/
theorem oneSixth_mul_effectiveMultiplicity_le_cofinalRatioBound
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (ratio :
      MatchedDyadicCofinalPositiveCentralFaceAssignedStationaryRatio bridge)
    (scale : Nat) (hscale : ratio.start ≤ scale)
    (replication :
      CentralLowerExcitedSpinCubeWeightedRawReplication
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_pos family coupling scale)
        (matchedAllSpinCutoff family coupling scale)) :
    Q'.mkPos 1 6 (by decide) * replication.effectiveMultiplicity ≤
      ratio.ratioBound := by
  exact Q'.le_trans' _ _ _
    (oneSixth_mul_matchedEffectiveMultiplicity_le_finiteCeiling
      bridge (Nat.le_trans ratio.start_tail hscale) replication)
    (ratio.finiteCeiling_le_ratioBound scale hscale)

end YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayWeightedReplicationRatioGrowth

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayWeightedReplicationRatioGrowth.oneSixth_mul_effectiveMultiplicity_le_finiteCeiling_of_productFloor
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayWeightedReplicationRatioGrowth.oneSixth_mul_effectiveMultiplicity_le_finiteCeiling
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayWeightedReplicationRatioGrowth.oneSixth_mul_matchedEffectiveMultiplicity_le_finiteCeiling
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayWeightedReplicationRatioGrowth.oneSixth_mul_effectiveMultiplicity_le_cofinalRatioBound
