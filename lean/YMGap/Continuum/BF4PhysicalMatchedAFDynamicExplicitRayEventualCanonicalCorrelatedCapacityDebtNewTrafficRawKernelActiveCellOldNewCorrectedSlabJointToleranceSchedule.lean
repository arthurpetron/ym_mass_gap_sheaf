/-
# Old--new corrected-slab product: exact joint-tolerance schedule

The corrected-slab product lane must control one cutoff increment times the
same-cutoff observable-connected active-path/raw-capacity amplification.  The
arbitrary-nome slab tail theorem can do this at a requested positive tolerance.
For cutoff offset `k`, request

  invSqTerm k / (1 + jointAmplification k).

Because the amplification is nonnegative, multiplying this tolerance by the
amplification is at most the inverse-square target.  The remaining datum is a
literal natural-number schedule condition: the current consecutive cutoff has
already reached the retained cutoff requested by that joint tolerance.

This module proves that such schedule data inhabits the corrected-slab product
control with coefficient one.  It does not inhabit the schedule condition,
bound the amplification, solve its fixed-point dependence on the cutoff,
control mergers, construct a continuum theory, or prove the Clay claim.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or declaration
marked noncomputable is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathRawCapacityMassFactorSplit
import YMGap.Continuum.BF4PhysicalCutoffUniformRowFloor
import YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewCorrectedSlabJointToleranceSchedule

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffUniformRowFloor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathRawCapacityAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathRawCapacityMassFactorSplit
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewMassSplit
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.SU2PhysicalOuterCutoffNomeTolerance
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

private theorem invSqTerm_pos_local
    (offset : Nat) (offset_at_least_two : 2 <= offset)
    (cutoffOffset : Nat) :
    (0 : Q') < invSqTerm offset offset_at_least_two cutoffOffset := by
  unfold invSqTerm
  exact unit_pos _ _

private theorem amplification_add_one_pos_local
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    (0 : Q') <
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum
          trajectory transitionStart physicalScale cutoffOffset + 1 := by
  let amplification :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum
      trajectory transitionStart physicalScale cutoffOffset
  have hamp : (0 : Q') <= amplification :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum_nonnegative
      trajectory transitionStart physicalScale cutoffOffset
  have honeAdd : (0 : Q') < (1 : Q') + amplification :=
    Q'.pos_add_nonneg (by decide) hamp
  exact Q'.pos_of_lt_of_le honeAdd
    (Q'.le_of_eqv (Q'.add_comm_eqv 1 amplification))

/-! ## 1. Exact tolerance requested by the joint product -/

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointTolerance
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) (cutoffOffset : Nat) : Q' :=
  let amplification :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum
      trajectory transitionStart physicalScale cutoffOffset
  Q'.divPos
    (invSqTerm offset offset_at_least_two cutoffOffset)
    (amplification + 1)
    (amplification_add_one_pos_local
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointTolerance_pos
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) (cutoffOffset : Nat) :
    (0 : Q') <
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointTolerance
        trajectory transitionStart physicalScale offset
        offset_at_least_two cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointTolerance
    Q'.divPos
  exact Q'.mul_pos
    (invSqTerm_pos_local offset offset_at_least_two cutoffOffset)
    (Q'.recipPos_pos _
      (amplification_add_one_pos_local
        trajectory transitionStart physicalScale cutoffOffset))

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointTolerance_mul_amplification_le_invSq
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) (cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointTolerance
          trajectory transitionStart physicalScale offset
          offset_at_least_two cutoffOffset *
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum
          trajectory transitionStart physicalScale cutoffOffset <=
      invSqTerm offset offset_at_least_two cutoffOffset := by
  let amplification :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum
      trajectory transitionStart physicalScale cutoffOffset
  let denominator := amplification + 1
  let target := invSqTerm offset offset_at_least_two cutoffOffset
  let tolerance :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointTolerance
      trajectory transitionStart physicalScale offset
      offset_at_least_two cutoffOffset
  have hamp0 : (0 : Q') <= amplification :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum_nonnegative
      trajectory transitionStart physicalScale cutoffOffset
  have hdenominator : (0 : Q') < denominator :=
    amplification_add_one_pos_local
      trajectory transitionStart physicalScale cutoffOffset
  have htolerance0 : (0 : Q') <= tolerance :=
    Q'.le_of_lt
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointTolerance_pos
        trajectory transitionStart physicalScale offset
        offset_at_least_two cutoffOffset)
  have hampDenominator : amplification <= denominator :=
    Q'.add_le_self_of_nonneg amplification 1 (by decide)
  have hscaled : tolerance * amplification <= tolerance * denominator :=
    Q'.mul_le_mul_of_nonneg_left _ _ tolerance
      hampDenominator htolerance0
  have hcollapse : tolerance * denominator ≈ target := by
    dsimp only [tolerance]
    unfold
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointTolerance
    exact Q'.divPos_mul_eqv target denominator hdenominator
  exact Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hcollapse)

/-! ## 2. The remaining natural-number schedule obligation -/

structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointToleranceSchedule
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  retainedCutoff_le_current : forall cutoffOffset,
    physicalNomeTensorToleranceRetainedCutoff
        (trajectory.nome physicalScale)
        (plaquetteEdgeCount (centralExtent 0 + 1))
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointTolerance
          trajectory transitionStart physicalScale offset
          offset_at_least_two cutoffOffset) <=
      matchedEventualCanonicalCurrentCutoff
        transitionStart physicalScale cutoffOffset

/-! ## 3. Schedule domination inhabits the slab-product lane -/

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointToleranceSchedule.toCorrectedSlabControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (schedule :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointToleranceSchedule
        trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabActivePathRawCapacityAmplificationInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two where
  coefficient := 1
  coefficient_nonnegative := by decide
  envelope_le := by
    intro cutoffOffset
    let tolerance :=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointTolerance
        trajectory transitionStart physicalScale offset
        offset_at_least_two cutoffOffset
    let retained :=
      physicalNomeTensorToleranceRetainedCutoff
        (trajectory.nome physicalScale)
        (plaquetteEdgeCount (centralExtent 0 + 1)) tolerance
    let current :=
      matchedEventualCanonicalCurrentCutoff
        transitionStart physicalScale cutoffOffset
    let later :=
      matchedEventualCanonicalLaterCutoff
        transitionStart physicalScale cutoffOffset
    let amplification :=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum
        trajectory transitionStart physicalScale cutoffOffset
    let target := invSqTerm offset offset_at_least_two cutoffOffset
    have hretainedCurrent : retained <= current :=
      schedule.retainedCutoff_le_current cutoffOffset
    have hcurrentLater : current <= later :=
      matchedEventualCanonicalCurrentCutoff_le_laterCutoff
        transitionStart physicalScale cutoffOffset
    have hretainedLater : retained <= later :=
      Nat.le_trans hretainedCurrent hcurrentLater
    have hincrementAntitone :
        slabParametricKCutoffIncrement
            (trajectory.nome physicalScale) current later (centralExtent 0) <=
          slabParametricKCutoffIncrement
            (trajectory.nome physicalScale) retained later (centralExtent 0) :=
      slabParametricKCutoffIncrement_antitone_base
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        hretainedCurrent hcurrentLater
    have hincrementTolerance :
        slabParametricKCutoffIncrement
            (trajectory.nome physicalScale) retained later (centralExtent 0) <=
          tolerance :=
      slabPhysicalNomeCutoffIncrement_le_tolerance
        (trajectory.nome_pos physicalScale)
        (trajectory.nome_lt_one physicalScale)
        (centralExtent 0)
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointTolerance_pos
          trajectory transitionStart physicalScale offset
          offset_at_least_two cutoffOffset)
        hretainedLater
    have hincrement :
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
            trajectory transitionStart physicalScale cutoffOffset <=
          tolerance := by
      unfold
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
      exact Q'.le_trans' _ _ _ hincrementAntitone hincrementTolerance
    have hamp0 : (0 : Q') <= amplification :=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum_nonnegative
        trajectory transitionStart physicalScale cutoffOffset
    have hproduct :
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
              trajectory transitionStart physicalScale cutoffOffset *
            amplification <=
          tolerance * amplification :=
      Q'.mul_le_mul_of_nonneg_right _ _ amplification hincrement hamp0
    have htoleranceProduct : tolerance * amplification <= target :=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointTolerance_mul_amplification_le_invSq
        trajectory transitionStart physicalScale offset
        offset_at_least_two cutoffOffset
    exact Q'.le_trans' _ _ _ hproduct
      (Q'.le_trans' _ _ _ htoleranceProduct
        (Q'.ge_of_eqv (Q'.one_mul_eqv target)))

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewCorrectedSlabJointToleranceSchedule

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewCorrectedSlabJointToleranceSchedule.matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointTolerance_pos
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewCorrectedSlabJointToleranceSchedule.matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointTolerance_mul_amplification_le_invSq
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewCorrectedSlabJointToleranceSchedule.MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointToleranceSchedule.toCorrectedSlabControl
