/-
# Old--new corrected-slab product: least-dyadic joint schedule

The exact joint tolerance

  invSqTerm / (1 + observable-connected amplification)

is positive.  Instead of feeding that rational directly to a denominator-based
tail modulus, this module computes the least certified dyadic precision below
it and invokes the affine dyadic corrected-slab tail compiler.

The remaining consecutive-cutoff obligation is then factored causally into:

* a fixed start large enough to absorb the nome/dimension tail burn and one
  precision intercept; and
* an at-most-one-per-offset growth bound for the least joint precision.

The second field is the live analytic obstruction.  It is still computed from
the exact same current/later carrier and therefore preserves the observable-
connected path through the compilers.  No such growth datum is inhabited here.

No component-merger theorem, other directed face estimate, continuum theory,
or Clay conclusion is supplied.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Constructive.DyadicPrecision
import YMGap.Continuum.BF4SU2CorrectedSlabNomeDyadicTail
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewCorrectedSlabJointToleranceSchedule

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewCorrectedSlabDyadicJointToleranceSchedule

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffUniformRowFloor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathRawCapacityAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathRawCapacityMassFactorSplit
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewCorrectedSlabJointToleranceSchedule
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewMassSplit
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4SU2CorrectedSlabNomeDyadicTail
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2PhysicalOuterCutoffNomeDyadicTolerance
open YMGap.Continuum.SU2PhysicalOuterCutoffNomeTolerance
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Least dyadic exponent below the exact joint tolerance -/

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicPrecision
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) (cutoffOffset : Nat) : Nat :=
  YMGap.Constructive.DyadicPrecision.least
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointTolerance
      trajectory transitionStart physicalScale offset
      offset_at_least_two cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyad_le_tolerance
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) (cutoffOffset : Nat) :
    dyad
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicPrecision
          trajectory transitionStart physicalScale offset
          offset_at_least_two cutoffOffset) <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointTolerance
        trajectory transitionStart physicalScale offset
        offset_at_least_two cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicPrecision
    dyad
  exact YMGap.Constructive.DyadicPrecision.half_pow_le_at_least
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointTolerance_pos
      trajectory transitionStart physicalScale offset
      offset_at_least_two cutoffOffset)

/-- Any analytic dyadic lower bound on the exact joint tolerance immediately
bounds the executable least precision. -/
theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicPrecision_le_of_dyad_le_tolerance
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) (cutoffOffset candidate : Nat)
    (hcandidate :
      dyad candidate <=
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointTolerance
          trajectory transitionStart physicalScale offset
          offset_at_least_two cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicPrecision
        trajectory transitionStart physicalScale offset
        offset_at_least_two cutoffOffset <=
      candidate := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicPrecision
  apply YMGap.Constructive.DyadicPrecision.least_le_of_half_pow_le
  exact hcandidate

/-! ## 2. Affine dyadic retained cutoff -/

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicRetainedCutoff
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) (cutoffOffset : Nat) : Nat :=
  physicalNomeTensorDyadicRetainedCutoff
    (trajectory.nome physicalScale)
    (plaquetteEdgeCount (centralExtent 0 + 1))
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicPrecision
      trajectory transitionStart physicalScale offset
      offset_at_least_two cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicRetainedCutoff_eq
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) (cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicRetainedCutoff
        trajectory transitionStart physicalScale offset
        offset_at_least_two cutoffOffset =
      physicalNomeBaseCutoff (trajectory.nome physicalScale) - 1 +
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicPrecision
            trajectory transitionStart physicalScale offset
            offset_at_least_two cutoffOffset +
          physicalNomeTensorDyadicBurn
            (trajectory.nome physicalScale)
            (plaquetteEdgeCount (centralExtent 0 + 1))) := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicRetainedCutoff
  exact physicalNomeTensorDyadicRetainedCutoff_eq _ _ _

/-! ## 3. Direct schedule and corrected-slab product compiler -/

structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicSchedule
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  retainedCutoff_le_current : forall cutoffOffset,
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicRetainedCutoff
        trajectory transitionStart physicalScale offset
        offset_at_least_two cutoffOffset <=
      matchedEventualCanonicalCurrentCutoff
        transitionStart physicalScale cutoffOffset

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicSchedule.toCorrectedSlabControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (schedule :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicSchedule
        trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabActivePathRawCapacityAmplificationInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two where
  coefficient := 1
  coefficient_nonnegative := by decide
  envelope_le := by
    intro cutoffOffset
    let precision :=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicPrecision
        trajectory transitionStart physicalScale offset
        offset_at_least_two cutoffOffset
    let tolerance :=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointTolerance
        trajectory transitionStart physicalScale offset
        offset_at_least_two cutoffOffset
    let retained :=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicRetainedCutoff
        trajectory transitionStart physicalScale offset
        offset_at_least_two cutoffOffset
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
    have hincrementDyad :
        slabParametricKCutoffIncrement
            (trajectory.nome physicalScale) retained later (centralExtent 0) <=
          dyad precision := by
      exact slabPhysicalNomeCutoffIncrement_le_dyad_linear
        (trajectory.nome_pos physicalScale)
        (trajectory.nome_lt_one physicalScale)
        (centralExtent 0) precision hretainedLater
    have hdyadTolerance : dyad precision <= tolerance :=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyad_le_tolerance
        trajectory transitionStart physicalScale offset
        offset_at_least_two cutoffOffset
    have hincrement :
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
            trajectory transitionStart physicalScale cutoffOffset <=
          tolerance := by
      unfold
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
      exact Q'.le_trans' _ _ _ hincrementAntitone
        (Q'.le_trans' _ _ _ hincrementDyad hdyadTolerance)
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

/-! ## 4. Causal factorization for consecutive cutoffs -/

/-- The direct dyadic schedule follows from a fixed start payment and
at-most-one growth of the least joint precision per cutoff offset. -/
structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicLinearData
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  precisionIntercept : Nat
  precision_le : forall cutoffOffset,
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicPrecision
        trajectory transitionStart physicalScale offset
        offset_at_least_two cutoffOffset <=
      precisionIntercept + cutoffOffset
  start_absorbs_fixed_tail_cost :
    physicalNomeBaseCutoff (trajectory.nome physicalScale) - 1 +
        (precisionIntercept +
          physicalNomeTensorDyadicBurn
            (trajectory.nome physicalScale)
            (plaquetteEdgeCount (centralExtent 0 + 1))) <=
      transitionStart physicalScale

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicLinearData.toSchedule
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (data :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicLinearData
        trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicSchedule
      trajectory transitionStart physicalScale offset offset_at_least_two where
  retainedCutoff_le_current := by
    intro cutoffOffset
    rw [matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicRetainedCutoff_eq]
    unfold matchedEventualCanonicalCurrentCutoff
    have hprecision := data.precision_le cutoffOffset
    have hstart := data.start_absorbs_fixed_tail_cost
    omega

/-! ## Axiom audit -/

#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyad_le_tolerance
#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicPrecision_le_of_dyad_le_tolerance
#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicRetainedCutoff_eq
#print axioms
  MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicSchedule.toCorrectedSlabControl
#print axioms
  MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabJointDyadicLinearData.toSchedule

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewCorrectedSlabDyadicJointToleranceSchedule
