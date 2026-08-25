/-
# Old--new traffic: corrected-slab increment and merger split

The exact old--new face row is already bounded by one later new-block mass
times its row-local projective amplification.  The existing adjacent-cutoff
mass theorem bounds that new-block mass by the corrected-slab increment plus
an explicit component-merger residual.  When the executable no-merger check
succeeds, the residual vanishes from the bound.

This module performs exactly those substitutions and exposes separate
Type-level analytic interfaces for the general merger branch and the uniform
no-merger branch.  It does not bound the slab increment, merger residual, or
projective amplification.  No continuum theory or Clay conclusion is
supplied.  No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
or declaration marked noncomputable is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewFaceMass
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorComponentMergerDecision
import YMGap.Continuum.Z4HalfTimeReflectionGeometry

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewMassSplit

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorComponentMergerDecision
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorNewMassComponentSplit
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceEndpointRatio
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceRelativeSourceLoad
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewFaceMass
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewProjectiveAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. Exact names for the two mass producers -/

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Q' :=
  slabParametricKCutoffIncrement
    (trajectory.nome physicalScale)
    (matchedEventualCanonicalCurrentCutoff
      transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalLaterCutoff
      transitionStart physicalScale cutoffOffset)
    (centralExtent 0)

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceComponentMergerResidual
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Q' :=
  centralPhysicalFiniteNewComponentMergerMass
    (trajectory.nome physicalScale)
    (Q'.le_of_lt (trajectory.nome_pos physicalScale))
    (matchedEventualCanonicalCurrentCutoff
      transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalLaterCutoff
      transitionStart physicalScale cutoffOffset) 0

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerCheck
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Bool :=
  centralPhysicalFiniteNoComponentMergerCheck
    (trajectory.nome physicalScale)
    (Q'.le_of_lt (trajectory.nome_pos physicalScale))
    (matchedEventualCanonicalCurrentCutoff
      transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalLaterCutoff
      transitionStart physicalScale cutoffOffset) 0

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow_le_increment_add_merger_mul_projectiveAmplificationMaximum
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow
        trajectory transitionStart physicalScale cutoffOffset pair <=
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
          trajectory transitionStart physicalScale cutoffOffset +
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceComponentMergerResidual
          trajectory transitionStart physicalScale cutoffOffset) *
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationMaximumOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair := by
  exact Q'.le_trans' _ _ _
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow_le_newBlockMass_mul_projectiveAmplificationMaximum
      trajectory transitionStart physicalScale cutoffOffset pair)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (matchedEventualCanonicalLaterNewBlockMass_le_increment_add_merger
        trajectory transitionStart physicalScale cutoffOffset)
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationMaximumOnCurrentPair_nonnegative
        trajectory transitionStart physicalScale cutoffOffset pair))

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow_le_increment_mul_projectiveAmplificationMaximum_of_noMerger
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hcheck :
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerCheck
        trajectory transitionStart physicalScale cutoffOffset = true) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow
        trajectory transitionStart physicalScale cutoffOffset pair <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
          trajectory transitionStart physicalScale cutoffOffset *
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationMaximumOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair := by
  exact Q'.le_trans' _ _ _
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow_le_newBlockMass_mul_projectiveAmplificationMaximum
      trajectory transitionStart physicalScale cutoffOffset pair)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (matchedEventualCanonicalLaterNewBlockMass_le_increment_of_noMerger
        trajectory transitionStart physicalScale cutoffOffset hcheck)
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationMaximumOnCurrentPair_nonnegative
        trajectory transitionStart physicalScale cutoffOffset pair))

/-! ## 2. General merger-residual analytic interface -/

structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitProjectiveAmplificationInverseSquareControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  envelope_le : forall cutoffOffset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale cutoffOffset ->
    matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        ((matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
              trajectory transitionStart physicalScale cutoffOffset +
            matchedEventualCanonicalNewEndpointTrafficOldNewFaceComponentMergerResidual
              trajectory transitionStart physicalScale cutoffOffset) *
          matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationMaximumOnCurrentPair
            trajectory transitionStart physicalScale cutoffOffset pair) <=
      (coefficient * invSqTerm offset offset_at_least_two cutoffOffset) *
        matchedEventualCanonicalNewEndpointTrafficConditionalCapacityOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitProjectiveAmplificationInverseSquareControl.toEndpointRatioControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (control : MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitProjectiveAmplificationInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two where
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  endpointRatio_le := by
    intro cutoffOffset pair hpair
    have hfloor0 : (0 : Q') <=
        matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale :=
      Q'.le_of_lt
        (matchedEventualCanonicalSupportSharedFloor_pos
          trajectory transitionStart physicalScale)
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow_le_increment_add_merger_mul_projectiveAmplificationMaximum
          trajectory transitionStart physicalScale cutoffOffset pair)
        hfloor0)
      (control.envelope_le cutoffOffset pair hpair)

theorem matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewMassSplitProjectiveAmplification_and_otherFaces
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (oldNew : MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitProjectiveAmplificationInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two)
    (newOld : MatchedEventualCanonicalNewEndpointTrafficNewOldFaceEndpointRatioCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two)
    (newNew : MatchedEventualCanonicalNewEndpointTrafficNewNewFaceEndpointRatioCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two)
    (cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      (oldNew.coefficient + (newOld.coefficient + newNew.coefficient)) *
        invSqTerm offset offset_at_least_two cutoffOffset :=
  matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_threeFaceEndpointRatioCapacityBalances
    oldNew.toEndpointRatioControl newOld newNew cutoffOffset

/-! ## 3. Uniform executable no-merger analytic interface -/

structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerProjectiveAmplificationInverseSquareControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  noMerger : forall cutoffOffset,
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerCheck
      trajectory transitionStart physicalScale cutoffOffset = true
  envelope_le : forall cutoffOffset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale cutoffOffset ->
    matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
            trajectory transitionStart physicalScale cutoffOffset *
          matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationMaximumOnCurrentPair
            trajectory transitionStart physicalScale cutoffOffset pair) <=
      (coefficient * invSqTerm offset offset_at_least_two cutoffOffset) *
        matchedEventualCanonicalNewEndpointTrafficConditionalCapacityOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerProjectiveAmplificationInverseSquareControl.toEndpointRatioControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (control : MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerProjectiveAmplificationInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two where
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  endpointRatio_le := by
    intro cutoffOffset pair hpair
    have hfloor0 : (0 : Q') <=
        matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale :=
      Q'.le_of_lt
        (matchedEventualCanonicalSupportSharedFloor_pos
          trajectory transitionStart physicalScale)
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow_le_increment_mul_projectiveAmplificationMaximum_of_noMerger
          trajectory transitionStart physicalScale cutoffOffset pair
          (control.noMerger cutoffOffset))
        hfloor0)
      (control.envelope_le cutoffOffset pair hpair)

theorem matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewNoMergerProjectiveAmplification_and_otherFaces
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (oldNew : MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerProjectiveAmplificationInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two)
    (newOld : MatchedEventualCanonicalNewEndpointTrafficNewOldFaceEndpointRatioCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two)
    (newNew : MatchedEventualCanonicalNewEndpointTrafficNewNewFaceEndpointRatioCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two)
    (cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      (oldNew.coefficient + (newOld.coefficient + newNew.coefficient)) *
        invSqTerm offset offset_at_least_two cutoffOffset :=
  matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_threeFaceEndpointRatioCapacityBalances
    oldNew.toEndpointRatioControl newOld newNew cutoffOffset

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewMassSplit

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewMassSplit.matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow_le_increment_add_merger_mul_projectiveAmplificationMaximum
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewMassSplit.matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow_le_increment_mul_projectiveAmplificationMaximum_of_noMerger
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewMassSplit.MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitProjectiveAmplificationInverseSquareControl.toEndpointRatioControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewMassSplit.matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewMassSplitProjectiveAmplification_and_otherFaces
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewMassSplit.MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerProjectiveAmplificationInverseSquareControl.toEndpointRatioControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewMassSplit.matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewNoMergerProjectiveAmplification_and_otherFaces
