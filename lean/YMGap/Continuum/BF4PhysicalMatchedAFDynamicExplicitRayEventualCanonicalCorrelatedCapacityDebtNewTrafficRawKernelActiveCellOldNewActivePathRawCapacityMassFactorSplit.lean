/-
# Old--new joint amplification: split the two mass producers

The exact old--new observable-connected obstruction is now one scalar joint
amplification stream.  Its remaining general coefficient is the sum of two
different mass producers: the corrected-slab cutoff increment and the
component-merger residual.  Those two estimates need not be proved by the same
argument or at the same time.

This module exposes independent inverse-square controls for the corrected-slab
and merger products, then recombines them constructively by distributivity.
An independent uniform no-merger certificate lets the corrected-slab lane
compile without any merger estimate.  Both routes return the preceding exact
same-carrier amplification control and unchanged three-face debt maximum.

No corrected-slab rate, merger rate, no-merger certificate, joint-amplification
bound, continuum theory, or Clay conclusion is supplied.  No `Classical.*`,
choice, `native_decide`, `sorry`, custom axiom, or declaration marked
noncomputable is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathRawCapacityAmplification

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathRawCapacityMassFactorSplit

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceEndpointRatio
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathRawCapacityAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewMassSplit
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.SummableInverseSquare

/-! ## 1. Independent product controls -/

structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabActivePathRawCapacityAmplificationInverseSquareControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  envelope_le : forall cutoffOffset,
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
        trajectory transitionStart physicalScale cutoffOffset *
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      coefficient * invSqTerm offset offset_at_least_two cutoffOffset

structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceComponentMergerActivePathRawCapacityAmplificationInverseSquareControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  envelope_le : forall cutoffOffset,
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceComponentMergerResidual
        trajectory transitionStart physicalScale cutoffOffset *
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      coefficient * invSqTerm offset offset_at_least_two cutoffOffset

structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceUniformNoMergerCertificate
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale : Nat) : Type 1 where
  noMerger : forall cutoffOffset,
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerCheck
      trajectory transitionStart physicalScale cutoffOffset = true

/-! ## 2. Recombination compilers -/

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabActivePathRawCapacityAmplificationInverseSquareControl.andComponentMerger
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (slab :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabActivePathRawCapacityAmplificationInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two)
    (merger :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceComponentMergerActivePathRawCapacityAmplificationInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitActivePathRawCapacityAmplificationInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two where
  coefficient := slab.coefficient + merger.coefficient
  coefficient_nonnegative :=
    Q'.add_le_add slab.coefficient_nonnegative merger.coefficient_nonnegative
  envelope_le := by
    intro cutoffOffset
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.add_mul_eqv
          (matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
            trajectory transitionStart physicalScale cutoffOffset)
          (matchedEventualCanonicalNewEndpointTrafficOldNewFaceComponentMergerResidual
            trajectory transitionStart physicalScale cutoffOffset)
          (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivePathRawCapacityAmplificationMaximum
            trajectory transitionStart physicalScale cutoffOffset)))
      (Q'.le_trans' _ _ _
        (Q'.add_le_add
          (slab.envelope_le cutoffOffset)
          (merger.envelope_le cutoffOffset))
        (Q'.ge_of_eqv
          (Q'.add_mul_eqv
            slab.coefficient merger.coefficient
            (invSqTerm offset offset_at_least_two cutoffOffset))))

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabActivePathRawCapacityAmplificationInverseSquareControl.withNoMerger
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (slab :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabActivePathRawCapacityAmplificationInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two)
    (noMerger :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceUniformNoMergerCertificate
        trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerActivePathRawCapacityAmplificationInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two where
  coefficient := slab.coefficient
  coefficient_nonnegative := slab.coefficient_nonnegative
  noMerger := noMerger.noMerger
  envelope_le := slab.envelope_le

/-! ## 3. Exact debt endpoints -/

theorem matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewCorrectedSlab_and_componentMerger_activePathRawCapacityAmplification_and_otherFaces
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (slab :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabActivePathRawCapacityAmplificationInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two)
    (merger :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceComponentMergerActivePathRawCapacityAmplificationInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two)
    (newOld : MatchedEventualCanonicalNewEndpointTrafficNewOldFaceEndpointRatioCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two)
    (newNew : MatchedEventualCanonicalNewEndpointTrafficNewNewFaceEndpointRatioCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two)
    (cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      ((slab.coefficient + merger.coefficient) +
          (newOld.coefficient + newNew.coefficient)) *
        invSqTerm offset offset_at_least_two cutoffOffset :=
  matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewMassSplitActivePathRawCapacityAmplification_and_otherFaces
    (slab.andComponentMerger merger) newOld newNew cutoffOffset

theorem matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewCorrectedSlab_noMerger_activePathRawCapacityAmplification_and_otherFaces
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (slab :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabActivePathRawCapacityAmplificationInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two)
    (noMerger :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceUniformNoMergerCertificate
        trajectory transitionStart physicalScale)
    (newOld : MatchedEventualCanonicalNewEndpointTrafficNewOldFaceEndpointRatioCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two)
    (newNew : MatchedEventualCanonicalNewEndpointTrafficNewNewFaceEndpointRatioCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two)
    (cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      (slab.coefficient + (newOld.coefficient + newNew.coefficient)) *
        invSqTerm offset offset_at_least_two cutoffOffset :=
  matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewNoMergerActivePathRawCapacityAmplification_and_otherFaces
    (slab.withNoMerger noMerger) newOld newNew cutoffOffset

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathRawCapacityMassFactorSplit

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathRawCapacityMassFactorSplit.MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabActivePathRawCapacityAmplificationInverseSquareControl.andComponentMerger
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathRawCapacityMassFactorSplit.MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabActivePathRawCapacityAmplificationInverseSquareControl.withNoMerger
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathRawCapacityMassFactorSplit.matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewCorrectedSlab_and_componentMerger_activePathRawCapacityAmplification_and_otherFaces
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActivePathRawCapacityMassFactorSplit.matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewCorrectedSlab_noMerger_activePathRawCapacityAmplification_and_otherFaces
