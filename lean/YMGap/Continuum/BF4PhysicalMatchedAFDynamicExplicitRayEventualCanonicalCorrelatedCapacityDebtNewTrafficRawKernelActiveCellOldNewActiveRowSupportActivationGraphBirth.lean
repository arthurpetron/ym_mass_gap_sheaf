/-
# Activated used rows are literal support-graph edge births

The executable activation decision already returns a used current pair whose
current physical kernel is not positive and whose mapped later raw capacity is
positive.  On the exact vacuum-sector carriers, kernel positivity is
equivalent to Boolean support adjacency.  This module transports the decision
through that equivalence.

Every activated witness is therefore a literal graph-edge birth: adjacency is
false at the current cutoff and true on the mapped pair at the later cutoff.
The avoided branch remains literal emptiness.  A future adaptive route need
only address these checked births; it need not replace all canonical edges.

No theorem says births are uniformly absent, quantitatively harmless, or
avoidable by a coherent adaptive routing.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationRouteDecision

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationGraphBirth

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowCapacityFloorFactorization
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowRawKernelFloor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationRouteDecision
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationSplit
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewMassSplit
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.FiniteWeightedCartesianInjection

private theorem q_right_pos_of_mul_pos_local
    {left right : Q'}
    (hleft : (0 : Q') <= left)
    (hproduct : (0 : Q') < left * right) :
    (0 : Q') < right := by
  have hproductNum := Q'.num_pos_of_pos hproduct
  change (0 : Int) < left.num * right.num at hproductNum
  have hleftNum : (0 : Int) <= left.num :=
    (Q'.zero_le_iff_num_nonneg left).mp hleft
  apply CReal.pos_of_num_pos
  apply Int.lt_of_not_ge
  intro hrightNonpos
  have hmulNonpos : left.num * right.num <= 0 :=
    Int.mul_nonpos_of_nonneg_of_nonpos hleftNum hrightNonpos
  exact (Int.not_lt_of_ge hmulNonpos) hproductNum

/-! ## 1. One activated row is exactly one support birth -/

structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedSupportGraphBirth
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Type where
  pair : Nat × Nat
  pair_mem : pair ∈
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairs
      trajectory transitionStart physicalScale cutoffOffset
  current_support_false :
    centralPhysicalFiniteSupportAdjacentB
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + cutoffOffset)
        0 pair.1 pair.2 = false
  later_mapped_support_true :
    centralPhysicalFiniteSupportAdjacentB
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1))
        0
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair).1
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair).2 = true

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedSupportGraphBirth_of_pair
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedSupportGraphBirth
      trajectory transitionStart physicalScale cutoffOffset := by
  have hactivation :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedPair_is_genuine_later_support
      trajectory transitionStart physicalScale cutoffOffset pair hpair
  have hactiveParts :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActiveCurrentPair_mem_and_routeMaximum_pos
      trajectory transitionStart physicalScale cutoffOffset pair hactivation.1
  have hcurrentMembers := (mem_cartesian_iff _ _ pair).mp hactiveParts.1
  have hcurrentIff :=
    centralPhysicalFiniteSupportAdjacentB_true_iff_kernel_pos
      hcurrentMembers.1 hcurrentMembers.2
  have hcurrentFalse :
      centralPhysicalFiniteSupportAdjacentB
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + cutoffOffset)
          0 pair.1 pair.2 = false := by
    cases hsupport : centralPhysicalFiniteSupportAdjacentB
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + cutoffOffset)
        0 pair.1 pair.2 with
    | false => rfl
    | true =>
        exact False.elim (hactivation.2.1 (hcurrentIff.mp hsupport))
  have hlaterPair :=
    matchedEventualCanonicalCurrentPairToNext_mem
      trajectory transitionStart physicalScale cutoffOffset pair hactiveParts.1
  have hlaterMembers :=
    (mem_cartesian_iff _ _
      (matchedEventualCanonicalCurrentPairToNext
        trajectory transitionStart physicalScale cutoffOffset pair)).mp
      hlaterPair
  have hlaterRawCapacity := hactivation.2.2
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceMappedRawKernelCapacityOnCurrentPair
    matchedEventualCanonicalTransportedBridgeRawKernelCapacityOnEdge
    at hlaterRawCapacity
  have hlaterKernel :=
    q_right_pos_of_mul_pos_local (by decide) hlaterRawCapacity
  have hlaterTrue :=
    (centralPhysicalFiniteSupportAdjacentB_true_iff_kernel_pos
      hlaterMembers.1 hlaterMembers.2).mpr hlaterKernel
  exact
    { pair := pair
      pair_mem := hpair
      current_support_false := hcurrentFalse
      later_mapped_support_true := hlaterTrue }

/-! ## 2. The executable route decision returns emptiness or a birth -/

inductive MatchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedSupportGraphBirthDecision
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Type where
  | avoided
      (activatedPairs_eq_nil :
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedActiveCurrentPairs
          trajectory transitionStart physicalScale cutoffOffset = [])
  | born
      (birth :
        MatchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedSupportGraphBirth
          trajectory transitionStart physicalScale cutoffOffset)

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedSupportGraphBirthDecision
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedSupportGraphBirthDecision
      trajectory transitionStart physicalScale cutoffOffset :=
  match
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedSupportUseDecision
      trajectory transitionStart physicalScale cutoffOffset with
  | .avoided hempty => .avoided hempty
  | .used pair hpair =>
      .born
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedSupportGraphBirth_of_pair
          trajectory transitionStart physicalScale cutoffOffset pair hpair)

/-! ## Axiom audit -/

#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedSupportGraphBirth_of_pair
#print axioms
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceActivatedSupportGraphBirthDecision

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationGraphBirth
