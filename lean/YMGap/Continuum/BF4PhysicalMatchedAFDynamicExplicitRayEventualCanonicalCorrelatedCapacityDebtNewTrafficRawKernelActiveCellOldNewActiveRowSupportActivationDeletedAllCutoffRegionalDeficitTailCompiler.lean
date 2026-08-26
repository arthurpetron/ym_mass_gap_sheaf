/-
# Tail compiler for the shifted adaptive regional bridge

The exact adaptive regional bridge bounds the canonical transported deficit at
`k+1` by route mismatch at `k`, coherent adaptive data drift at `k`, and route
mismatch at `k+1`.  This module performs only the remaining summability
bookkeeping:

* shift a tail control forward by one cutoff;
* combine the three pointwise terms;
* transport the resulting tail through the checked inequality;
* restore the omitted finite cutoff by increasing the tail rate by one; and
* feed the resulting canonical transported tail, together with the unchanged
  three shell-face tails, to the existing total-deficit compiler.

The two adaptive analytic inputs are explicit `Type`-level arguments.  They
are not inhabited here.  No completed gap, continuum limit, or Clay conclusion
is asserted.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffRegionalDeficitBridge
import YMGap.Continuum.SummableRationalStepVariationAlgebra

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffRegionalDeficitTailCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtDeficitCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffObservableCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffRegionalDeficitBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTotalDeficitCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.SummableCRealStepVariation
open YMGap.Continuum.SummableRationalStepVariationAlgebra

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Three generic constructive tail transports -/

private def antitoneTailControlOfPointwiseLe
    {lower upper : Nat -> Q'}
    (upperTail : AntitoneTailControl upper)
    (pointwise : forall offset, lower offset <= upper offset) :
    AntitoneTailControl lower where
  tailRate := upperTail.tailRate
  tailRate_antitone := upperTail.tailRate_antitone
  tailBound := by
    intro epsilon epsilon_pos start start_bound length
    exact Q'.le_trans' _ _ _
      (ExpNeg.finSum_le_finSum_of_termwise
        (fun offset => lower (start + offset))
        (fun offset => upper (start + offset))
        (fun offset => pointwise (start + offset)) length)
      (upperTail.tailBound epsilon epsilon_pos start start_bound length)

private def antitoneTailControlSucc
    {variation : Nat -> Q'}
    (tail : AntitoneTailControl variation) :
    AntitoneTailControl (fun offset => variation (offset + 1)) where
  tailRate := tail.tailRate
  tailRate_antitone := tail.tailRate_antitone
  tailBound := by
    intro epsilon epsilon_pos start start_bound length
    have hsum :
        finSum (fun offset => variation ((start + offset) + 1)) length ≈
          finSum (fun offset => variation ((start + 1) + offset)) length := by
      apply RationalTail.finSum_eqv_congr
      intro offset
      have hindex : (start + offset) + 1 = (start + 1) + offset := by omega
      rw [hindex]
      exact Q'.eqv_refl _
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsum)
      (tail.tailBound epsilon epsilon_pos (start + 1)
        (Nat.le_trans start_bound (Nat.le_add_right start 1)) length)

private def antitoneTailControlOfSucc
    {variation : Nat -> Q'}
    (tail : AntitoneTailControl (fun offset => variation (offset + 1))) :
    AntitoneTailControl variation where
  tailRate := fun epsilon => tail.tailRate epsilon + 1
  tailRate_antitone := by
    intro epsilon delta delta_pos delta_le_epsilon
    exact Nat.add_le_add_right
      (tail.tailRate_antitone epsilon delta delta_pos delta_le_epsilon) 1
  tailBound := by
    intro epsilon epsilon_pos start start_bound length
    have hpredecessor : tail.tailRate epsilon <= start - 1 :=
      Nat.le_sub_of_add_le start_bound
    have hsum :
        finSum (fun offset => variation (start + offset)) length ≈
          finSum (fun offset => variation (((start - 1) + offset) + 1)) length := by
      apply RationalTail.finSum_eqv_congr
      intro offset
      have hindex : start + offset = ((start - 1) + offset) + 1 := by omega
      rw [hindex]
      exact Q'.eqv_refl _
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsum)
      (tail.tailBound epsilon epsilon_pos (start - 1) hpredecessor length)

/-! ## 2. The two exact adaptive scalar streams -/

def matchedEventualAdaptiveCanonicalRouteMismatchDeficitSequence
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (certificate :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
        trajectory transitionStart physicalScale) : Nat -> Q' :=
  fun cutoffOffset =>
    matchedEventualAdaptiveCanonicalRouteMismatchDeficitMaximum
      certificate cutoffOffset

def matchedEventualAdaptiveCoherentDataDeficitSequence
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (certificate :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
        trajectory transitionStart physicalScale) : Nat -> Q' :=
  fun cutoffOffset =>
    matchedEventualAdaptiveCoherentDataDeficitMaximum certificate cutoffOffset

/-! ## 3. Two adaptive tails reconstruct the canonical transported tail -/

def matchedEventualAdaptiveCoherentTailsToShiftedCanonicalTransportedTailControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    {certificate :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
        trajectory transitionStart physicalScale}
    (routeMismatch : AntitoneTailControl
      (matchedEventualAdaptiveCanonicalRouteMismatchDeficitSequence certificate))
    (coherentData : AntitoneTailControl
      (matchedEventualAdaptiveCoherentDataDeficitSequence certificate)) :
    AntitoneTailControl
      (fun cutoffOffset =>
        matchedEventualCanonicalTransportedCapacityDebtDeficitMaximum
          trajectory transitionStart physicalScale (cutoffOffset + 1)) :=
  antitoneTailControlOfPointwiseLe
    (addAntitoneTailControl routeMismatch
      (addAntitoneTailControl coherentData
        (antitoneTailControlSucc routeMismatch)))
    (fun cutoffOffset => by
      simpa only [
        matchedEventualAdaptiveCanonicalRouteMismatchDeficitSequence,
        matchedEventualAdaptiveCoherentDataDeficitSequence] using
        matchedEventualCanonicalTransportedCapacityDebtDeficitMaximum_succ_le_adaptive_split
          certificate cutoffOffset)

def matchedEventualAdaptiveCoherentTailsToCanonicalTransportedTail
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    {certificate :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
        trajectory transitionStart physicalScale}
    (routeMismatch : AntitoneTailControl
      (matchedEventualAdaptiveCanonicalRouteMismatchDeficitSequence certificate))
    (coherentData : AntitoneTailControl
      (matchedEventualAdaptiveCoherentDataDeficitSequence certificate)) :
    MatchedEventualCanonicalTransportedCapacityDebtDeficitTail
      trajectory transitionStart physicalScale where
  tailControl := antitoneTailControlOfSucc
    (matchedEventualAdaptiveCoherentTailsToShiftedCanonicalTransportedTailControl
      routeMismatch coherentData)

/-! ## 4. The adaptive branch rejoins the unchanged total tail -/

def matchedEventualAdaptiveCoherentRegionalTailsToTotalDeficitTail
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    {certificate :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
        trajectory transitionStart physicalScale}
    (routeMismatch : AntitoneTailControl
      (matchedEventualAdaptiveCanonicalRouteMismatchDeficitSequence certificate))
    (coherentData : AntitoneTailControl
      (matchedEventualAdaptiveCoherentDataDeficitSequence certificate))
    (oldNew : MatchedEventualCanonicalOldNewCapacityDebtDeficitTail
      trajectory transitionStart physicalScale)
    (newOld : MatchedEventualCanonicalNewOldCapacityDebtDeficitTail
      trajectory transitionStart physicalScale)
    (newNew : MatchedEventualCanonicalNewNewCapacityDebtDeficitTail
      trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalCapacityDebtTotalDeficitTail
      trajectory transitionStart physicalScale :=
  matchedEventualCanonicalCapacityDebtTotalDeficitTailOfRegionalTails
    (matchedEventualAdaptiveCoherentTailsToCanonicalTransportedTail
      routeMismatch coherentData)
    oldNew newOld newNew

/-! ## Axiom audit -/

#print axioms matchedEventualAdaptiveCanonicalRouteMismatchDeficitSequence
#print axioms matchedEventualAdaptiveCoherentDataDeficitSequence
#print axioms
  matchedEventualAdaptiveCoherentTailsToShiftedCanonicalTransportedTailControl
#print axioms
  matchedEventualAdaptiveCoherentTailsToCanonicalTransportedTail
#print axioms
  matchedEventualAdaptiveCoherentRegionalTailsToTotalDeficitTail

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffRegionalDeficitTailCompiler
