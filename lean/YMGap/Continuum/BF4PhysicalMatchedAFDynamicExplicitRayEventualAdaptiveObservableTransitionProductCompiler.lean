/-
# Exact observable capacity constructs the matched transition product

The adaptive all-cutoff observable certificate already states the literal
edgewise inequality needed by the finite off-ray capacity check.  This module
closes the small but load-bearing logical gap between those presentations.

First, an elementary finite-minimum reflection proves that an edgewise
capacity payment puts the shared ray floor below the exact minimum of all
capacity ratios.  The unit fallback is harmless because every cofinal ray
capacity has `delta <= 1/2`.  Second, shifting the requested cofinal start by
one aligns the observable certificate's cutoff `start + (offset + 1)` with
the check producer's cutoff variable.  A scale-wise family of observable
certificates then constructs the existing matched local producer, completed
family, and normalized strength law directly.

No route-coherence or regional-deficit tail is required for this contraction.
The observable capacity family itself is not inhabited here.  No strength
band, same-object observable pin, continuum limit, continuum Yang--Mills
theory, isolated vacuum, or Clay conclusion is asserted.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffObservableCompiler
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualTransitionProductCompiler
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicStrengthNormalization

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualAdaptiveObservableTransitionProductCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffObservableCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualTransitionProductCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicStrengthNormalization
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityDecision
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor

/-! ## 1. Reflect edgewise capacity into the exact finite minimum -/

private theorem lower_le_listPositiveMinOne_local
    {State : Type} (value : State -> Q') (lower : Q') :
    forall states : List State,
      lower <= (1 : Q') ->
      (forall state, state ∈ states -> lower <= value state) ->
      lower <= listPositiveMinOne value states
  | [], hunit, _ => hunit
  | first :: rest, hunit, hall => by
      unfold listPositiveMinOne Q'.min'
      by_cases hle : value first <= listPositiveMinOne value rest
      · rw [if_pos hle]
        exact hall first List.mem_cons_self
      · rw [if_neg hle]
        exact lower_le_listPositiveMinOne_local value lower rest hunit
          (fun state hstate =>
            hall state (List.mem_cons_of_mem first hstate))

theorem matchedEventualCanonicalSupportSharedFloor_le_one
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale : Nat) :
    matchedEventualCanonicalSupportSharedFloor
        trajectory transitionStart physicalScale <= (1 : Q') := by
  have hdelta :
      (eventualExplicitRayCapacity trajectory transitionStart physicalScale).delta <=
        HalfPow.half :=
    FixedNomeCofinalSpinCubeRayCapacity.delta_le_half
      (eventualExplicitRayCapacity trajectory transitionStart physicalScale)
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half hdelta
    (by decide : (0 : Q') <= HalfPow.half)
  unfold matchedEventualCanonicalSupportSharedFloor
  exact Q'.le_trans' _ (HalfPow.half * HalfPow.half) _ hscaled (by decide)

theorem MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate.sharedFloor_le_finiteCapacityMargin
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (certificate :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) :
    matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale <=
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductFiniteCapacityMargin
        (certificate.fullRoutingAt cutoffOffset) := by
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductFiniteCapacityMargin
  apply lower_le_listPositiveMinOne_local
  · exact matchedEventualCanonicalSupportSharedFloor_le_one
      trajectory transitionStart physicalScale
  · intro pair hpair
    unfold
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductEdgeRatio
    by_cases hload : (0 : Q') <
        centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad
          (certificate.fullRoutingAt cutoffOffset) pair.1 pair.2
    · rw [dif_pos hload]
      apply Q'.le_divPos_of_mul_le
      simpa only [
        centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadOnPair]
        using certificate.fullLoad_capacity cutoffOffset pair hpair
    · rw [dif_neg hload]
      exact matchedEventualCanonicalSupportSharedFloor_le_one
        trajectory transitionStart physicalScale

/-! ## 2. One scale-wise observable certificate constructs exact checks -/

def transportPositiveRoutingAt
    {w : Q'} {hw : (0 : Q') <= w} {leftCutoff rightCutoff : Nat}
    (hcutoff : leftCutoff = rightCutoff)
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w hw leftCutoff) :
    CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w hw rightCutoff :=
  hcutoff ▸ routing

theorem finiteCapacityMargin_transportPositiveRoutingAt
    {w : Q'} {hw : (0 : Q') <= w} {leftCutoff rightCutoff : Nat}
    (hcutoff : leftCutoff = rightCutoff)
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w hw leftCutoff) :
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductFiniteCapacityMargin
        (transportPositiveRoutingAt hcutoff routing) =
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductFiniteCapacityMargin
        routing := by
  cases hcutoff
  rfl

def observableCertificateShiftedRoutingAt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (certificate :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) :
    CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      ((transitionStart physicalScale + 1) + cutoffOffset) :=
  transportPositiveRoutingAt (by omega)
    (certificate.fullRoutingAt cutoffOffset)

theorem MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate.sharedFloor_le_shiftedFiniteCapacityMargin
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (certificate :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) :
    matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale <=
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductFiniteCapacityMargin
        (observableCertificateShiftedRoutingAt certificate cutoffOffset) := by
  unfold observableCertificateShiftedRoutingAt
  rw [finiteCapacityMargin_transportPositiveRoutingAt]
  exact
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate.sharedFloor_le_finiteCapacityMargin
      certificate cutoffOffset

def observableCertificateRoutingAt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (certificate :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
        trajectory transitionStart physicalScale)
    (K : Nat) (hK : transitionStart physicalScale + 1 <= K) :
    CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale)) K :=
  transportPositiveRoutingAt (Nat.add_sub_of_le hK)
    (observableCertificateShiftedRoutingAt certificate
      (K - (transitionStart physicalScale + 1)))

theorem MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate.sharedFloor_le_finiteCapacityMarginAt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (certificate :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
        trajectory transitionStart physicalScale)
    (K : Nat) (hK : transitionStart physicalScale + 1 <= K) :
    matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale <=
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductFiniteCapacityMargin
        (observableCertificateRoutingAt certificate K hK) := by
  unfold observableCertificateRoutingAt
  rw [finiteCapacityMargin_transportPositiveRoutingAt]
  exact
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate.sharedFloor_le_shiftedFiniteCapacityMargin
      certificate (K - (transitionStart physicalScale + 1))

def observableCertificateToAdaptiveFiniteCapacityCheckSuccess
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (certificate :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
        trajectory transitionStart physicalScale) :
    FixedNomeCofinalSpinCubeOffRayResidualAdaptiveFiniteCapacityCheckSuccess
      (trajectory.nome_pos physicalScale)
      (eventualExplicitRayCapacity trajectory
        (fun scale => transitionStart scale + 1) physicalScale) where
  routing := fun K hK =>
    observableCertificateRoutingAt certificate K (by
      simpa only [eventualExplicitRayCapacity_start] using hK)
  check_success := by
    intro K hK
    have hK' : transitionStart physicalScale + 1 <= K := by
      simpa only [eventualExplicitRayCapacity_start] using hK
    apply adaptiveFiniteCapacityMarginCheck_complete
    change matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale <=
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductFiniteCapacityMargin
        (observableCertificateRoutingAt certificate K hK')
    exact
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate.sharedFloor_le_finiteCapacityMarginAt
        certificate K hK'

/-! ## 3. The scale-wise family contracts directly to physical carriers -/

def observableCertificatesToEventualAdaptiveCapacityCheckProducer
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (transitionStart : Nat -> Nat)
    (certificates : forall physicalScale,
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
        trajectory transitionStart physicalScale) :
    MatchedPhysicalDynamicExplicitRayEventualAdaptiveCapacityCheckProducer
      trajectory where
  transitionStart := fun scale => transitionStart scale + 1
  capacityCheck := fun scale =>
    observableCertificateToAdaptiveFiniteCapacityCheckSuccess
      (certificates scale)

def observableCertificatesToLocalProducer
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (transitionStart : Nat -> Nat)
    (certificates : forall physicalScale,
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
        trajectory transitionStart physicalScale) :
    trajectory.LocalProducer :=
  (observableCertificatesToEventualAdaptiveCapacityCheckProducer
    transitionStart certificates).toLocalProducer

def observableCertificatesToCompletedFamily
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (transitionStart : Nat -> Nat)
    (certificates : forall physicalScale,
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
        trajectory transitionStart physicalScale) :
    DynamicVacuumSectorCompletedFamily 0 :=
  trajectory.toCompletedFamily
    (observableCertificatesToLocalProducer transitionStart certificates)

def observableCertificatesToNormalizedStrengthLaw
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (transitionStart : Nat -> Nat)
    (certificates : forall physicalScale,
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
        trajectory transitionStart physicalScale) :
    DynamicVacuumSectorNormalizedStrengthLaw
      (observableCertificatesToCompletedFamily transitionStart certificates) :=
  trajectory.toNormalizedStrengthLaw
    (observableCertificatesToLocalProducer transitionStart certificates)

/-! ## Axiom audit -/

#print axioms matchedEventualCanonicalSupportSharedFloor_le_one
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate.sharedFloor_le_finiteCapacityMargin
#print axioms observableCertificateRoutingAt
#print axioms transportPositiveRoutingAt
#print axioms finiteCapacityMargin_transportPositiveRoutingAt
#print axioms observableCertificateShiftedRoutingAt
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate.sharedFloor_le_shiftedFiniteCapacityMargin
#print axioms
  MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate.sharedFloor_le_finiteCapacityMarginAt
#print axioms observableCertificateToAdaptiveFiniteCapacityCheckSuccess
#print axioms observableCertificatesToEventualAdaptiveCapacityCheckProducer
#print axioms observableCertificatesToLocalProducer
#print axioms observableCertificatesToCompletedFamily
#print axioms observableCertificatesToNormalizedStrengthLaw

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualAdaptiveObservableTransitionProductCompiler
