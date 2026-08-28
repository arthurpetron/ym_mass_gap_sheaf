/-
# Pay exact adaptive debt with the explicit weighted route ceiling

The exact adaptive new-endpoint routing is definitionally the constructed
deleted-support simple routing.  Its weighted-congestion theorem therefore
bounds the literal observable load by the explicit prefix/endpoint weight sum
times the later carrier length.  Monotonicity of same-edge normalization turns
that load comparison into a normalized-debt comparison, and finite maximum
monotonicity contracts it to one scalar ceiling-debt maximum.

Consequently a bound on

  transported data-deficit maximum + constructed ceiling-debt maximum

pays the sharper exact scalar frontier and hence compiles to the exact
all-cutoff observable certificate.

No ceiling-payment bound or initial strict closure is inhabited here.  No
regional tail, completed gap, continuum limit, continuum Yang--Mills theory,
isolated vacuum, or Clay conclusion is asserted.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveScalarPaymentCompiler
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNewCeilingDebtCompiler

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCeilingPaymentCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCanonicalSlackCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCapacityPartitionCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveScalarPaymentCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffObservableCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedConnectivityCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNewCeilingDebtCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedResidualCapacityCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedSimpleRoutingWeightedCongestion
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTransportedNewEdgeCanonicalDomination
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.SummableRationalStepVariationPrefixTailClosure

private theorem listQMaxZero_mono_local
    {State : Type} (left right : State -> Q')
    (hle : forall state, left state <= right state) :
    forall states : List State,
      listQMaxZero left states <= listQMaxZero right states
  | [] => Q'.le_refl' 0
  | state :: states => by
      unfold listQMaxZero
      apply (Q'.max'_le_iff' _ _ _).mpr
      constructor
      · exact Q'.le_trans' _ _ _ (hle state)
          (Q'.le_max'_left _ _)
      · exact Q'.le_trans' _ _ _
          (listQMaxZero_mono_local left right hle states)
          (Q'.le_max'_right _ _)

/-! ## 1. The explicit ceiling dominates the literal adaptive-new load -/

theorem matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointLoad_le_weightedCeiling
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) :
    matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointLoadOnPair
        trajectory transitionStart physicalScale cutoffOffset edge <=
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveWeightedCeilingOnPair
        (matchedEventualActivatedDeletedSupportConstructedPathFamilyAt
          trajectory transitionStart physicalScale cutoffOffset)
        edge := by
  exact
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveWeightedLoad_le_prefixEndpointWeightSum_mul_carrierLength
      (matchedEventualActivatedDeletedSupportConstructedPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
      edge

theorem matchedEventualActivatedDeletedSupportNewCeilingDebt_eqv_fromLoad
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (paths :
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset)
    (edge : Nat × Nat) :
    matchedEventualActivatedDeletedSupportNewCeilingDebtOnPair
        trajectory transitionStart physicalScale cutoffOffset paths edge =
      matchedEventualCapacityDebtFromLoadOnPair
        trajectory transitionStart physicalScale (cutoffOffset + 1) edge
        (MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportPathFamilyAt.simpleAdaptiveWeightedCeilingOnPair
          paths edge) := by
  rfl

theorem matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebt_le_ceilingDebt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) :
    matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtOnPair
        trajectory transitionStart physicalScale cutoffOffset edge <=
      matchedEventualActivatedDeletedSupportNewCeilingDebtOnPair
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualActivatedDeletedSupportConstructedPathFamilyAt
          trajectory transitionStart physicalScale cutoffOffset)
        edge := by
  rw [matchedEventualActivatedDeletedSupportNewCeilingDebt_eqv_fromLoad]
  exact matchedEventualCapacityDebtFromLoadOnPair_mono
    trajectory transitionStart physicalScale (cutoffOffset + 1) edge _ _
    (matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointLoad_le_weightedCeiling
      trajectory transitionStart physicalScale cutoffOffset edge)

/-! ## 2. Finite maximum contraction -/

def matchedEventualActivatedDeletedSupportConstructedNewCeilingDebtMaximum
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Q' :=
  listQMaxZero
    (matchedEventualActivatedDeletedSupportNewCeilingDebtOnPair
      trajectory transitionStart physicalScale cutoffOffset
      (matchedEventualActivatedDeletedSupportConstructedPathFamilyAt
        trajectory transitionStart physicalScale cutoffOffset))
    (matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (cutoffOffset + 1))

theorem matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtMaximum_le_constructedCeilingMaximum
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualActivatedDeletedSupportConstructedNewCeilingDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtMaximum
    matchedEventualActivatedDeletedSupportConstructedNewCeilingDebtMaximum
  apply listQMaxZero_mono_local
  intro edge
  exact
    matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebt_le_ceilingDebt
      trajectory transitionStart physicalScale cutoffOffset edge

/-! ## 3. The explicit ceiling scalar pays the exact observable frontier -/

structure MatchedEventualActivatedDeletedSupportAllCutoffConstructedCeilingScalarPayment
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale : Nat) : Type 1 where
  envelope : MatchedEventualCanonicalCorrelatedCapacityDebtEnvelope
    trajectory transitionStart physicalScale
  tailAllowance : Q'
  tailAllowance_pos : (0 : Q') < tailAllowance
  margin : Q'
  initial_closure_with_margin :
    (matchedEventualCanonicalRoutedCapacityDebtMaximum
          trajectory transitionStart physicalScale 0 +
        prefixTailTotalBudget
          (matchedEventualCanonicalRoutedCapacityDebtMaximumVariation envelope)
          tailAllowance) + margin <=
      (1 : Q')
  ceiling_payment_le_margin : forall cutoffOffset,
    matchedEventualCanonicalTransportedBridgeDataDeficitMaximum
          trajectory transitionStart physicalScale cutoffOffset +
        matchedEventualActivatedDeletedSupportConstructedNewCeilingDebtMaximum
          trajectory transitionStart physicalScale cutoffOffset <=
      margin

def MatchedEventualActivatedDeletedSupportAllCutoffConstructedCeilingScalarPayment.toExactScalarPayment
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (data :
      MatchedEventualActivatedDeletedSupportAllCutoffConstructedCeilingScalarPayment
        trajectory transitionStart physicalScale) :
    MatchedEventualActivatedDeletedSupportAllCutoffExactAdaptiveScalarPayment
      trajectory transitionStart physicalScale where
  envelope := data.envelope
  tailAllowance := data.tailAllowance
  tailAllowance_pos := data.tailAllowance_pos
  margin := data.margin
  initial_closure_with_margin := data.initial_closure_with_margin
  payment_le_margin := by
    intro cutoffOffset
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_left
        (matchedEventualCanonicalTransportedBridgeDataDeficitMaximum
          trajectory transitionStart physicalScale cutoffOffset)
        _ _
        (matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtMaximum_le_constructedCeilingMaximum
          trajectory transitionStart physicalScale cutoffOffset))
      (data.ceiling_payment_le_margin cutoffOffset)

def MatchedEventualActivatedDeletedSupportAllCutoffConstructedCeilingScalarPayment.toObservableCertificate
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (data :
      MatchedEventualActivatedDeletedSupportAllCutoffConstructedCeilingScalarPayment
        trajectory transitionStart physicalScale) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
      trajectory transitionStart physicalScale :=
  data.toExactScalarPayment.toObservableCertificate

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCeilingPaymentCompiler

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCeilingPaymentCompiler.matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointLoad_le_weightedCeiling
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCeilingPaymentCompiler.matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebt_le_ceilingDebt
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCeilingPaymentCompiler.matchedEventualActivatedDeletedSupportExactAdaptiveNewEndpointDebtMaximum_le_constructedCeilingMaximum
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtExactAdaptiveCeilingPaymentCompiler.MatchedEventualActivatedDeletedSupportAllCutoffConstructedCeilingScalarPayment.toObservableCertificate
