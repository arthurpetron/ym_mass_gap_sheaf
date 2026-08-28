/-
# Partition the combined normalized-debt frontier by edge age

The all-cutoff combined debt estimate has two geometrically different lanes.
On an embedded-old edge it retains the transported debt.  On a genuinely new
edge, canonical domination replaces transported debt by the later canonical
debt.  This module records that exact partition and compiles it back to the
single observable-connected certificate.

The new-edge lane is also connected to the existing prefix-plus-tail slack
theorem.  If canonical debt preserves a named scalar margin and the constructed
ceiling debt on every new edge is at most that margin, then the new-edge
combined estimate follows automatically.  Thus the remaining analytic work is
separated into an old-edge transported lane and a new-edge ceiling-to-margin
lane.

No lane is inhabited here.  No regional tail, completed gap, continuum limit,
continuum Yang--Mills theory, isolated vacuum, or Clay conclusion is asserted.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTransportedNewEdgeCanonicalDomination

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtPartitionedCombinedDebtCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNewCeilingDebtCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedNormalizedReserveCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffObservableCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedResidualCapacityCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTransportedNewEdgeCanonicalDomination
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.SummableRationalStepVariationPrefixTailClosure

/-! ## 1. Exact old-edge and new-edge lanes -/

def MatchedEventualActivatedDeletedSupportAllCutoffOldEdgeCombinedNormalizedDebt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale : Nat) : Prop :=
  forall cutoffOffset edge,
    edge ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale (cutoffOffset + 1) ->
      edge ∈ matchedEventualCanonicalEmbeddedOldPairCarrier
          trajectory transitionStart physicalScale cutoffOffset ->
        matchedEventualRoutedCapacityDebtOnPairForRouting
              trajectory transitionStart physicalScale (cutoffOffset + 1)
              (matchedEventualCanonicalTransportedRoutingAtNext
                trajectory transitionStart physicalScale cutoffOffset) edge +
            matchedEventualActivatedDeletedSupportNewCeilingDebtOnPair
              trajectory transitionStart physicalScale cutoffOffset
              (matchedEventualActivatedDeletedSupportConstructedPathFamilyAt
                trajectory transitionStart physicalScale cutoffOffset)
              edge <= (1 : Q')

def MatchedEventualActivatedDeletedSupportAllCutoffNewEdgeCanonicalCombinedNormalizedDebt
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale : Nat) : Prop :=
  forall cutoffOffset edge,
    edge ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale (cutoffOffset + 1) ->
      edge ∉ matchedEventualCanonicalEmbeddedOldPairCarrier
          trajectory transitionStart physicalScale cutoffOffset ->
        matchedEventualCanonicalRoutedCapacityDebtOnPair
              trajectory transitionStart physicalScale (cutoffOffset + 1) edge +
            matchedEventualActivatedDeletedSupportNewCeilingDebtOnPair
              trajectory transitionStart physicalScale cutoffOffset
              (matchedEventualActivatedDeletedSupportConstructedPathFamilyAt
                trajectory transitionStart physicalScale cutoffOffset)
              edge <= (1 : Q')

def matchedEventualActivatedDeletedSupportCombinedNormalizedDebtOfEdgePartition
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (oldEdge :
      MatchedEventualActivatedDeletedSupportAllCutoffOldEdgeCombinedNormalizedDebt
        trajectory transitionStart physicalScale)
    (newEdge :
      MatchedEventualActivatedDeletedSupportAllCutoffNewEdgeCanonicalCombinedNormalizedDebt
        trajectory transitionStart physicalScale) :
    MatchedEventualActivatedDeletedSupportAllCutoffCombinedNormalizedDebt
      trajectory transitionStart physicalScale := by
  intro cutoffOffset edge hedge
  by_cases hold : edge ∈ matchedEventualCanonicalEmbeddedOldPairCarrier
      trajectory transitionStart physicalScale cutoffOffset
  · exact oldEdge cutoffOffset edge hedge hold
  · have hdomination :=
      matchedEventualRoutedCapacityDebtOnPairForTransportedRouting_le_laterCanonical_of_newEdge
        trajectory transitionStart physicalScale cutoffOffset edge hold
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _
        (matchedEventualActivatedDeletedSupportNewCeilingDebtOnPair
          trajectory transitionStart physicalScale cutoffOffset
          (matchedEventualActivatedDeletedSupportConstructedPathFamilyAt
            trajectory transitionStart physicalScale cutoffOffset)
          edge)
        hdomination)
      (newEdge cutoffOffset edge hedge hold)

/-! ## 2. Canonical persistence pays a named new-edge margin -/

def MatchedEventualActivatedDeletedSupportAllCutoffNewEdgeCeilingDebtLeMargin
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale : Nat)
    (margin : Q') : Prop :=
  forall cutoffOffset edge,
    edge ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale (cutoffOffset + 1) ->
      edge ∉ matchedEventualCanonicalEmbeddedOldPairCarrier
          trajectory transitionStart physicalScale cutoffOffset ->
        matchedEventualActivatedDeletedSupportNewCeilingDebtOnPair
            trajectory transitionStart physicalScale cutoffOffset
            (matchedEventualActivatedDeletedSupportConstructedPathFamilyAt
              trajectory transitionStart physicalScale cutoffOffset)
            edge <= margin

def matchedEventualActivatedDeletedSupportNewEdgeCanonicalCombinedNormalizedDebtOfCanonicalMargin
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (envelope : MatchedEventualCanonicalCorrelatedCapacityDebtEnvelope
      trajectory transitionStart physicalScale)
    (tailAllowance : Q')
    (tailAllowance_pos : (0 : Q') < tailAllowance)
    (margin : Q')
    (initial_closure_with_margin :
      (matchedEventualCanonicalRoutedCapacityDebtMaximum
            trajectory transitionStart physicalScale 0 +
          prefixTailTotalBudget
            (matchedEventualCanonicalRoutedCapacityDebtMaximumVariation
              envelope)
            tailAllowance) + margin <=
        (1 : Q'))
    (ceiling :
      MatchedEventualActivatedDeletedSupportAllCutoffNewEdgeCeilingDebtLeMargin
        trajectory transitionStart physicalScale margin) :
    MatchedEventualActivatedDeletedSupportAllCutoffNewEdgeCanonicalCombinedNormalizedDebt
      trajectory transitionStart physicalScale := by
  intro cutoffOffset edge hedge hnew
  have hcanonical :=
    matchedEventualCanonicalRoutedCapacityDebtOnPair_add_margin_le_one
      envelope tailAllowance tailAllowance_pos margin
      initial_closure_with_margin (cutoffOffset + 1) edge hedge
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add_left
      (matchedEventualCanonicalRoutedCapacityDebtOnPair
        trajectory transitionStart physicalScale (cutoffOffset + 1) edge)
      (matchedEventualActivatedDeletedSupportNewCeilingDebtOnPair
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualActivatedDeletedSupportConstructedPathFamilyAt
          trajectory transitionStart physicalScale cutoffOffset)
        edge)
      margin (ceiling cutoffOffset edge hedge hnew))
    hcanonical

def matchedEventualActivatedDeletedSupportCombinedNormalizedDebtOfOldEdgeAndCanonicalMargin
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (oldEdge :
      MatchedEventualActivatedDeletedSupportAllCutoffOldEdgeCombinedNormalizedDebt
        trajectory transitionStart physicalScale)
    (envelope : MatchedEventualCanonicalCorrelatedCapacityDebtEnvelope
      trajectory transitionStart physicalScale)
    (tailAllowance : Q')
    (tailAllowance_pos : (0 : Q') < tailAllowance)
    (margin : Q')
    (initial_closure_with_margin :
      (matchedEventualCanonicalRoutedCapacityDebtMaximum
            trajectory transitionStart physicalScale 0 +
          prefixTailTotalBudget
            (matchedEventualCanonicalRoutedCapacityDebtMaximumVariation
              envelope)
            tailAllowance) + margin <=
        (1 : Q'))
    (ceiling :
      MatchedEventualActivatedDeletedSupportAllCutoffNewEdgeCeilingDebtLeMargin
        trajectory transitionStart physicalScale margin) :
    MatchedEventualActivatedDeletedSupportAllCutoffCombinedNormalizedDebt
      trajectory transitionStart physicalScale :=
  matchedEventualActivatedDeletedSupportCombinedNormalizedDebtOfEdgePartition
    oldEdge
    (matchedEventualActivatedDeletedSupportNewEdgeCanonicalCombinedNormalizedDebtOfCanonicalMargin
      envelope tailAllowance tailAllowance_pos margin
      initial_closure_with_margin ceiling)

def matchedEventualActivatedDeletedSupportObservableCertificateOfEdgePartition
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale : Nat}
    (oldEdge :
      MatchedEventualActivatedDeletedSupportAllCutoffOldEdgeCombinedNormalizedDebt
        trajectory transitionStart physicalScale)
    (newEdge :
      MatchedEventualActivatedDeletedSupportAllCutoffNewEdgeCanonicalCombinedNormalizedDebt
        trajectory transitionStart physicalScale) :
    MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
      trajectory transitionStart physicalScale :=
  (matchedEventualActivatedDeletedSupportCombinedNormalizedDebtOfEdgePartition
    oldEdge newEdge).toObservableCertificate

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtPartitionedCombinedDebtCompiler

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtPartitionedCombinedDebtCompiler.matchedEventualActivatedDeletedSupportCombinedNormalizedDebtOfEdgePartition
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtPartitionedCombinedDebtCompiler.matchedEventualActivatedDeletedSupportNewEdgeCanonicalCombinedNormalizedDebtOfCanonicalMargin
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtPartitionedCombinedDebtCompiler.matchedEventualActivatedDeletedSupportCombinedNormalizedDebtOfOldEdgeAndCanonicalMargin
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtPartitionedCombinedDebtCompiler.matchedEventualActivatedDeletedSupportObservableCertificateOfEdgePartition
