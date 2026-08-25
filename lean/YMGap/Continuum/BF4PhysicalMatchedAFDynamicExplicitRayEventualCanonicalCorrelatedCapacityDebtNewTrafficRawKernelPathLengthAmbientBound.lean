/-
# Explicit ambient bound for matched new-endpoint route length

The path-length factorization leaves a located quadratic route maximum on the
actual new-endpoint list.  Membership in that list says constructively that
the endpoint pair is not embedded-old on both coordinates.  The transported
routing therefore takes its later-cutoff canonical branch on every such pair.
That branch is definitionally the loop-erased simple positive path.

The existing simple-path theorem bounds its edge length by the later vacuum-
sector cardinality, and the existing ambient enumeration bounds that sector
by the full lower-face Cartesian carrier.  This module compiles those facts
into an explicit later ambient carrier-square envelope for the same exact
new-debt observable.

No reciprocal raw-kernel bound, new-block-mass decay, inverse-square estimate,
no-merger certificate, continuum theory, or Clay conclusion is supplied.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or declaration
marked noncomputable is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCarrierAmbientBound
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthFactorization

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthAmbientBound

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCarrierAmbientBound
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveFactorization
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthFactorization
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportProxy
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem listQMaxZero_le_of_member_bound_local
    {State : Type} (value : State -> Q') (bound : Q') :
    forall states : List State,
      (0 : Q') <= bound ->
      (forall state, state ∈ states -> value state <= bound) ->
      listQMaxZero value states <= bound
  | [], hbound, _ => hbound
  | head :: tail, hbound, hall => by
      unfold listQMaxZero
      exact (Q'.max'_le_iff' _ _ _).mpr
        ⟨hall head List.mem_cons_self,
          listQMaxZero_le_of_member_bound_local value bound tail hbound
            (fun state hstate =>
              hall state (List.mem_cons_of_mem head hstate))⟩

/-! ## 1. New endpoint pairs force the later canonical routing branch -/

theorem matchedEventualCanonicalNewEndpointPair_not_both_embeddedOld
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (endpointPair : Nat × Nat)
    (hendpointPair : endpointPair ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    ¬ (endpointPair.1 ∈
          matchedEventualCanonicalEmbeddedOldIndexCarrier
            trajectory transitionStart physicalScale cutoffOffset ∧
        endpointPair.2 ∈
          matchedEventualCanonicalEmbeddedOldIndexCarrier
            trajectory transitionStart physicalScale cutoffOffset) := by
  have hfiltered := List.mem_filter.mp hendpointPair
  intro hboth
  have holdB :
      matchedEventualCanonicalTransportedBridgeEndpointPairOldB
          trajectory transitionStart physicalScale cutoffOffset endpointPair =
        true := by
    unfold matchedEventualCanonicalTransportedBridgeEndpointPairOldB
    exact decide_eq_true hboth
  have hnewB := hfiltered.2
  rw [holdB] at hnewB
  cases hnewB

theorem matchedEventualCanonicalTransportedRoutingAtNext_path_eq_laterCanonical_of_not_both_embeddedOld
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (left right : Nat)
    (hleft : left ∈
      matchedEventualCanonicalVacuumSectorIndices
        trajectory transitionStart physicalScale (cutoffOffset + 1))
    (hright : right ∈
      matchedEventualCanonicalVacuumSectorIndices
        trajectory transitionStart physicalScale (cutoffOffset + 1))
    (hnotOld :
      ¬ (left ∈ matchedEventualCanonicalEmbeddedOldIndexCarrier
            trajectory transitionStart physicalScale cutoffOffset ∧
          right ∈ matchedEventualCanonicalEmbeddedOldIndexCarrier
            trajectory transitionStart physicalScale cutoffOffset)) :
    (matchedEventualCanonicalTransportedRoutingAtNext
        trajectory transitionStart physicalScale cutoffOffset).path
        left right hleft hright =
      (matchedEventualCanonicalRoutingAt
        trajectory transitionStart physicalScale (cutoffOffset + 1)).path
        left right hleft hright := by
  unfold matchedEventualCanonicalTransportedRoutingAtNext
  dsimp only
  by_cases hleftOld : left ∈
      matchedEventualCanonicalEmbeddedOldIndexCarrier
        trajectory transitionStart physicalScale cutoffOffset
  · have hrightOld : right ∉
        matchedEventualCanonicalEmbeddedOldIndexCarrier
          trajectory transitionStart physicalScale cutoffOffset := by
      intro hrightOld
      exact hnotOld ⟨hleftOld, hrightOld⟩
    rw [dif_pos hleftOld, dif_neg hrightOld]
  · rw [dif_neg hleftOld]

/-! ## 2. Actual quadratic route maximum is bounded by the later carrier -/

def matchedEventualCanonicalNewEndpointTrafficLaterSimpleCarrierSquareScale
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Q' :=
  centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale
    (trajectory.nome physicalScale)
    (Q'.le_of_lt (trajectory.nome_pos physicalScale))
    (transitionStart physicalScale + (cutoffOffset + 1)) 0

theorem matchedEventualCanonicalNewEndpointTrafficLaterSimpleCarrierSquareScale_pos
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    (0 : Q') <
      matchedEventualCanonicalNewEndpointTrafficLaterSimpleCarrierSquareScale
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficLaterSimpleCarrierSquareScale
  exact centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale_pos
    (trajectory.nome physicalScale)
    (Q'.le_of_lt (trajectory.nome_pos physicalScale))
    (transitionStart physicalScale + (cutoffOffset + 1)) 0

theorem matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareOnPair_le_laterSimpleCarrierSquareScale
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (endpointPair : Nat × Nat)
    (hendpointPair : endpointPair ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareOnPair
        trajectory transitionStart physicalScale cutoffOffset endpointPair <=
      matchedEventualCanonicalNewEndpointTrafficLaterSimpleCarrierSquareScale
        trajectory transitionStart physicalScale cutoffOffset := by
  have hfiltered := List.mem_filter.mp hendpointPair
  have hresidual := hfiltered.1
  have hfull :=
    centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hresidual
  have hnotOld :=
    matchedEventualCanonicalNewEndpointPair_not_both_embeddedOld
      trajectory transitionStart physicalScale cutoffOffset endpointPair
      hendpointPair
  have hpath :=
    matchedEventualCanonicalTransportedRoutingAtNext_path_eq_laterCanonical_of_not_both_embeddedOld
      trajectory transitionStart physicalScale cutoffOffset
      endpointPair.1 endpointPair.2 hfull.1 hfull.2 hnotOld
  unfold
    matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareOnPair
  rw [dif_pos hresidual, hpath]
  unfold
    matchedEventualCanonicalNewEndpointTrafficLaterSimpleCarrierSquareScale
    matchedEventualCanonicalRoutingAt
    canonicalCentralPhysicalFiniteVacuumSectorPositiveRoutingAt
  exact
    centralPhysicalFiniteVacuumSectorSimplePath_quadraticLength_le_scale
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1)) 0
      endpointPair.1 endpointPair.2 hfull.1 hfull.2

theorem matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareMaximum_le_laterSimpleCarrierSquareScale
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficLaterSimpleCarrierSquareScale
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareMaximum
  apply listQMaxZero_le_of_member_bound_local
  · exact Q'.le_of_lt
      (matchedEventualCanonicalNewEndpointTrafficLaterSimpleCarrierSquareScale_pos
        trajectory transitionStart physicalScale cutoffOffset)
  · intro endpointPair hendpointPair
    exact
      matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareOnPair_le_laterSimpleCarrierSquareScale
        trajectory transitionStart physicalScale cutoffOffset endpointPair
        hendpointPair

def matchedEventualCanonicalNewEndpointTrafficLaterAmbientCarrierSquareScale
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (_trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Q' :=
  centralPhysicalFiniteVacuumSectorAmbientCarrierSquareScale
    (transitionStart physicalScale + (cutoffOffset + 1)) 0

theorem matchedEventualCanonicalNewEndpointTrafficLaterAmbientCarrierSquareScale_pos
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    (0 : Q') <
      matchedEventualCanonicalNewEndpointTrafficLaterAmbientCarrierSquareScale
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficLaterAmbientCarrierSquareScale
  exact centralPhysicalFiniteVacuumSectorAmbientCarrierSquareScale_pos
    (transitionStart physicalScale + (cutoffOffset + 1)) 0

theorem matchedEventualCanonicalNewEndpointTrafficLaterAmbientCarrierSquareScale_eq_explicit
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointTrafficLaterAmbientCarrierSquareScale
        trajectory transitionStart physicalScale cutoffOffset =
      1 + Q'.ofNat
        (((transitionStart physicalScale + (cutoffOffset + 1) + 1) ^ 24) *
          ((transitionStart physicalScale + (cutoffOffset + 1) + 1) ^ 24)) := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficLaterAmbientCarrierSquareScale
    centralPhysicalFiniteVacuumSectorAmbientCarrierSquareScale
    centralPhysicalFiniteVacuumSectorAmbientCarrierSize
  rw [centralLowerFaceIds_zero_length]

theorem matchedEventualCanonicalNewEndpointTrafficLaterSimpleCarrierSquareScale_le_ambient
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointTrafficLaterSimpleCarrierSquareScale
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficLaterAmbientCarrierSquareScale
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficLaterSimpleCarrierSquareScale
    matchedEventualCanonicalNewEndpointTrafficLaterAmbientCarrierSquareScale
  exact centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale_le_ambient
    (trajectory.nome physicalScale)
    (Q'.le_of_lt (trajectory.nome_pos physicalScale))
    (transitionStart physicalScale + (cutoffOffset + 1)) 0

theorem matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareMaximum_le_laterAmbientCarrierSquareScale
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficLaterAmbientCarrierSquareScale
        trajectory transitionStart physicalScale cutoffOffset :=
  Q'.le_trans' _ _ _
    (matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareMaximum_le_laterSimpleCarrierSquareScale
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalNewEndpointTrafficLaterSimpleCarrierSquareScale_le_ambient
      trajectory transitionStart physicalScale cutoffOffset)

/-! ## 3. Explicit ambient amplification and exact new-debt contraction -/

def matchedEventualCanonicalNewEndpointTrafficAmbientPathAmplificationEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Q' :=
  matchedEventualCanonicalSupportSharedFloor
      trajectory transitionStart physicalScale *
    (matchedEventualCanonicalNewEndpointTrafficLaterAmbientCarrierSquareScale
        trajectory transitionStart physicalScale cutoffOffset *
      matchedEventualCanonicalNewEndpointTrafficActiveCapacityReciprocalMaximum
        trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficAmbientPathAmplificationEnvelope_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficAmbientPathAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficAmbientPathAmplificationEnvelope
  exact Q'.mul_nonneg _ _
    (Q'.le_of_lt
      (matchedEventualCanonicalSupportSharedFloor_pos
        trajectory transitionStart physicalScale))
    (Q'.mul_nonneg _ _
      (Q'.le_of_lt
        (matchedEventualCanonicalNewEndpointTrafficLaterAmbientCarrierSquareScale_pos
          trajectory transitionStart physicalScale cutoffOffset))
      (matchedEventualCanonicalNewEndpointTrafficActiveCapacityReciprocalMaximum_nonnegative
        trajectory transitionStart physicalScale cutoffOffset))

theorem matchedEventualCanonicalNewEndpointTrafficPathFactorizedAmplificationEnvelope_le_ambientPathEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointTrafficPathFactorizedAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficAmbientPathAmplificationEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficPathFactorizedAmplificationEnvelope
    matchedEventualCanonicalNewEndpointTrafficAmbientPathAmplificationEnvelope
  apply Q'.mul_le_mul_of_nonneg_left
  · exact Q'.mul_le_mul_of_nonneg_right _ _ _
      (matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareMaximum_le_laterAmbientCarrierSquareScale
        trajectory transitionStart physicalScale cutoffOffset)
      (matchedEventualCanonicalNewEndpointTrafficActiveCapacityReciprocalMaximum_nonnegative
        trajectory transitionStart physicalScale cutoffOffset)
  · exact Q'.le_of_lt
      (matchedEventualCanonicalSupportSharedFloor_pos
        trajectory transitionStart physicalScale)

def matchedEventualCanonicalNewEndpointTrafficAmbientPathNewBlockDebtEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Q' :=
  (Q'.ofNat 2 *
      matchedEventualCanonicalLaterNewBlockMass
        trajectory transitionStart physicalScale cutoffOffset) *
    matchedEventualCanonicalNewEndpointTrafficAmbientPathAmplificationEnvelope
      trajectory transitionStart physicalScale cutoffOffset

theorem matchedEventualCanonicalNewEndpointTrafficAmbientPathNewBlockDebtEnvelope_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficAmbientPathNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficAmbientPathNewBlockDebtEnvelope
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (by decide)
      (matchedEventualCanonicalLaterNewBlockMass_nonnegative
        trajectory transitionStart physicalScale cutoffOffset))
    (matchedEventualCanonicalNewEndpointTrafficAmbientPathAmplificationEnvelope_nonnegative
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficPathFactorizedNewBlockDebtEnvelope_le_ambientPathNewBlockDebtEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointTrafficPathFactorizedNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficAmbientPathNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficPathFactorizedNewBlockDebtEnvelope
    matchedEventualCanonicalNewEndpointTrafficAmbientPathNewBlockDebtEnvelope
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (matchedEventualCanonicalNewEndpointTrafficPathFactorizedAmplificationEnvelope_le_ambientPathEnvelope
      trajectory transitionStart physicalScale cutoffOffset)
    (Q'.mul_nonneg _ _ (by decide)
      (matchedEventualCanonicalLaterNewBlockMass_nonnegative
        trajectory transitionStart physicalScale cutoffOffset))

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum_le_ambientPathNewBlockDebtEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalNewEndpointTrafficAmbientPathNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset :=
  Q'.le_trans' _ _ _
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum_le_pathFactorizedNewBlockDebtEnvelope
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalNewEndpointTrafficPathFactorizedNewBlockDebtEnvelope_le_ambientPathNewBlockDebtEnvelope
      trajectory transitionStart physicalScale cutoffOffset)

/-! ## 4. Type-level inverse-square interface -/

structure MatchedEventualCanonicalNewEndpointTrafficAmbientPathInverseSquareControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat) : Type 1 where
  offset : Nat
  offset_at_least_two : 2 <= offset
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  envelope_le : forall cutoffOffset : Nat,
    matchedEventualCanonicalNewEndpointTrafficAmbientPathNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset <=
      coefficient *
        invSqTerm offset offset_at_least_two cutoffOffset

def MatchedEventualCanonicalNewEndpointTrafficAmbientPathInverseSquareControl.toPathFactorizedControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficAmbientPathInverseSquareControl
        trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalNewEndpointTrafficPathFactorizedInverseSquareControl
      trajectory transitionStart physicalScale where
  offset := control.offset
  offset_at_least_two := control.offset_at_least_two
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  envelope_le := fun cutoffOffset =>
    Q'.le_trans' _ _ _
      (matchedEventualCanonicalNewEndpointTrafficPathFactorizedNewBlockDebtEnvelope_le_ambientPathNewBlockDebtEnvelope
        trajectory transitionStart physicalScale cutoffOffset)
      (control.envelope_le cutoffOffset)

theorem MatchedEventualCanonicalNewEndpointTrafficAmbientPathInverseSquareControl.debtMaximum_le
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficAmbientPathInverseSquareControl
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      control.coefficient *
        invSqTerm control.offset control.offset_at_least_two cutoffOffset :=
  control.toPathFactorizedControl.debtMaximum_le cutoffOffset

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthAmbientBound

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthAmbientBound.matchedEventualCanonicalNewEndpointPair_not_both_embeddedOld
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthAmbientBound.matchedEventualCanonicalTransportedRoutingAtNext_path_eq_laterCanonical_of_not_both_embeddedOld
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthAmbientBound.matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareMaximum_le_laterSimpleCarrierSquareScale
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthAmbientBound.matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareMaximum_le_laterAmbientCarrierSquareScale
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthAmbientBound.matchedEventualCanonicalNewEndpointTrafficLaterAmbientCarrierSquareScale_eq_explicit
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthAmbientBound.matchedEventualCanonicalNewEndpointTrafficPathFactorizedAmplificationEnvelope_le_ambientPathEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthAmbientBound.matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum_le_ambientPathNewBlockDebtEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthAmbientBound.MatchedEventualCanonicalNewEndpointTrafficAmbientPathInverseSquareControl.toPathFactorizedControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthAmbientBound.MatchedEventualCanonicalNewEndpointTrafficAmbientPathInverseSquareControl.debtMaximum_le
