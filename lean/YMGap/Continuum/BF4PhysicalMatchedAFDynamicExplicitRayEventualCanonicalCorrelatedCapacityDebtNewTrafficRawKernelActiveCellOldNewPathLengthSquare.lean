/-
# Old--new raw capacity: face-specific quadratic path scale

The division-free old--new interface leaves the literal route factor
`pathLength * directedMultiplicity`.  The existing routed-path compiler proves
that directed multiplicity is at most total path length, even when the route
repeats edges.  This module preserves the old--new face mask while substituting
that checked quadratic path bound.

The primary maximum is taken only over old--new endpoints on the unchanged
literal new-endpoint list.  Its pointwise summands are also compared with the
existing unmasked path-length square as an explicit fallback precursor.  No
path-growth estimate,
raw-capacity lower bound, mass decay estimate, continuum theory, or Clay
conclusion is supplied.  No `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or declaration marked noncomputable is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewRawCapacityCrossMultiplication
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthFactorization

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewPathLengthSquare

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceCapacityBalance
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceEndpointRatio
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewMassSplit
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewRawCapacityCrossMultiplication
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelPathLengthFactorization
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.SummableInverseSquare

private def oldNewShellPairDecidable
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (pair : Nat × Nat) :
    Decidable
      (MatchedEventualCanonicalPairInOldNewShell
        trajectory transitionStart physicalScale offset pair) := by
  unfold MatchedEventualCanonicalPairInOldNewShell
    MatchedEventualCanonicalIndexInNewShell
  infer_instance

private theorem listQMaxZero_mono_on_local
    {A : Type} (left right : A -> Q') : forall items : List A,
      (forall item, item ∈ items -> left item <= right item) ->
      listQMaxZero left items <= listQMaxZero right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hall => by
      unfold listQMaxZero
      apply (Q'.max'_le_iff' _ _ _).mpr
      constructor
      · exact Q'.le_trans' _ _ _
          (hall head List.mem_cons_self)
          (Q'.le_max'_left _ _)
      · exact Q'.le_trans' _ _ _
          (listQMaxZero_mono_on_local left right tail
            (fun item hitem =>
              hall item (List.mem_cons_of_mem head hitem)))
          (Q'.le_max'_right _ _)

private theorem listQMaxZero_nonnegative_on_local
    {A : Type} (value : A -> Q') : forall items : List A,
      (forall item, item ∈ items -> (0 : Q') <= value item) ->
      (0 : Q') <= listQMaxZero value items
  | [], _ => Q'.le_refl' 0
  | head :: _tail, hvalue =>
      Q'.le_trans' _ _ _
        (hvalue head List.mem_cons_self)
        (Q'.le_max'_left _ _)

private theorem correctedSlabIncrement_nonnegative_local
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
  exact slabParametricKCutoffIncrement_nonnegative
    (Q'.le_of_lt (trajectory.nome_pos physicalScale)) _ _ _

private theorem componentMergerResidual_nonnegative_local
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceComponentMergerResidual
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceComponentMergerResidual
  exact
    YMGap.Continuum.BF4PhysicalCutoffVacuumSectorNewMassComponentSplit.centralPhysicalFiniteNewComponentMergerMass_nonnegative
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale)) _ _ _

/-! ## 1. Face-specific routed path-length-square maximum -/

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareOnPair
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (endpointPair : Nat × Nat) : Q' := by
  letI := oldNewShellPairDecidable
    trajectory transitionStart physicalScale cutoffOffset endpointPair
  exact
    if MatchedEventualCanonicalPairInOldNewShell
        trajectory transitionStart physicalScale cutoffOffset endpointPair then
      matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareOnPair
        trajectory transitionStart physicalScale cutoffOffset endpointPair
    else 0

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareOnPair_nonnegative
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (endpointPair : Nat × Nat) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareOnPair
        trajectory transitionStart physicalScale cutoffOffset endpointPair := by
  letI := oldNewShellPairDecidable
    trajectory transitionStart physicalScale cutoffOffset endpointPair
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareOnPair
  by_cases hface : MatchedEventualCanonicalPairInOldNewShell
      trajectory transitionStart physicalScale cutoffOffset endpointPair
  · rw [if_pos hface]
    exact
      matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareOnPair_nonnegative
        trajectory transitionStart physicalScale cutoffOffset endpointPair
  · rw [if_neg hface]
    exact Q'.le_refl' 0

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareMaximum
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Q' :=
  listQMaxZero
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareOnPair
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareMaximum_nonnegative
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareMaximum
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareMaximum
  apply listQMaxZero_nonnegative_on_local
  intro endpointPair _
  exact
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareOnPair_nonnegative
      trajectory transitionStart physicalScale cutoffOffset endpointPair

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorOnCell_le_routedPathLengthSquareOnPair
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorOnCell
        trajectory transitionStart physicalScale cutoffOffset cell <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareOnPair
        trajectory transitionStart physicalScale cutoffOffset cell.2 := by
  letI := oldNewShellPairDecidable
    trajectory transitionStart physicalScale cutoffOffset cell.2
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorOnCell
    YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFacePayment.matchedEventualCanonicalNewEndpointTrafficOldNewFaceAllowance
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareOnPair
  by_cases hface : MatchedEventualCanonicalPairInOldNewShell
      trajectory transitionStart physicalScale cutoffOffset cell.2
  · rw [if_pos hface, if_pos hface]
    exact
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficRouteFactorOnPair_le_routedPathLengthSquare
        trajectory transitionStart physicalScale cutoffOffset
        (YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding.matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset cell.1)
        cell.2
  · rw [if_neg hface, if_neg hface]
    exact Q'.le_refl' 0

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair_le_routedPathLengthSquareMaximum
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair
        trajectory transitionStart physicalScale cutoffOffset pair <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareMaximum
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareMaximum
  apply listQMaxZero_mono_on_local
  intro endpointPair _
  exact
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorOnCell_le_routedPathLengthSquareOnPair
      trajectory transitionStart physicalScale cutoffOffset
      (pair, endpointPair)

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareOnPair_le_unmasked
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (endpointPair : Nat × Nat) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareOnPair
        trajectory transitionStart physicalScale cutoffOffset endpointPair <=
      matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareOnPair
        trajectory transitionStart physicalScale cutoffOffset endpointPair := by
  letI := oldNewShellPairDecidable
    trajectory transitionStart physicalScale cutoffOffset endpointPair
  unfold
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareOnPair
  by_cases hface : MatchedEventualCanonicalPairInOldNewShell
      trajectory transitionStart physicalScale cutoffOffset endpointPair
  · rw [if_pos hface]
    exact Q'.le_refl' _
  · rw [if_neg hface]
    exact
      matchedEventualCanonicalNewEndpointTrafficRoutedPathLengthSquareOnPair_nonnegative
        trajectory transitionStart physicalScale cutoffOffset endpointPair

/-! ## 2. Quadratic-path interfaces compile to raw capacity controls -/

structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitPathLengthSquareRawCapacityInverseSquareControl
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
          matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareMaximum
            trajectory transitionStart physicalScale cutoffOffset) <=
      (coefficient * invSqTerm offset offset_at_least_two cutoffOffset) *
        matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitPathLengthSquareRawCapacityInverseSquareControl.toRawCapacityControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (control : MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitPathLengthSquareRawCapacityInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitRawCapacityInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two where
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  envelope_le := by
    intro cutoffOffset pair hpair
    have hmass0 : (0 : Q') <=
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceCorrectedSlabIncrement
            trajectory transitionStart physicalScale cutoffOffset +
          matchedEventualCanonicalNewEndpointTrafficOldNewFaceComponentMergerResidual
            trajectory transitionStart physicalScale cutoffOffset :=
      Q'.add_le_add
        (correctedSlabIncrement_nonnegative_local
          trajectory transitionStart physicalScale cutoffOffset)
        (componentMergerResidual_nonnegative_local
          trajectory transitionStart physicalScale cutoffOffset)
    have hmassRoute := Q'.mul_le_mul_of_nonneg_left _ _ _
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair_le_routedPathLengthSquareMaximum
        trajectory transitionStart physicalScale cutoffOffset pair)
      hmass0
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hmassRoute
        (Q'.le_of_lt
          (matchedEventualCanonicalSupportSharedFloor_pos
            trajectory transitionStart physicalScale)))
      (control.envelope_le cutoffOffset pair hpair)

theorem matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewMassSplitPathLengthSquareRawCapacity_and_otherFaces
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (oldNew : MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitPathLengthSquareRawCapacityInverseSquareControl
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
  matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewMassSplitRawCapacity_and_otherFaces
    oldNew.toRawCapacityControl newOld newNew cutoffOffset

structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerPathLengthSquareRawCapacityInverseSquareControl
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
          matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareMaximum
            trajectory transitionStart physicalScale cutoffOffset) <=
      (coefficient * invSqTerm offset offset_at_least_two cutoffOffset) *
        matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerPathLengthSquareRawCapacityInverseSquareControl.toRawCapacityControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (control : MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerPathLengthSquareRawCapacityInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerRawCapacityInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two where
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  noMerger := control.noMerger
  envelope_le := by
    intro cutoffOffset pair hpair
    have hmassRoute := Q'.mul_le_mul_of_nonneg_left _ _ _
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair_le_routedPathLengthSquareMaximum
        trajectory transitionStart physicalScale cutoffOffset pair)
      (correctedSlabIncrement_nonnegative_local
        trajectory transitionStart physicalScale cutoffOffset)
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hmassRoute
        (Q'.le_of_lt
          (matchedEventualCanonicalSupportSharedFloor_pos
            trajectory transitionStart physicalScale)))
      (control.envelope_le cutoffOffset pair hpair)

theorem matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewNoMergerPathLengthSquareRawCapacity_and_otherFaces
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (oldNew : MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerPathLengthSquareRawCapacityInverseSquareControl
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
  matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewNoMergerRawCapacity_and_otherFaces
    oldNew.toRawCapacityControl newOld newNew cutoffOffset

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewPathLengthSquare

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewPathLengthSquare.matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareOnPair_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewPathLengthSquare.matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareMaximum_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewPathLengthSquare.matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorOnCell_le_routedPathLengthSquareOnPair
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewPathLengthSquare.matchedEventualCanonicalNewEndpointTrafficOldNewFaceRouteFactorMaximumOnCurrentPair_le_routedPathLengthSquareMaximum
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewPathLengthSquare.matchedEventualCanonicalNewEndpointTrafficOldNewFaceRoutedPathLengthSquareOnPair_le_unmasked
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewPathLengthSquare.MatchedEventualCanonicalNewEndpointTrafficOldNewFaceMassSplitPathLengthSquareRawCapacityInverseSquareControl.toRawCapacityControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewPathLengthSquare.matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewMassSplitPathLengthSquareRawCapacity_and_otherFaces
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewPathLengthSquare.MatchedEventualCanonicalNewEndpointTrafficOldNewFaceNoMergerPathLengthSquareRawCapacityInverseSquareControl.toRawCapacityControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewPathLengthSquare.matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_oldNewNoMergerPathLengthSquareRawCapacity_and_otherFaces
