/-
# Three-face active-cell payment for matched new traffic

The exact new-endpoint traffic carrier lies in the later vacuum-pair shell.
That shell is the disjoint union of the old--new, new--old, and new--new
ordered faces relative to the embedded current carrier.  This module uses
those literal faces to split one observable-connected active-cell allowance
into three independently estimable row sums.

The three estimates retain the same cutoff, current pair, endpoint list,
allowance, active cell, numerator, and capacity.  Exact finite-sum algebra
then rejoins them into the preceding active-cell payment compiler.  Thus the
split creates three parallel analytic producers without replacing the debt by
three unrelated observables or discarding the stationary-weight/capacity
correlation.

The shared active-cell payment and all three inverse-square face estimates
remain explicit fields.  No such estimate, continuum theory, or Clay
conclusion is supplied.  No `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or declaration marked noncomputable is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellPayment
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficCarrierBound

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFacePayment

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficCarrierBound
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellPayment
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveFactorization
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private def oldNewShellPairDecidable
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) (pair : Nat × Nat) :
    Decidable (MatchedEventualCanonicalPairInOldNewShell
      trajectory transitionStart physicalScale offset pair) := by
  unfold MatchedEventualCanonicalPairInOldNewShell
    MatchedEventualCanonicalIndexInNewShell
  infer_instance

private def newOldShellPairDecidable
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) (pair : Nat × Nat) :
    Decidable (MatchedEventualCanonicalPairInNewOldShell
      trajectory transitionStart physicalScale offset pair) := by
  unfold MatchedEventualCanonicalPairInNewOldShell
    MatchedEventualCanonicalIndexInNewShell
  infer_instance

private def newNewShellPairDecidable
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) (pair : Nat × Nat) :
    Decidable (MatchedEventualCanonicalPairInNewNewShell
      trajectory transitionStart physicalScale offset pair) := by
  unfold MatchedEventualCanonicalPairInNewNewShell
    MatchedEventualCanonicalIndexInNewShell
  infer_instance

local instance oldNewShellPairDecidableInstance
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) (pair : Nat × Nat) :
    Decidable (MatchedEventualCanonicalPairInOldNewShell
      trajectory transitionStart physicalScale offset pair) :=
  oldNewShellPairDecidable
    trajectory transitionStart physicalScale offset pair

local instance newOldShellPairDecidableInstance
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) (pair : Nat × Nat) :
    Decidable (MatchedEventualCanonicalPairInNewOldShell
      trajectory transitionStart physicalScale offset pair) :=
  newOldShellPairDecidable
    trajectory transitionStart physicalScale offset pair

local instance newNewShellPairDecidableInstance
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) (pair : Nat × Nat) :
    Decidable (MatchedEventualCanonicalPairInNewNewShell
      trajectory transitionStart physicalScale offset pair) :=
  newNewShellPairDecidable
    trajectory transitionStart physicalScale offset pair

/-! ## 1. Every literal new endpoint occupies one of the three faces -/

theorem matchedEventualCanonicalNewEndpointPair_face_cases
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
    MatchedEventualCanonicalPairInOldNewShell
        trajectory transitionStart physicalScale cutoffOffset endpointPair ∨
      MatchedEventualCanonicalPairInNewOldShell
          trajectory transitionStart physicalScale cutoffOffset endpointPair ∨
        MatchedEventualCanonicalPairInNewNewShell
          trajectory transitionStart physicalScale cutoffOffset endpointPair := by
  have hshell :=
    matchedEventualCanonicalNewEndpointPairs_mem_laterVacuumPairShell
      trajectory transitionStart physicalScale cutoffOffset endpointPair
      hendpointPair
  have hparts := List.mem_filter.mp hshell
  apply matchedEventualCanonicalNewShellPair_face_cases
    trajectory transitionStart physicalScale cutoffOffset endpointPair
  refine ⟨hparts.1, ?_⟩
  intro hold
  have hcoords :=
    (mem_matchedEventualCanonicalEmbeddedOldPairCarrier_iff
      trajectory transitionStart physicalScale cutoffOffset endpointPair).mp
      hold
  have holdB :
      matchedEventualCanonicalTransportedBridgeEndpointPairOldB
          trajectory transitionStart physicalScale cutoffOffset endpointPair =
        true := by
    unfold matchedEventualCanonicalTransportedBridgeEndpointPairOldB
    exact decide_eq_true hcoords
  have hnewB := hparts.2
  rw [holdB] at hnewB
  cases hnewB

private theorem not_newOld_of_oldNew
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale cutoffOffset : Nat}
    {endpointPair : Nat × Nat}
    (hface : MatchedEventualCanonicalPairInOldNewShell
      trajectory transitionStart physicalScale cutoffOffset endpointPair) :
    ¬ MatchedEventualCanonicalPairInNewOldShell
      trajectory transitionStart physicalScale cutoffOffset endpointPair := by
  intro hother
  exact hother.1.2 hface.1

private theorem not_newNew_of_oldNew
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale cutoffOffset : Nat}
    {endpointPair : Nat × Nat}
    (hface : MatchedEventualCanonicalPairInOldNewShell
      trajectory transitionStart physicalScale cutoffOffset endpointPair) :
    ¬ MatchedEventualCanonicalPairInNewNewShell
      trajectory transitionStart physicalScale cutoffOffset endpointPair := by
  intro hother
  exact hother.1.2 hface.1

private theorem not_oldNew_of_newOld
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale cutoffOffset : Nat}
    {endpointPair : Nat × Nat}
    (hface : MatchedEventualCanonicalPairInNewOldShell
      trajectory transitionStart physicalScale cutoffOffset endpointPair) :
    ¬ MatchedEventualCanonicalPairInOldNewShell
      trajectory transitionStart physicalScale cutoffOffset endpointPair := by
  intro hother
  exact hface.1.2 hother.1

private theorem not_newNew_of_newOld
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale cutoffOffset : Nat}
    {endpointPair : Nat × Nat}
    (hface : MatchedEventualCanonicalPairInNewOldShell
      trajectory transitionStart physicalScale cutoffOffset endpointPair) :
    ¬ MatchedEventualCanonicalPairInNewNewShell
      trajectory transitionStart physicalScale cutoffOffset endpointPair := by
  intro hother
  exact hother.2.2 hface.2

private theorem not_oldNew_of_newNew
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale cutoffOffset : Nat}
    {endpointPair : Nat × Nat}
    (hface : MatchedEventualCanonicalPairInNewNewShell
      trajectory transitionStart physicalScale cutoffOffset endpointPair) :
    ¬ MatchedEventualCanonicalPairInOldNewShell
      trajectory transitionStart physicalScale cutoffOffset endpointPair := by
  intro hother
  exact hface.1.2 hother.1

private theorem not_newOld_of_newNew
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale cutoffOffset : Nat}
    {endpointPair : Nat × Nat}
    (hface : MatchedEventualCanonicalPairInNewNewShell
      trajectory transitionStart physicalScale cutoffOffset endpointPair) :
    ¬ MatchedEventualCanonicalPairInNewOldShell
      trajectory transitionStart physicalScale cutoffOffset endpointPair := by
  intro hother
  exact hface.2.2 hother.2

/-! ## 2. Three indicators over one shared allowance -/

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceAllowance
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat)
    (allowance : Nat -> ((Nat × Nat) × (Nat × Nat)) -> Q')
    (cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) : Q' :=
  if MatchedEventualCanonicalPairInOldNewShell
      trajectory transitionStart physicalScale cutoffOffset cell.2 then
    allowance cutoffOffset cell
  else 0

def matchedEventualCanonicalNewEndpointTrafficNewOldFaceAllowance
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat)
    (allowance : Nat -> ((Nat × Nat) × (Nat × Nat)) -> Q')
    (cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) : Q' :=
  if MatchedEventualCanonicalPairInNewOldShell
      trajectory transitionStart physicalScale cutoffOffset cell.2 then
    allowance cutoffOffset cell
  else 0

def matchedEventualCanonicalNewEndpointTrafficNewNewFaceAllowance
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat)
    (allowance : Nat -> ((Nat × Nat) × (Nat × Nat)) -> Q')
    (cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) : Q' :=
  if MatchedEventualCanonicalPairInNewNewShell
      trajectory transitionStart physicalScale cutoffOffset cell.2 then
    allowance cutoffOffset cell
  else 0

theorem matchedEventualCanonicalNewEndpointTrafficAllowance_eqv_threeFaces
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat)
    (allowance : Nat -> ((Nat × Nat) × (Nat × Nat)) -> Q')
    (cutoffOffset : Nat)
    (pair endpointPair : Nat × Nat)
    (hendpointPair : endpointPair ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    allowance cutoffOffset (pair, endpointPair) ≈
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceAllowance
          trajectory transitionStart physicalScale allowance cutoffOffset
          (pair, endpointPair) +
        (matchedEventualCanonicalNewEndpointTrafficNewOldFaceAllowance
            trajectory transitionStart physicalScale allowance cutoffOffset
            (pair, endpointPair) +
          matchedEventualCanonicalNewEndpointTrafficNewNewFaceAllowance
            trajectory transitionStart physicalScale allowance cutoffOffset
            (pair, endpointPair)) := by
  rcases matchedEventualCanonicalNewEndpointPair_face_cases
      trajectory transitionStart physicalScale cutoffOffset endpointPair
      hendpointPair with hface | hface | hface
  · unfold matchedEventualCanonicalNewEndpointTrafficOldNewFaceAllowance
      matchedEventualCanonicalNewEndpointTrafficNewOldFaceAllowance
      matchedEventualCanonicalNewEndpointTrafficNewNewFaceAllowance
    rw [if_pos hface, if_neg (not_newOld_of_oldNew hface),
      if_neg (not_newNew_of_oldNew hface), Q'.zero_add', Q'.add_zero']
    exact Q'.eqv_refl _
  · unfold matchedEventualCanonicalNewEndpointTrafficOldNewFaceAllowance
      matchedEventualCanonicalNewEndpointTrafficNewOldFaceAllowance
      matchedEventualCanonicalNewEndpointTrafficNewNewFaceAllowance
    rw [if_neg (not_oldNew_of_newOld hface), if_pos hface,
      if_neg (not_newNew_of_newOld hface), Q'.add_zero', Q'.zero_add']
    exact Q'.eqv_refl _
  · unfold matchedEventualCanonicalNewEndpointTrafficOldNewFaceAllowance
      matchedEventualCanonicalNewEndpointTrafficNewOldFaceAllowance
      matchedEventualCanonicalNewEndpointTrafficNewNewFaceAllowance
    rw [if_neg (not_oldNew_of_newNew hface),
      if_neg (not_newOld_of_newNew hface), if_pos hface,
      Q'.zero_add', Q'.zero_add']
    exact Q'.eqv_refl _

/-! ## 3. Exact row decomposition -/

theorem matchedEventualCanonicalNewEndpointTrafficRowAllowance_eqv_threeFaces
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat)
    (allowance : Nat -> ((Nat × Nat) × (Nat × Nat)) -> Q')
    (cutoffOffset : Nat)
    (pair : Nat × Nat) :
    listQSum
        (fun endpointPair => allowance cutoffOffset (pair, endpointPair))
        (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
          trajectory transitionStart physicalScale cutoffOffset) ≈
      listQSum
          (fun endpointPair =>
            matchedEventualCanonicalNewEndpointTrafficOldNewFaceAllowance
              trajectory transitionStart physicalScale allowance cutoffOffset
              (pair, endpointPair))
          (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
            trajectory transitionStart physicalScale cutoffOffset) +
        (listQSum
            (fun endpointPair =>
              matchedEventualCanonicalNewEndpointTrafficNewOldFaceAllowance
                trajectory transitionStart physicalScale allowance cutoffOffset
                (pair, endpointPair))
            (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
              trajectory transitionStart physicalScale cutoffOffset) +
          listQSum
            (fun endpointPair =>
              matchedEventualCanonicalNewEndpointTrafficNewNewFaceAllowance
                trajectory transitionStart physicalScale allowance cutoffOffset
                (pair, endpointPair))
            (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
              trajectory transitionStart physicalScale cutoffOffset)) := by
  let items :=
    matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset
  let oldNew := fun endpointPair =>
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceAllowance
      trajectory transitionStart physicalScale allowance cutoffOffset
      (pair, endpointPair)
  let newOld := fun endpointPair =>
    matchedEventualCanonicalNewEndpointTrafficNewOldFaceAllowance
      trajectory transitionStart physicalScale allowance cutoffOffset
      (pair, endpointPair)
  let newNew := fun endpointPair =>
    matchedEventualCanonicalNewEndpointTrafficNewNewFaceAllowance
      trajectory transitionStart physicalScale allowance cutoffOffset
      (pair, endpointPair)
  refine Q'.eqv_trans _
      (listQSum (fun endpointPair =>
        oldNew endpointPair + (newOld endpointPair + newNew endpointPair))
        items) _ ?_ ?_
  · exact listQSum_congr_on _ _ items
      (fun endpointPair hendpointPair =>
        matchedEventualCanonicalNewEndpointTrafficAllowance_eqv_threeFaces
          trajectory transitionStart physicalScale allowance cutoffOffset
          pair endpointPair hendpointPair)
  · refine Q'.eqv_trans _
      (listQSum oldNew items +
        listQSum (fun endpointPair =>
          newOld endpointPair + newNew endpointPair) items) _
      (listQSum_add oldNew
        (fun endpointPair => newOld endpointPair + newNew endpointPair) items)
      ?_
    exact Q'.add_eqv_congr'
      (Q'.eqv_refl (listQSum oldNew items))
      (listQSum_add newOld newNew items)

/-! ## 4. Three parallel face budgets and their contraction -/

structure MatchedEventualCanonicalNewEndpointTrafficActiveCellThreeFacePaymentInverseSquareControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat) : Type 1 where
  offset : Nat
  offset_at_least_two : 2 <= offset
  oldNewCoefficient : Q'
  newOldCoefficient : Q'
  newNewCoefficient : Q'
  oldNewCoefficient_nonnegative : (0 : Q') <= oldNewCoefficient
  newOldCoefficient_nonnegative : (0 : Q') <= newOldCoefficient
  newNewCoefficient_nonnegative : (0 : Q') <= newNewCoefficient
  allowance : Nat -> ((Nat × Nat) × (Nat × Nat)) -> Q'
  allowance_nonnegative : forall cutoffOffset cell,
    (0 : Q') <= allowance cutoffOffset cell
  active_payment : forall cutoffOffset cell,
    cell ∈ matchedEventualCanonicalNewEndpointTrafficActiveCells
        trajectory transitionStart physicalScale cutoffOffset ->
    matchedEventualCanonicalNewEndpointTrafficActiveCellWeightedNumerator
        trajectory transitionStart physicalScale cutoffOffset cell <=
      allowance cutoffOffset cell *
        matchedEventualCanonicalNewEndpointTrafficCapacityOnCell
          trajectory transitionStart physicalScale cutoffOffset cell
  oldNew_row_allowance_le : forall cutoffOffset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale cutoffOffset ->
    listQSum
        (fun endpointPair =>
          matchedEventualCanonicalNewEndpointTrafficOldNewFaceAllowance
            trajectory transitionStart physicalScale allowance cutoffOffset
            (pair, endpointPair))
        (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
          trajectory transitionStart physicalScale cutoffOffset) <=
      oldNewCoefficient *
        invSqTerm offset offset_at_least_two cutoffOffset
  newOld_row_allowance_le : forall cutoffOffset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale cutoffOffset ->
    listQSum
        (fun endpointPair =>
          matchedEventualCanonicalNewEndpointTrafficNewOldFaceAllowance
            trajectory transitionStart physicalScale allowance cutoffOffset
            (pair, endpointPair))
        (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
          trajectory transitionStart physicalScale cutoffOffset) <=
      newOldCoefficient *
        invSqTerm offset offset_at_least_two cutoffOffset
  newNew_row_allowance_le : forall cutoffOffset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale cutoffOffset ->
    listQSum
        (fun endpointPair =>
          matchedEventualCanonicalNewEndpointTrafficNewNewFaceAllowance
            trajectory transitionStart physicalScale allowance cutoffOffset
            (pair, endpointPair))
        (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
          trajectory transitionStart physicalScale cutoffOffset) <=
      newNewCoefficient *
        invSqTerm offset offset_at_least_two cutoffOffset

def MatchedEventualCanonicalNewEndpointTrafficActiveCellThreeFacePaymentInverseSquareControl.coefficient
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficActiveCellThreeFacePaymentInverseSquareControl
        trajectory transitionStart physicalScale) : Q' :=
  control.oldNewCoefficient +
    (control.newOldCoefficient + control.newNewCoefficient)

theorem MatchedEventualCanonicalNewEndpointTrafficActiveCellThreeFacePaymentInverseSquareControl.coefficient_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficActiveCellThreeFacePaymentInverseSquareControl
        trajectory transitionStart physicalScale) :
    (0 : Q') <= control.coefficient := by
  have hsum := Q'.add_le_add
    control.oldNewCoefficient_nonnegative
    (Q'.add_le_add control.newOldCoefficient_nonnegative
      control.newNewCoefficient_nonnegative)
  rwa [Q'.zero_add', Q'.zero_add'] at hsum

theorem MatchedEventualCanonicalNewEndpointTrafficActiveCellThreeFacePaymentInverseSquareControl.row_allowance_le
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficActiveCellThreeFacePaymentInverseSquareControl
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset) :
    listQSum
        (fun endpointPair =>
          control.allowance cutoffOffset (pair, endpointPair))
        (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
          trajectory transitionStart physicalScale cutoffOffset) <=
      control.coefficient *
        invSqTerm control.offset control.offset_at_least_two cutoffOffset := by
  let term := invSqTerm control.offset control.offset_at_least_two cutoffOffset
  let oldNewSum := listQSum
    (fun endpointPair =>
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceAllowance
        trajectory transitionStart physicalScale control.allowance cutoffOffset
        (pair, endpointPair))
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)
  let newOldSum := listQSum
    (fun endpointPair =>
      matchedEventualCanonicalNewEndpointTrafficNewOldFaceAllowance
        trajectory transitionStart physicalScale control.allowance cutoffOffset
        (pair, endpointPair))
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)
  let newNewSum := listQSum
    (fun endpointPair =>
      matchedEventualCanonicalNewEndpointTrafficNewNewFaceAllowance
        trajectory transitionStart physicalScale control.allowance cutoffOffset
        (pair, endpointPair))
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)
  have hdecomposition :=
    matchedEventualCanonicalNewEndpointTrafficRowAllowance_eqv_threeFaces
      trajectory transitionStart physicalScale control.allowance cutoffOffset
      pair
  have hfaces : oldNewSum + (newOldSum + newNewSum) <=
      control.oldNewCoefficient * term +
        (control.newOldCoefficient * term +
          control.newNewCoefficient * term) :=
    Q'.add_le_add
      (control.oldNew_row_allowance_le cutoffOffset pair hpair)
      (Q'.add_le_add
        (control.newOld_row_allowance_le cutoffOffset pair hpair)
        (control.newNew_row_allowance_le cutoffOffset pair hpair))
  have hexpand : control.coefficient * term ≈
      control.oldNewCoefficient * term +
        (control.newOldCoefficient * term +
          control.newNewCoefficient * term) := by
    exact Q'.eqv_trans _
      (control.oldNewCoefficient * term +
        (control.newOldCoefficient + control.newNewCoefficient) * term) _
      (Q'.add_mul_eqv control.oldNewCoefficient
        (control.newOldCoefficient + control.newNewCoefficient) term)
      (Q'.add_eqv_congr'
        (Q'.eqv_refl (control.oldNewCoefficient * term))
        (Q'.add_mul_eqv control.newOldCoefficient
          control.newNewCoefficient term))
  exact Q'.le_trans' _ (oldNewSum + (newOldSum + newNewSum)) _
    (Q'.le_of_eqv hdecomposition)
    (Q'.le_trans' _ _ _ hfaces (Q'.ge_of_eqv hexpand))

def MatchedEventualCanonicalNewEndpointTrafficActiveCellThreeFacePaymentInverseSquareControl.toActiveCellPaymentControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficActiveCellThreeFacePaymentInverseSquareControl
        trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalNewEndpointTrafficActiveCellPaymentInverseSquareControl
      trajectory transitionStart physicalScale where
  offset := control.offset
  offset_at_least_two := control.offset_at_least_two
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  allowance := control.allowance
  allowance_nonnegative := control.allowance_nonnegative
  active_payment := control.active_payment
  row_allowance_le := control.row_allowance_le

theorem MatchedEventualCanonicalNewEndpointTrafficActiveCellThreeFacePaymentInverseSquareControl.debtMaximum_le
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficActiveCellThreeFacePaymentInverseSquareControl
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      control.coefficient *
        invSqTerm control.offset control.offset_at_least_two cutoffOffset :=
  control.toActiveCellPaymentControl.debtMaximum_le cutoffOffset

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFacePayment

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFacePayment.matchedEventualCanonicalNewEndpointPair_face_cases
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFacePayment.matchedEventualCanonicalNewEndpointTrafficAllowance_eqv_threeFaces
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFacePayment.matchedEventualCanonicalNewEndpointTrafficRowAllowance_eqv_threeFaces
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFacePayment.MatchedEventualCanonicalNewEndpointTrafficActiveCellThreeFacePaymentInverseSquareControl.coefficient_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFacePayment.MatchedEventualCanonicalNewEndpointTrafficActiveCellThreeFacePaymentInverseSquareControl.row_allowance_le
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFacePayment.MatchedEventualCanonicalNewEndpointTrafficActiveCellThreeFacePaymentInverseSquareControl.toActiveCellPaymentControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFacePayment.MatchedEventualCanonicalNewEndpointTrafficActiveCellThreeFacePaymentInverseSquareControl.debtMaximum_le
