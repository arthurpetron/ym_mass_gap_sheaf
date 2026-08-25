/-
# Denominator-free face capacity balances for matched new traffic

The canonical cell allowance is an exact stationary-weighted numerator divided
by the capacity of the mapped current cell.  Along one current-pair row that
capacity is common to every endpoint.  This module preserves each literal
old--new, new--old, and new--new endpoint face while moving the common positive
denominator outside the exact finite sum.

Each canonical face row is therefore the quotient of its exact face numerator
sum by the same mapped-cell capacity (and is zero when that capacity is not
positive).  A denominator-free estimate

  face numerator <= coefficient * inverse-square term * cell capacity

then compiles constructively to the corresponding canonical face-row control.
The three capacity-balance certificates are independent and rejoin through the
already checked canonical-payment compiler.

No capacity-balance estimate, continuum theory, or Clay conclusion is supplied.
No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or declaration
marked noncomputable is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellCanonicalPayment

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceCapacityBalance

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellCanonicalPayment
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFacePayment
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellPayment
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveFactorization
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficWeightedAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_divPos_eqv_divPos_listQSum_local
    {A : Type} (value : A -> Q') (denominator : Q')
    (hdenominator : (0 : Q') < denominator) :
    forall items : List A,
      listQSum
          (fun item => Q'.divPos (value item) denominator hdenominator)
          items ≈
        Q'.divPos (listQSum value items) denominator hdenominator
  | [] => by
      unfold Q'.divPos
      exact Q'.eqv_symm
        (Q'.zero_mul_eqv (Q'.recipPos denominator hdenominator))
  | first :: rest => by
      unfold listQSum
      refine Q'.eqv_trans _
        (Q'.divPos (value first) denominator hdenominator +
          Q'.divPos (listQSum value rest) denominator hdenominator) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (listQSum_divPos_eqv_divPos_listQSum_local
            value denominator hdenominator rest)
      unfold Q'.divPos
      exact Q'.eqv_symm
        (Q'.add_mul_eqv
          (value first) (listQSum value rest)
          (Q'.recipPos denominator hdenominator))

/-! ## 1. The exact numerator/denominator form of one canonical cell -/

theorem matchedEventualCanonicalNewEndpointTrafficCanonicalCellAllowance_eqv_dividedWeightedNumerator
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) :
    matchedEventualCanonicalNewEndpointTrafficCanonicalCellAllowance
        trajectory transitionStart physicalScale cutoffOffset cell ≈
      if hcapacity : (0 : Q') <
          matchedEventualCanonicalNewEndpointTrafficCapacityOnCell
            trajectory transitionStart physicalScale cutoffOffset cell then
        Q'.divPos
          (matchedEventualCanonicalNewEndpointTrafficActiveCellWeightedNumerator
            trajectory transitionStart physicalScale cutoffOffset cell)
          (matchedEventualCanonicalNewEndpointTrafficCapacityOnCell
            trajectory transitionStart physicalScale cutoffOffset cell)
          hcapacity
      else 0 := by
  let weight := matchedEventualCanonicalNewEndpointStationaryPairWeight
    trajectory transitionStart physicalScale cutoffOffset cell.2
  let floor := matchedEventualCanonicalSupportSharedFloor
    trajectory transitionStart physicalScale
  let route := matchedEventualCanonicalNewEndpointTrafficRouteFactorOnCell
    trajectory transitionStart physicalScale cutoffOffset cell
  let capacity := matchedEventualCanonicalNewEndpointTrafficCapacityOnCell
    trajectory transitionStart physicalScale cutoffOffset cell
  change weight *
      (if hcapacity : (0 : Q') < capacity then
        Q'.divPos (floor * route) capacity hcapacity
      else 0) ≈
    if hcapacity : (0 : Q') < capacity then
      Q'.divPos (weight * (floor * route)) capacity hcapacity
    else 0
  by_cases hcapacity : (0 : Q') < capacity
  · rw [dif_pos hcapacity, dif_pos hcapacity]
    unfold Q'.divPos
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv weight (floor * route)
        (Q'.recipPos capacity hcapacity))
  · rw [dif_neg hcapacity, dif_neg hcapacity]
    exact Q'.mul_zero_eqv weight

/-! ## 2. Face numerators on the unchanged literal cell -/

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceWeightedNumerator
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) : Q' :=
  matchedEventualCanonicalNewEndpointTrafficOldNewFaceAllowance
    trajectory transitionStart physicalScale
    (matchedEventualCanonicalNewEndpointTrafficActiveCellWeightedNumerator
      trajectory transitionStart physicalScale)
    cutoffOffset cell

def matchedEventualCanonicalNewEndpointTrafficNewOldFaceWeightedNumerator
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) : Q' :=
  matchedEventualCanonicalNewEndpointTrafficNewOldFaceAllowance
    trajectory transitionStart physicalScale
    (matchedEventualCanonicalNewEndpointTrafficActiveCellWeightedNumerator
      trajectory transitionStart physicalScale)
    cutoffOffset cell

def matchedEventualCanonicalNewEndpointTrafficNewNewFaceWeightedNumerator
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) : Q' :=
  matchedEventualCanonicalNewEndpointTrafficNewNewFaceAllowance
    trajectory transitionStart physicalScale
    (matchedEventualCanonicalNewEndpointTrafficActiveCellWeightedNumerator
      trajectory transitionStart physicalScale)
    cutoffOffset cell

private theorem maskedAllowance_eqv_dividedMaskedNumerator
    (face : Prop) [Decidable face]
    (allowance numerator capacity : Q')
    (hallowance : allowance ≈
      if hcapacity : (0 : Q') < capacity then
        Q'.divPos numerator capacity hcapacity
      else 0) :
    (if face then allowance else 0) ≈
      if hcapacity : (0 : Q') < capacity then
        Q'.divPos (if face then numerator else 0)
          capacity hcapacity
      else 0 := by
  by_cases hface : face
  · rw [if_pos hface, if_pos hface]
    exact hallowance
  · rw [if_neg hface, if_neg hface]
    by_cases hcapacity : (0 : Q') < capacity
    · rw [dif_pos hcapacity]
      unfold Q'.divPos
      exact Q'.eqv_symm
        (Q'.zero_mul_eqv (Q'.recipPos capacity hcapacity))
    · rw [dif_neg hcapacity]
      exact Q'.eqv_refl 0

private def oldNewShellPairDecidable
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) (pair : Nat × Nat) :
    Decidable
      (YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalPairInOldNewShell
        trajectory transitionStart physicalScale offset pair) := by
  unfold
    YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalPairInOldNewShell
    YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalIndexInNewShell
  infer_instance

private def newOldShellPairDecidable
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) (pair : Nat × Nat) :
    Decidable
      (YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalPairInNewOldShell
        trajectory transitionStart physicalScale offset pair) := by
  unfold
    YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalPairInNewOldShell
    YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalIndexInNewShell
  infer_instance

private def newNewShellPairDecidable
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) (pair : Nat × Nat) :
    Decidable
      (YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalPairInNewNewShell
        trajectory transitionStart physicalScale offset pair) := by
  unfold
    YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalPairInNewNewShell
    YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.MatchedEventualCanonicalIndexInNewShell
  infer_instance

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceAllowance_eqv_dividedWeightedNumerator
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceAllowance
        trajectory transitionStart physicalScale
        (matchedEventualCanonicalNewEndpointTrafficCanonicalCellAllowance
          trajectory transitionStart physicalScale)
        cutoffOffset cell ≈
      if hcapacity : (0 : Q') <
          matchedEventualCanonicalNewEndpointTrafficCapacityOnCell
            trajectory transitionStart physicalScale cutoffOffset cell then
        Q'.divPos
          (matchedEventualCanonicalNewEndpointTrafficOldNewFaceWeightedNumerator
            trajectory transitionStart physicalScale cutoffOffset cell)
          (matchedEventualCanonicalNewEndpointTrafficCapacityOnCell
            trajectory transitionStart physicalScale cutoffOffset cell)
          hcapacity
      else 0 := by
  letI := oldNewShellPairDecidable
    trajectory transitionStart physicalScale cutoffOffset cell.2
  unfold matchedEventualCanonicalNewEndpointTrafficOldNewFaceAllowance
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceWeightedNumerator
  exact maskedAllowance_eqv_dividedMaskedNumerator
    _ _ _ _
    (matchedEventualCanonicalNewEndpointTrafficCanonicalCellAllowance_eqv_dividedWeightedNumerator
      trajectory transitionStart physicalScale cutoffOffset cell)

theorem matchedEventualCanonicalNewEndpointTrafficNewOldFaceAllowance_eqv_dividedWeightedNumerator
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) :
    matchedEventualCanonicalNewEndpointTrafficNewOldFaceAllowance
        trajectory transitionStart physicalScale
        (matchedEventualCanonicalNewEndpointTrafficCanonicalCellAllowance
          trajectory transitionStart physicalScale)
        cutoffOffset cell ≈
      if hcapacity : (0 : Q') <
          matchedEventualCanonicalNewEndpointTrafficCapacityOnCell
            trajectory transitionStart physicalScale cutoffOffset cell then
        Q'.divPos
          (matchedEventualCanonicalNewEndpointTrafficNewOldFaceWeightedNumerator
            trajectory transitionStart physicalScale cutoffOffset cell)
          (matchedEventualCanonicalNewEndpointTrafficCapacityOnCell
            trajectory transitionStart physicalScale cutoffOffset cell)
          hcapacity
      else 0 := by
  letI := newOldShellPairDecidable
    trajectory transitionStart physicalScale cutoffOffset cell.2
  unfold matchedEventualCanonicalNewEndpointTrafficNewOldFaceAllowance
    matchedEventualCanonicalNewEndpointTrafficNewOldFaceWeightedNumerator
  exact maskedAllowance_eqv_dividedMaskedNumerator
    _ _ _ _
    (matchedEventualCanonicalNewEndpointTrafficCanonicalCellAllowance_eqv_dividedWeightedNumerator
      trajectory transitionStart physicalScale cutoffOffset cell)

theorem matchedEventualCanonicalNewEndpointTrafficNewNewFaceAllowance_eqv_dividedWeightedNumerator
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (cell : (Nat × Nat) × (Nat × Nat)) :
    matchedEventualCanonicalNewEndpointTrafficNewNewFaceAllowance
        trajectory transitionStart physicalScale
        (matchedEventualCanonicalNewEndpointTrafficCanonicalCellAllowance
          trajectory transitionStart physicalScale)
        cutoffOffset cell ≈
      if hcapacity : (0 : Q') <
          matchedEventualCanonicalNewEndpointTrafficCapacityOnCell
            trajectory transitionStart physicalScale cutoffOffset cell then
        Q'.divPos
          (matchedEventualCanonicalNewEndpointTrafficNewNewFaceWeightedNumerator
            trajectory transitionStart physicalScale cutoffOffset cell)
          (matchedEventualCanonicalNewEndpointTrafficCapacityOnCell
            trajectory transitionStart physicalScale cutoffOffset cell)
          hcapacity
      else 0 := by
  letI := newNewShellPairDecidable
    trajectory transitionStart physicalScale cutoffOffset cell.2
  unfold matchedEventualCanonicalNewEndpointTrafficNewNewFaceAllowance
    matchedEventualCanonicalNewEndpointTrafficNewNewFaceWeightedNumerator
  exact maskedAllowance_eqv_dividedMaskedNumerator
    _ _ _ _
    (matchedEventualCanonicalNewEndpointTrafficCanonicalCellAllowance_eqv_dividedWeightedNumerator
      trajectory transitionStart physicalScale cutoffOffset cell)

/-! ## 3. Exact finite face rows with one common denominator -/

/-- The common denominator of an endpoint row, named directly from the mapped
current pair rather than by choosing an irrelevant endpoint coordinate. -/
def matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) : Q' :=
  matchedEventualCanonicalTransportedBridgeSourceWeightedConditionalCapacityOnEdge
    trajectory transitionStart physicalScale cutoffOffset
    (matchedEventualCanonicalCurrentPairToNext
      trajectory transitionStart physicalScale cutoffOffset pair)

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceWeightedNumeratorRow
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) : Q' :=
  listQSum
    (fun endpointPair =>
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceWeightedNumerator
        trajectory transitionStart physicalScale cutoffOffset
        (pair, endpointPair))
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

def matchedEventualCanonicalNewEndpointTrafficNewOldFaceWeightedNumeratorRow
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) : Q' :=
  listQSum
    (fun endpointPair =>
      matchedEventualCanonicalNewEndpointTrafficNewOldFaceWeightedNumerator
        trajectory transitionStart physicalScale cutoffOffset
        (pair, endpointPair))
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

def matchedEventualCanonicalNewEndpointTrafficNewNewFaceWeightedNumeratorRow
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) : Q' :=
  listQSum
    (fun endpointPair =>
      matchedEventualCanonicalNewEndpointTrafficNewNewFaceWeightedNumerator
        trajectory transitionStart physicalScale cutoffOffset
        (pair, endpointPair))
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

private theorem listQSum_allowance_eqv_divided_numerator
    {A : Type} (allowance numerator : A -> Q')
    (capacity : Q') (items : List A)
    (hpoint : forall item,
      allowance item ≈
        if hcapacity : (0 : Q') < capacity then
          Q'.divPos (numerator item) capacity hcapacity
        else 0) :
    listQSum allowance items ≈
      if hcapacity : (0 : Q') < capacity then
        Q'.divPos (listQSum numerator items) capacity hcapacity
      else 0 := by
  by_cases hcapacity : (0 : Q') < capacity
  · rw [dif_pos hcapacity]
    refine Q'.eqv_trans _
      (listQSum
        (fun item => Q'.divPos (numerator item) capacity hcapacity)
        items) _ ?_ ?_
    · exact listQSum_congr_on _ _ items
        (fun item _ => by
          simpa only [dif_pos hcapacity] using hpoint item)
    · exact listQSum_divPos_eqv_divPos_listQSum_local
        numerator capacity hcapacity items
  · rw [dif_neg hcapacity]
    refine Q'.eqv_trans _ (listQSum (fun _ => (0 : Q')) items) _ ?_ ?_
    · exact listQSum_congr_on _ _ items
        (fun item _ => by
          simpa only [dif_neg hcapacity] using hpoint item)
    · exact listQSum_zero items

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceRowAllowance_eqv_dividedNumerator
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) :
    listQSum
        (fun endpointPair =>
          matchedEventualCanonicalNewEndpointTrafficOldNewFaceAllowance
            trajectory transitionStart physicalScale
            (matchedEventualCanonicalNewEndpointTrafficCanonicalCellAllowance
              trajectory transitionStart physicalScale)
            cutoffOffset (pair, endpointPair))
        (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
          trajectory transitionStart physicalScale cutoffOffset) ≈
      if hcapacity : (0 : Q') <
          matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
            trajectory transitionStart physicalScale cutoffOffset pair then
        Q'.divPos
          (matchedEventualCanonicalNewEndpointTrafficOldNewFaceWeightedNumeratorRow
            trajectory transitionStart physicalScale cutoffOffset pair)
          (matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
            trajectory transitionStart physicalScale cutoffOffset pair)
          hcapacity
      else 0 := by
  let capacity := matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
    trajectory transitionStart physicalScale cutoffOffset pair
  apply listQSum_allowance_eqv_divided_numerator _ _ capacity _
  intro endpointPair
  have hcapacityEq :
      matchedEventualCanonicalNewEndpointTrafficCapacityOnCell
          trajectory transitionStart physicalScale cutoffOffset
          (pair, endpointPair) = capacity := rfl
  simpa only [hcapacityEq] using
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceAllowance_eqv_dividedWeightedNumerator
      trajectory transitionStart physicalScale cutoffOffset
      (pair, endpointPair)

theorem matchedEventualCanonicalNewEndpointTrafficNewOldFaceRowAllowance_eqv_dividedNumerator
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) :
    listQSum
        (fun endpointPair =>
          matchedEventualCanonicalNewEndpointTrafficNewOldFaceAllowance
            trajectory transitionStart physicalScale
            (matchedEventualCanonicalNewEndpointTrafficCanonicalCellAllowance
              trajectory transitionStart physicalScale)
            cutoffOffset (pair, endpointPair))
        (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
          trajectory transitionStart physicalScale cutoffOffset) ≈
      if hcapacity : (0 : Q') <
          matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
            trajectory transitionStart physicalScale cutoffOffset pair then
        Q'.divPos
          (matchedEventualCanonicalNewEndpointTrafficNewOldFaceWeightedNumeratorRow
            trajectory transitionStart physicalScale cutoffOffset pair)
          (matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
            trajectory transitionStart physicalScale cutoffOffset pair)
          hcapacity
      else 0 := by
  let capacity := matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
    trajectory transitionStart physicalScale cutoffOffset pair
  apply listQSum_allowance_eqv_divided_numerator _ _ capacity _
  intro endpointPair
  have hcapacityEq :
      matchedEventualCanonicalNewEndpointTrafficCapacityOnCell
          trajectory transitionStart physicalScale cutoffOffset
          (pair, endpointPair) = capacity := rfl
  simpa only [hcapacityEq] using
    matchedEventualCanonicalNewEndpointTrafficNewOldFaceAllowance_eqv_dividedWeightedNumerator
      trajectory transitionStart physicalScale cutoffOffset
      (pair, endpointPair)

theorem matchedEventualCanonicalNewEndpointTrafficNewNewFaceRowAllowance_eqv_dividedNumerator
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) :
    listQSum
        (fun endpointPair =>
          matchedEventualCanonicalNewEndpointTrafficNewNewFaceAllowance
            trajectory transitionStart physicalScale
            (matchedEventualCanonicalNewEndpointTrafficCanonicalCellAllowance
              trajectory transitionStart physicalScale)
            cutoffOffset (pair, endpointPair))
        (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
          trajectory transitionStart physicalScale cutoffOffset) ≈
      if hcapacity : (0 : Q') <
          matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
            trajectory transitionStart physicalScale cutoffOffset pair then
        Q'.divPos
          (matchedEventualCanonicalNewEndpointTrafficNewNewFaceWeightedNumeratorRow
            trajectory transitionStart physicalScale cutoffOffset pair)
          (matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
            trajectory transitionStart physicalScale cutoffOffset pair)
          hcapacity
      else 0 := by
  let capacity := matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
    trajectory transitionStart physicalScale cutoffOffset pair
  apply listQSum_allowance_eqv_divided_numerator _ _ capacity _
  intro endpointPair
  have hcapacityEq :
      matchedEventualCanonicalNewEndpointTrafficCapacityOnCell
          trajectory transitionStart physicalScale cutoffOffset
          (pair, endpointPair) = capacity := rfl
  simpa only [hcapacityEq] using
    matchedEventualCanonicalNewEndpointTrafficNewNewFaceAllowance_eqv_dividedWeightedNumerator
      trajectory transitionStart physicalScale cutoffOffset
      (pair, endpointPair)

/-! ## 4. Three denominator-free inverse-square capacity balances -/

structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCapacityBalanceInverseSquareControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  numerator_le : forall cutoffOffset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale cutoffOffset ->
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceWeightedNumeratorRow
        trajectory transitionStart physicalScale cutoffOffset pair <=
      (coefficient *
          invSqTerm offset offset_at_least_two cutoffOffset) *
        matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair

structure MatchedEventualCanonicalNewEndpointTrafficNewOldFaceCapacityBalanceInverseSquareControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  numerator_le : forall cutoffOffset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale cutoffOffset ->
    matchedEventualCanonicalNewEndpointTrafficNewOldFaceWeightedNumeratorRow
        trajectory transitionStart physicalScale cutoffOffset pair <=
      (coefficient *
          invSqTerm offset offset_at_least_two cutoffOffset) *
        matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair

structure MatchedEventualCanonicalNewEndpointTrafficNewNewFaceCapacityBalanceInverseSquareControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  numerator_le : forall cutoffOffset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale cutoffOffset ->
    matchedEventualCanonicalNewEndpointTrafficNewNewFaceWeightedNumeratorRow
        trajectory transitionStart physicalScale cutoffOffset pair <=
      (coefficient *
          invSqTerm offset offset_at_least_two cutoffOffset) *
        matchedEventualCanonicalNewEndpointTrafficCapacityOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair

private theorem rowAllowance_le_of_eqv_dividedNumerator
    (row numerator capacity coefficient term : Q')
    (hrow : row ≈
      if hcapacity : (0 : Q') < capacity then
        Q'.divPos numerator capacity hcapacity
      else 0)
    (hcoefficient : (0 : Q') <= coefficient)
    (hterm : (0 : Q') <= term)
    (hnumerator : numerator <= (coefficient * term) * capacity) :
    row <= coefficient * term := by
  by_cases hcapacity : (0 : Q') < capacity
  · refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hrow) ?_
    rw [dif_pos hcapacity]
    exact Q'.divPos_le_of_le_mul numerator capacity hcapacity hnumerator
  · refine Q'.le_trans' _ (0 : Q') _ (Q'.le_of_eqv ?_) ?_
    · exact Q'.eqv_trans _ _ _ hrow (by
        rw [dif_neg hcapacity]
        exact Q'.eqv_refl 0)
    · exact Q'.mul_nonneg _ _ hcoefficient hterm

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCapacityBalanceInverseSquareControl.toCanonicalFaceControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCapacityBalanceInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficCanonicalOldNewFaceRowInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two where
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  row_allowance_le := by
    intro cutoffOffset pair hpair
    exact rowAllowance_le_of_eqv_dividedNumerator
      _ _ _ control.coefficient
      (invSqTerm offset offset_at_least_two cutoffOffset)
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceRowAllowance_eqv_dividedNumerator
        trajectory transitionStart physicalScale cutoffOffset pair)
      control.coefficient_nonnegative
      (invSqTerm_nonneg offset offset_at_least_two cutoffOffset)
      (control.numerator_le cutoffOffset pair hpair)

def MatchedEventualCanonicalNewEndpointTrafficNewOldFaceCapacityBalanceInverseSquareControl.toCanonicalFaceControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficNewOldFaceCapacityBalanceInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficCanonicalNewOldFaceRowInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two where
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  row_allowance_le := by
    intro cutoffOffset pair hpair
    exact rowAllowance_le_of_eqv_dividedNumerator
      _ _ _ control.coefficient
      (invSqTerm offset offset_at_least_two cutoffOffset)
      (matchedEventualCanonicalNewEndpointTrafficNewOldFaceRowAllowance_eqv_dividedNumerator
        trajectory transitionStart physicalScale cutoffOffset pair)
      control.coefficient_nonnegative
      (invSqTerm_nonneg offset offset_at_least_two cutoffOffset)
      (control.numerator_le cutoffOffset pair hpair)

def MatchedEventualCanonicalNewEndpointTrafficNewNewFaceCapacityBalanceInverseSquareControl.toCanonicalFaceControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (control :
      MatchedEventualCanonicalNewEndpointTrafficNewNewFaceCapacityBalanceInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficCanonicalNewNewFaceRowInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two where
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  row_allowance_le := by
    intro cutoffOffset pair hpair
    exact rowAllowance_le_of_eqv_dividedNumerator
      _ _ _ control.coefficient
      (invSqTerm offset offset_at_least_two cutoffOffset)
      (matchedEventualCanonicalNewEndpointTrafficNewNewFaceRowAllowance_eqv_dividedNumerator
        trajectory transitionStart physicalScale cutoffOffset pair)
      control.coefficient_nonnegative
      (invSqTerm_nonneg offset offset_at_least_two cutoffOffset)
      (control.numerator_le cutoffOffset pair hpair)

theorem matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_threeFaceCapacityBalances
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (oldNew :
      MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCapacityBalanceInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two)
    (newOld :
      MatchedEventualCanonicalNewEndpointTrafficNewOldFaceCapacityBalanceInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two)
    (newNew :
      MatchedEventualCanonicalNewEndpointTrafficNewNewFaceCapacityBalanceInverseSquareControl
        trajectory transitionStart physicalScale offset offset_at_least_two)
    (cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      (oldNew.coefficient +
          (newOld.coefficient + newNew.coefficient)) *
        invSqTerm offset offset_at_least_two cutoffOffset :=
  matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_canonicalThreeFaceControls
    oldNew.toCanonicalFaceControl newOld.toCanonicalFaceControl
      newNew.toCanonicalFaceControl cutoffOffset

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceCapacityBalance

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceCapacityBalance.matchedEventualCanonicalNewEndpointTrafficCanonicalCellAllowance_eqv_dividedWeightedNumerator
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceCapacityBalance.matchedEventualCanonicalNewEndpointTrafficOldNewFaceRowAllowance_eqv_dividedNumerator
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceCapacityBalance.matchedEventualCanonicalNewEndpointTrafficNewOldFaceRowAllowance_eqv_dividedNumerator
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceCapacityBalance.matchedEventualCanonicalNewEndpointTrafficNewNewFaceRowAllowance_eqv_dividedNumerator
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceCapacityBalance.MatchedEventualCanonicalNewEndpointTrafficOldNewFaceCapacityBalanceInverseSquareControl.toCanonicalFaceControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceCapacityBalance.MatchedEventualCanonicalNewEndpointTrafficNewOldFaceCapacityBalanceInverseSquareControl.toCanonicalFaceControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceCapacityBalance.MatchedEventualCanonicalNewEndpointTrafficNewNewFaceCapacityBalanceInverseSquareControl.toCanonicalFaceControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceCapacityBalance.matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_threeFaceCapacityBalances
