/-
# Exact matched finite-deficit compiler for correlated capacity debt

All four regional comparisons are over explicit finite carriers and explicit
rational same-edge debts.  This module computes their exact one-step deficit
maxima.  Those maxima automatically provide every pointwise inequality, so
the remaining regional analytic inputs are exactly four antitone tail-control
witnesses for four concrete scalar sequences.

The four tail witnesses may be proved in parallel but compile through the
same matched debt observable and the unchanged completed-family path.  No
tail witness, tail allowance, initial closure, continuum theory, or Clay
conclusion is supplied.  No `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellReturns

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtDeficitCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellReturns
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SummableCRealStepVariation
open YMGap.Continuum.SummableRationalStepVariationPrefixTailClosure

local infix:50 " ≈ " => Q'.eqv

private theorem le_add_of_abs_sub_le_local
    {left right bound : Q'}
    (hbound : Q'.abs (left + -right) <= bound) :
    left <= right + bound := by
  have hsub : left + -right <= bound :=
    Q'.le_trans' _ _ _ (Q'.le_abs_self (left + -right)) hbound
  have hadd : (left + -right) + right <= bound + right :=
    Q'.add_le_add_right (left + -right) bound right hsub
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_)
    (Q'.le_trans' _ _ _ hadd
      (Q'.le_of_eqv (Q'.add_comm_eqv bound right)))
  refine Q'.eqv_symm (Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv left (-right) right) ?_)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left left (-right + right) 0
      (Q'.neg_add_self_eqv right)) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' left)

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

/-! ## 1. Exact transported-old two-sided deficit -/

def matchedEventualCanonicalTransportedCapacityDebtDeficitOnPair
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) (pair : Nat × Nat) : Q' :=
  let current := matchedEventualCanonicalRoutedCapacityDebtOnPair
    trajectory transitionStart physicalScale offset pair
  let next := matchedEventualCanonicalRoutedCapacityDebtOnPair
    trajectory transitionStart physicalScale (offset + 1)
    (matchedEventualCanonicalCurrentPairToNext
      trajectory transitionStart physicalScale offset pair)
  Q'.max' (Q'.abs (current + -next)) (Q'.abs (next + -current))

def matchedEventualCanonicalTransportedCapacityDebtDeficitExactMaximum
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) : Q' :=
  listQMaxZero
    (matchedEventualCanonicalTransportedCapacityDebtDeficitOnPair
      trajectory transitionStart physicalScale offset)
    (matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale offset)

theorem matchedEventualCanonicalTransportedCapacityDebtDeficitExactMaximum_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) :
    (0 : Q') <= matchedEventualCanonicalTransportedCapacityDebtDeficitExactMaximum
      trajectory transitionStart physicalScale offset := by
  unfold matchedEventualCanonicalTransportedCapacityDebtDeficitExactMaximum
  apply listQMaxZero_nonnegative
  intro pair
  unfold matchedEventualCanonicalTransportedCapacityDebtDeficitOnPair
  dsimp only
  exact Q'.le_trans' _ _ _
    (Q'.abs_nonneg _)
    (Q'.le_max'_left _ _)

/-- Compact proof-bearing representative of the exact finite maximum. -/
structure MatchedEventualCanonicalTransportedCapacityDebtDeficitMaximumValue
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) : Type where
  value : Q'
  value_eqv : value ≈
    matchedEventualCanonicalTransportedCapacityDebtDeficitExactMaximum
      trajectory transitionStart physicalScale offset

opaque matchedEventualCanonicalTransportedCapacityDebtDeficitMaximumValueAt
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) :
    MatchedEventualCanonicalTransportedCapacityDebtDeficitMaximumValue
      trajectory transitionStart physicalScale offset := {
  value := matchedEventualCanonicalTransportedCapacityDebtDeficitExactMaximum
    trajectory transitionStart physicalScale offset
  value_eqv := Q'.eqv_refl _
}

def matchedEventualCanonicalTransportedCapacityDebtDeficitMaximum
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) : Q' :=
  (matchedEventualCanonicalTransportedCapacityDebtDeficitMaximumValueAt
    trajectory transitionStart physicalScale offset).value

theorem matchedEventualCanonicalTransportedCapacityDebtDeficitMaximum_eqv_exact
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) :
    matchedEventualCanonicalTransportedCapacityDebtDeficitMaximum
        trajectory transitionStart physicalScale offset ≈
      matchedEventualCanonicalTransportedCapacityDebtDeficitExactMaximum
        trajectory transitionStart physicalScale offset :=
  (matchedEventualCanonicalTransportedCapacityDebtDeficitMaximumValueAt
    trajectory transitionStart physicalScale offset).value_eqv

theorem matchedEventualCanonicalTransportedCapacityDebtDeficitMaximum_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) :
    (0 : Q') <= matchedEventualCanonicalTransportedCapacityDebtDeficitMaximum
      trajectory transitionStart physicalScale offset :=
  Q'.le_trans' _ _ _
    (matchedEventualCanonicalTransportedCapacityDebtDeficitExactMaximum_nonnegative
      trajectory transitionStart physicalScale offset)
    (Q'.le_of_eqv (Q'.eqv_symm
      (matchedEventualCanonicalTransportedCapacityDebtDeficitMaximum_eqv_exact
        trajectory transitionStart physicalScale offset)))

theorem matchedEventualCanonicalTransportedCapacityDebtDeficitOnPair_le_maximum
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale offset) :
    matchedEventualCanonicalTransportedCapacityDebtDeficitOnPair
        trajectory transitionStart physicalScale offset pair <=
      matchedEventualCanonicalTransportedCapacityDebtDeficitMaximum
        trajectory transitionStart physicalScale offset := by
  have hexact :
      matchedEventualCanonicalTransportedCapacityDebtDeficitOnPair
          trajectory transitionStart physicalScale offset pair <=
        matchedEventualCanonicalTransportedCapacityDebtDeficitExactMaximum
          trajectory transitionStart physicalScale offset := by
    unfold matchedEventualCanonicalTransportedCapacityDebtDeficitExactMaximum
    exact le_listQMaxZero_of_mem _ _ hpair
  exact Q'.le_trans' _ _ _ hexact
    (Q'.le_of_eqv (Q'.eqv_symm
      (matchedEventualCanonicalTransportedCapacityDebtDeficitMaximum_eqv_exact
        trajectory transitionStart physicalScale offset)))

structure MatchedEventualCanonicalTransportedCapacityDebtDeficitTail
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat) : Type 1 where
  tailControl : AntitoneTailControl
    (matchedEventualCanonicalTransportedCapacityDebtDeficitMaximum
      trajectory transitionStart physicalScale)

def MatchedEventualCanonicalTransportedCapacityDebtDeficitTail.toEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (data : MatchedEventualCanonicalTransportedCapacityDebtDeficitTail
      trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalTransportedCapacityDebtEnvelope
      trajectory transitionStart physicalScale where
  variation := matchedEventualCanonicalTransportedCapacityDebtDeficitMaximum
    trajectory transitionStart physicalScale
  variation_nonnegative :=
    matchedEventualCanonicalTransportedCapacityDebtDeficitMaximum_nonnegative
      trajectory transitionStart physicalScale
  tailControl := data.tailControl
  current_le_next := by
    intro offset pair hpair
    apply le_add_of_abs_sub_le_local
    exact Q'.le_trans' _ _ _
      (Q'.le_max'_left _ _)
      (matchedEventualCanonicalTransportedCapacityDebtDeficitOnPair_le_maximum
        trajectory transitionStart physicalScale offset pair hpair)
  next_le_current := by
    intro offset pair hpair
    apply le_add_of_abs_sub_le_local
    exact Q'.le_trans' _ _ _
      (Q'.le_max'_right _ _)
      (matchedEventualCanonicalTransportedCapacityDebtDeficitOnPair_le_maximum
        trajectory transitionStart physicalScale offset pair hpair)

/-! ## 2. Exact return-face deficits -/

def matchedEventualCanonicalOldNewReturnCapacityDebtDeficitOnPair
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) (pair : Nat × Nat) : Q' :=
  if MatchedEventualCanonicalPairInOldNewShell
      trajectory transitionStart physicalScale offset pair then
    Q'.abs
      (matchedEventualCanonicalRoutedCapacityDebtOnPair
          trajectory transitionStart physicalScale (offset + 1) pair +
        -matchedEventualCanonicalRoutedCapacityDebtOnPair
          trajectory transitionStart physicalScale offset
          (matchedEventualCanonicalOldNewReturnPair
            trajectory transitionStart physicalScale offset pair))
  else 0

def matchedEventualCanonicalNewOldReturnCapacityDebtDeficitOnPair
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) (pair : Nat × Nat) : Q' :=
  if MatchedEventualCanonicalPairInNewOldShell
      trajectory transitionStart physicalScale offset pair then
    Q'.abs
      (matchedEventualCanonicalRoutedCapacityDebtOnPair
          trajectory transitionStart physicalScale (offset + 1) pair +
        -matchedEventualCanonicalRoutedCapacityDebtOnPair
          trajectory transitionStart physicalScale offset
          (matchedEventualCanonicalNewOldReturnPair
            trajectory transitionStart physicalScale offset pair))
  else 0

def matchedEventualCanonicalNewNewReturnCapacityDebtDeficitOnPair
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) (pair : Nat × Nat) : Q' :=
  if MatchedEventualCanonicalPairInNewNewShell
      trajectory transitionStart physicalScale offset pair then
    Q'.abs
      (matchedEventualCanonicalRoutedCapacityDebtOnPair
          trajectory transitionStart physicalScale (offset + 1) pair +
        -matchedEventualCanonicalRoutedCapacityDebtOnPair
          trajectory transitionStart physicalScale offset
          (matchedEventualCanonicalNewNewReturnPair
            trajectory transitionStart physicalScale offset pair))
  else 0

def matchedEventualCanonicalOldNewReturnCapacityDebtDeficitExactMaximum
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) : Q' :=
  listQMaxZero
    (matchedEventualCanonicalOldNewReturnCapacityDebtDeficitOnPair
      trajectory transitionStart physicalScale offset)
    (matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (offset + 1))

def matchedEventualCanonicalNewOldReturnCapacityDebtDeficitExactMaximum
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) : Q' :=
  listQMaxZero
    (matchedEventualCanonicalNewOldReturnCapacityDebtDeficitOnPair
      trajectory transitionStart physicalScale offset)
    (matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (offset + 1))

def matchedEventualCanonicalNewNewReturnCapacityDebtDeficitExactMaximum
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) : Q' :=
  listQMaxZero
    (matchedEventualCanonicalNewNewReturnCapacityDebtDeficitOnPair
      trajectory transitionStart physicalScale offset)
    (matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (offset + 1))

structure MatchedEventualCanonicalOldNewReturnCapacityDebtDeficitMaximumValue
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) : Type where
  value : Q'
  value_eqv : value ≈
    matchedEventualCanonicalOldNewReturnCapacityDebtDeficitExactMaximum
      trajectory transitionStart physicalScale offset

opaque matchedEventualCanonicalOldNewReturnCapacityDebtDeficitMaximumValueAt
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) :
    MatchedEventualCanonicalOldNewReturnCapacityDebtDeficitMaximumValue
      trajectory transitionStart physicalScale offset := {
  value := matchedEventualCanonicalOldNewReturnCapacityDebtDeficitExactMaximum
    trajectory transitionStart physicalScale offset
  value_eqv := Q'.eqv_refl _
}

def matchedEventualCanonicalOldNewReturnCapacityDebtDeficitMaximum
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) : Q' :=
  (matchedEventualCanonicalOldNewReturnCapacityDebtDeficitMaximumValueAt
    trajectory transitionStart physicalScale offset).value

theorem matchedEventualCanonicalOldNewReturnCapacityDebtDeficitMaximum_eqv_exact
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) :
    matchedEventualCanonicalOldNewReturnCapacityDebtDeficitMaximum
        trajectory transitionStart physicalScale offset ≈
      matchedEventualCanonicalOldNewReturnCapacityDebtDeficitExactMaximum
        trajectory transitionStart physicalScale offset :=
  (matchedEventualCanonicalOldNewReturnCapacityDebtDeficitMaximumValueAt
    trajectory transitionStart physicalScale offset).value_eqv

structure MatchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximumValue
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) : Type where
  value : Q'
  value_eqv : value ≈
    matchedEventualCanonicalNewOldReturnCapacityDebtDeficitExactMaximum
      trajectory transitionStart physicalScale offset

opaque matchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximumValueAt
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) :
    MatchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximumValue
      trajectory transitionStart physicalScale offset := {
  value := matchedEventualCanonicalNewOldReturnCapacityDebtDeficitExactMaximum
    trajectory transitionStart physicalScale offset
  value_eqv := Q'.eqv_refl _
}

def matchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximum
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) : Q' :=
  (matchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximumValueAt
    trajectory transitionStart physicalScale offset).value

theorem matchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximum_eqv_exact
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) :
    matchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximum
        trajectory transitionStart physicalScale offset ≈
      matchedEventualCanonicalNewOldReturnCapacityDebtDeficitExactMaximum
        trajectory transitionStart physicalScale offset :=
  (matchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximumValueAt
    trajectory transitionStart physicalScale offset).value_eqv

structure MatchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximumValue
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) : Type where
  value : Q'
  value_eqv : value ≈
    matchedEventualCanonicalNewNewReturnCapacityDebtDeficitExactMaximum
      trajectory transitionStart physicalScale offset

opaque matchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximumValueAt
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) :
    MatchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximumValue
      trajectory transitionStart physicalScale offset := {
  value := matchedEventualCanonicalNewNewReturnCapacityDebtDeficitExactMaximum
    trajectory transitionStart physicalScale offset
  value_eqv := Q'.eqv_refl _
}

def matchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximum
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) : Q' :=
  (matchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximumValueAt
    trajectory transitionStart physicalScale offset).value

theorem matchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximum_eqv_exact
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) :
    matchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximum
        trajectory transitionStart physicalScale offset ≈
      matchedEventualCanonicalNewNewReturnCapacityDebtDeficitExactMaximum
        trajectory transitionStart physicalScale offset :=
  (matchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximumValueAt
    trajectory transitionStart physicalScale offset).value_eqv

private theorem oldNewShellPair_mem_next
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) (pair : Nat × Nat)
    (hpair : MatchedEventualCanonicalPairInOldNewShell
      trajectory transitionStart physicalScale offset pair) :
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (offset + 1) := by
  exact hpair.2.1 |> fun htarget =>
    (mem_cartesian_iff _ _ pair).mpr
      ⟨matchedEventualCanonicalEmbeddedOldIndexCarrier_mem_next
          trajectory transitionStart physicalScale offset pair.1 hpair.1,
        htarget⟩

private theorem newOldShellPair_mem_next
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) (pair : Nat × Nat)
    (hpair : MatchedEventualCanonicalPairInNewOldShell
      trajectory transitionStart physicalScale offset pair) :
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (offset + 1) := by
  exact (mem_cartesian_iff _ _ pair).mpr
    ⟨hpair.1.1,
      matchedEventualCanonicalEmbeddedOldIndexCarrier_mem_next
        trajectory transitionStart physicalScale offset pair.2 hpair.2⟩

private theorem newNewShellPair_mem_next
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) (pair : Nat × Nat)
    (hpair : MatchedEventualCanonicalPairInNewNewShell
      trajectory transitionStart physicalScale offset pair) :
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (offset + 1) := by
  exact (mem_cartesian_iff _ _ pair).mpr ⟨hpair.1.1, hpair.2.1⟩

theorem matchedEventualCanonicalOldNewReturnCapacityDebtDeficitExactMaximum_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) :
    (0 : Q') <= matchedEventualCanonicalOldNewReturnCapacityDebtDeficitExactMaximum
      trajectory transitionStart physicalScale offset := by
  unfold matchedEventualCanonicalOldNewReturnCapacityDebtDeficitExactMaximum
  apply listQMaxZero_nonnegative
  intro pair
  unfold matchedEventualCanonicalOldNewReturnCapacityDebtDeficitOnPair
  by_cases hpair : MatchedEventualCanonicalPairInOldNewShell
      trajectory transitionStart physicalScale offset pair
  · rw [if_pos hpair]
    exact Q'.abs_nonneg _
  · rw [if_neg hpair]
    exact Q'.le_refl' 0

theorem matchedEventualCanonicalNewOldReturnCapacityDebtDeficitExactMaximum_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) :
    (0 : Q') <= matchedEventualCanonicalNewOldReturnCapacityDebtDeficitExactMaximum
      trajectory transitionStart physicalScale offset := by
  unfold matchedEventualCanonicalNewOldReturnCapacityDebtDeficitExactMaximum
  apply listQMaxZero_nonnegative
  intro pair
  unfold matchedEventualCanonicalNewOldReturnCapacityDebtDeficitOnPair
  by_cases hpair : MatchedEventualCanonicalPairInNewOldShell
      trajectory transitionStart physicalScale offset pair
  · rw [if_pos hpair]
    exact Q'.abs_nonneg _
  · rw [if_neg hpair]
    exact Q'.le_refl' 0

theorem matchedEventualCanonicalNewNewReturnCapacityDebtDeficitExactMaximum_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) :
    (0 : Q') <= matchedEventualCanonicalNewNewReturnCapacityDebtDeficitExactMaximum
      trajectory transitionStart physicalScale offset := by
  unfold matchedEventualCanonicalNewNewReturnCapacityDebtDeficitExactMaximum
  apply listQMaxZero_nonnegative
  intro pair
  unfold matchedEventualCanonicalNewNewReturnCapacityDebtDeficitOnPair
  by_cases hpair : MatchedEventualCanonicalPairInNewNewShell
      trajectory transitionStart physicalScale offset pair
  · rw [if_pos hpair]
    exact Q'.abs_nonneg _
  · rw [if_neg hpair]
    exact Q'.le_refl' 0

theorem matchedEventualCanonicalOldNewReturnCapacityDebtDeficitMaximum_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) :
    (0 : Q') <= matchedEventualCanonicalOldNewReturnCapacityDebtDeficitMaximum
      trajectory transitionStart physicalScale offset :=
  Q'.le_trans' _ _ _
    (matchedEventualCanonicalOldNewReturnCapacityDebtDeficitExactMaximum_nonnegative
      trajectory transitionStart physicalScale offset)
    (Q'.le_of_eqv (Q'.eqv_symm
      (matchedEventualCanonicalOldNewReturnCapacityDebtDeficitMaximum_eqv_exact
        trajectory transitionStart physicalScale offset)))

theorem matchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximum_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) :
    (0 : Q') <= matchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximum
      trajectory transitionStart physicalScale offset :=
  Q'.le_trans' _ _ _
    (matchedEventualCanonicalNewOldReturnCapacityDebtDeficitExactMaximum_nonnegative
      trajectory transitionStart physicalScale offset)
    (Q'.le_of_eqv (Q'.eqv_symm
      (matchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximum_eqv_exact
        trajectory transitionStart physicalScale offset)))

theorem matchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximum_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) :
    (0 : Q') <= matchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximum
      trajectory transitionStart physicalScale offset :=
  Q'.le_trans' _ _ _
    (matchedEventualCanonicalNewNewReturnCapacityDebtDeficitExactMaximum_nonnegative
      trajectory transitionStart physicalScale offset)
    (Q'.le_of_eqv (Q'.eqv_symm
      (matchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximum_eqv_exact
        trajectory transitionStart physicalScale offset)))

theorem matchedEventualCanonicalOldNewReturnCapacityDebtDeficitOnPair_le_maximum
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) (pair : Nat × Nat)
    (hpair : MatchedEventualCanonicalPairInOldNewShell
      trajectory transitionStart physicalScale offset pair) :
    Q'.abs
        (matchedEventualCanonicalRoutedCapacityDebtOnPair
            trajectory transitionStart physicalScale (offset + 1) pair +
          -matchedEventualCanonicalRoutedCapacityDebtOnPair
            trajectory transitionStart physicalScale offset
            (matchedEventualCanonicalOldNewReturnPair
              trajectory transitionStart physicalScale offset pair)) <=
      matchedEventualCanonicalOldNewReturnCapacityDebtDeficitMaximum
        trajectory transitionStart physicalScale offset := by
  have hexact : Q'.abs
        (matchedEventualCanonicalRoutedCapacityDebtOnPair
            trajectory transitionStart physicalScale (offset + 1) pair +
          -matchedEventualCanonicalRoutedCapacityDebtOnPair
            trajectory transitionStart physicalScale offset
            (matchedEventualCanonicalOldNewReturnPair
              trajectory transitionStart physicalScale offset pair)) <=
      matchedEventualCanonicalOldNewReturnCapacityDebtDeficitExactMaximum
        trajectory transitionStart physicalScale offset := by
    unfold matchedEventualCanonicalOldNewReturnCapacityDebtDeficitExactMaximum
    have hmax := le_listQMaxZero_of_mem
      (matchedEventualCanonicalOldNewReturnCapacityDebtDeficitOnPair
        trajectory transitionStart physicalScale offset)
      (matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale (offset + 1))
      (oldNewShellPair_mem_next
        trajectory transitionStart physicalScale offset pair hpair)
    unfold matchedEventualCanonicalOldNewReturnCapacityDebtDeficitOnPair at hmax
    rw [if_pos hpair] at hmax
    exact hmax
  exact Q'.le_trans' _ _ _ hexact
    (Q'.le_of_eqv (Q'.eqv_symm
      (matchedEventualCanonicalOldNewReturnCapacityDebtDeficitMaximum_eqv_exact
        trajectory transitionStart physicalScale offset)))

theorem matchedEventualCanonicalNewOldReturnCapacityDebtDeficitOnPair_le_maximum
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) (pair : Nat × Nat)
    (hpair : MatchedEventualCanonicalPairInNewOldShell
      trajectory transitionStart physicalScale offset pair) :
    Q'.abs
        (matchedEventualCanonicalRoutedCapacityDebtOnPair
            trajectory transitionStart physicalScale (offset + 1) pair +
          -matchedEventualCanonicalRoutedCapacityDebtOnPair
            trajectory transitionStart physicalScale offset
            (matchedEventualCanonicalNewOldReturnPair
              trajectory transitionStart physicalScale offset pair)) <=
      matchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximum
        trajectory transitionStart physicalScale offset := by
  have hexact : Q'.abs
        (matchedEventualCanonicalRoutedCapacityDebtOnPair
            trajectory transitionStart physicalScale (offset + 1) pair +
          -matchedEventualCanonicalRoutedCapacityDebtOnPair
            trajectory transitionStart physicalScale offset
            (matchedEventualCanonicalNewOldReturnPair
              trajectory transitionStart physicalScale offset pair)) <=
      matchedEventualCanonicalNewOldReturnCapacityDebtDeficitExactMaximum
        trajectory transitionStart physicalScale offset := by
    unfold matchedEventualCanonicalNewOldReturnCapacityDebtDeficitExactMaximum
    have hmax := le_listQMaxZero_of_mem
      (matchedEventualCanonicalNewOldReturnCapacityDebtDeficitOnPair
        trajectory transitionStart physicalScale offset)
      (matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale (offset + 1))
      (newOldShellPair_mem_next
        trajectory transitionStart physicalScale offset pair hpair)
    unfold matchedEventualCanonicalNewOldReturnCapacityDebtDeficitOnPair at hmax
    rw [if_pos hpair] at hmax
    exact hmax
  exact Q'.le_trans' _ _ _ hexact
    (Q'.le_of_eqv (Q'.eqv_symm
      (matchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximum_eqv_exact
        trajectory transitionStart physicalScale offset)))

theorem matchedEventualCanonicalNewNewReturnCapacityDebtDeficitOnPair_le_maximum
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) (pair : Nat × Nat)
    (hpair : MatchedEventualCanonicalPairInNewNewShell
      trajectory transitionStart physicalScale offset pair) :
    Q'.abs
        (matchedEventualCanonicalRoutedCapacityDebtOnPair
            trajectory transitionStart physicalScale (offset + 1) pair +
          -matchedEventualCanonicalRoutedCapacityDebtOnPair
            trajectory transitionStart physicalScale offset
            (matchedEventualCanonicalNewNewReturnPair
              trajectory transitionStart physicalScale offset pair)) <=
      matchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximum
        trajectory transitionStart physicalScale offset := by
  have hexact : Q'.abs
        (matchedEventualCanonicalRoutedCapacityDebtOnPair
            trajectory transitionStart physicalScale (offset + 1) pair +
          -matchedEventualCanonicalRoutedCapacityDebtOnPair
            trajectory transitionStart physicalScale offset
            (matchedEventualCanonicalNewNewReturnPair
              trajectory transitionStart physicalScale offset pair)) <=
      matchedEventualCanonicalNewNewReturnCapacityDebtDeficitExactMaximum
        trajectory transitionStart physicalScale offset := by
    unfold matchedEventualCanonicalNewNewReturnCapacityDebtDeficitExactMaximum
    have hmax := le_listQMaxZero_of_mem
      (matchedEventualCanonicalNewNewReturnCapacityDebtDeficitOnPair
        trajectory transitionStart physicalScale offset)
      (matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale (offset + 1))
      (newNewShellPair_mem_next
        trajectory transitionStart physicalScale offset pair hpair)
    unfold matchedEventualCanonicalNewNewReturnCapacityDebtDeficitOnPair at hmax
    rw [if_pos hpair] at hmax
    exact hmax
  exact Q'.le_trans' _ _ _ hexact
    (Q'.le_of_eqv (Q'.eqv_symm
      (matchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximum_eqv_exact
        trajectory transitionStart physicalScale offset)))

/-! ## 3. Four exact scalar tail controls reconstruct all envelopes -/

structure MatchedEventualCanonicalOldNewCapacityDebtDeficitTail
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat) : Type 1 where
  tailControl : AntitoneTailControl
    (matchedEventualCanonicalOldNewReturnCapacityDebtDeficitMaximum
      trajectory transitionStart physicalScale)

structure MatchedEventualCanonicalNewOldCapacityDebtDeficitTail
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat) : Type 1 where
  tailControl : AntitoneTailControl
    (matchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximum
      trajectory transitionStart physicalScale)

structure MatchedEventualCanonicalNewNewCapacityDebtDeficitTail
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat) : Type 1 where
  tailControl : AntitoneTailControl
    (matchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximum
      trajectory transitionStart physicalScale)

def MatchedEventualCanonicalOldNewCapacityDebtDeficitTail.toReturnEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (data : MatchedEventualCanonicalOldNewCapacityDebtDeficitTail
      trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalOldNewReturnCapacityDebtEnvelope
      trajectory transitionStart physicalScale where
  variation := matchedEventualCanonicalOldNewReturnCapacityDebtDeficitMaximum
    trajectory transitionStart physicalScale
  variation_nonnegative :=
    matchedEventualCanonicalOldNewReturnCapacityDebtDeficitMaximum_nonnegative
      trajectory transitionStart physicalScale
  tailControl := data.tailControl
  next_le_return := by
    intro offset pair hpair
    exact le_add_of_abs_sub_le_local
      (matchedEventualCanonicalOldNewReturnCapacityDebtDeficitOnPair_le_maximum
        trajectory transitionStart physicalScale offset pair hpair)

def MatchedEventualCanonicalNewOldCapacityDebtDeficitTail.toReturnEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (data : MatchedEventualCanonicalNewOldCapacityDebtDeficitTail
      trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalNewOldReturnCapacityDebtEnvelope
      trajectory transitionStart physicalScale where
  variation := matchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximum
    trajectory transitionStart physicalScale
  variation_nonnegative :=
    matchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximum_nonnegative
      trajectory transitionStart physicalScale
  tailControl := data.tailControl
  next_le_return := by
    intro offset pair hpair
    exact le_add_of_abs_sub_le_local
      (matchedEventualCanonicalNewOldReturnCapacityDebtDeficitOnPair_le_maximum
        trajectory transitionStart physicalScale offset pair hpair)

def MatchedEventualCanonicalNewNewCapacityDebtDeficitTail.toReturnEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (data : MatchedEventualCanonicalNewNewCapacityDebtDeficitTail
      trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalNewNewReturnCapacityDebtEnvelope
      trajectory transitionStart physicalScale where
  variation := matchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximum
    trajectory transitionStart physicalScale
  variation_nonnegative :=
    matchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximum_nonnegative
      trajectory transitionStart physicalScale
  tailControl := data.tailControl
  next_le_return := by
    intro offset pair hpair
    exact le_add_of_abs_sub_le_local
      (matchedEventualCanonicalNewNewReturnCapacityDebtDeficitOnPair_le_maximum
        trajectory transitionStart physicalScale offset pair hpair)

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtDeficitCompiler

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtDeficitCompiler.matchedEventualCanonicalTransportedCapacityDebtDeficitMaximum_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtDeficitCompiler.MatchedEventualCanonicalTransportedCapacityDebtDeficitTail.toEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtDeficitCompiler.matchedEventualCanonicalOldNewReturnCapacityDebtDeficitOnPair_le_maximum
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtDeficitCompiler.matchedEventualCanonicalNewOldReturnCapacityDebtDeficitOnPair_le_maximum
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtDeficitCompiler.matchedEventualCanonicalNewNewReturnCapacityDebtDeficitOnPair_le_maximum
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtDeficitCompiler.MatchedEventualCanonicalOldNewCapacityDebtDeficitTail.toReturnEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtDeficitCompiler.MatchedEventualCanonicalNewOldCapacityDebtDeficitTail.toReturnEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtDeficitCompiler.MatchedEventualCanonicalNewNewCapacityDebtDeficitTail.toReturnEnvelope
