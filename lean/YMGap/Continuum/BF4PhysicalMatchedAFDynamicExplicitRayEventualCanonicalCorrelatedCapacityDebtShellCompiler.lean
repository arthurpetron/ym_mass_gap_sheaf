/-
# Matched old-component and new-shell correlated debt compiler

The one-envelope correlated route still compares two changing finite pair
carriers.  This module separates that comparison into the embedded image of
the current carrier and the genuinely new complement at the next cutoff.

The embedded-old and new-shell estimates carry independent summable budgets.
Their constructive sum recreates the exact correlated envelope on the same
matched nome, canonical routing, routed load, conditional kernel, and ray
floor.  A scale-indexed family of the two estimates therefore contracts to
the already checked matched completed family.

No transported estimate, shell estimate, tail allowance, or initial closure
is inhabited here.  No strength band, observable pin, continuum Yang--Mills
theory, or Clay conclusion is asserted.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler
import YMGap.Continuum.SummableRationalStepVariationAlgebra

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.SummableCRealStepVariation
open YMGap.Continuum.SummableRationalStepVariationAlgebra
open YMGap.Continuum.SummableRationalStepVariationPrefixTailClosure

/-! ## 1. Exact embedded-old and new-shell regions -/

/-- Literal image of the current matched pair carrier in the next cutoff. -/
def matchedEventualCanonicalEmbeddedOldPairCarrier
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat) : List (Nat × Nat) :=
  (matchedEventualCanonicalVacuumSectorPairs
    trajectory transitionStart physicalScale offset).map
      (matchedEventualCanonicalCurrentPairToNext
        trajectory transitionStart physicalScale offset)

theorem matchedEventualCanonicalCurrentPairToNext_mem_embeddedOld
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale offset) :
    matchedEventualCanonicalCurrentPairToNext
        trajectory transitionStart physicalScale offset pair ∈
      matchedEventualCanonicalEmbeddedOldPairCarrier
        trajectory transitionStart physicalScale offset := by
  exact List.mem_map.mpr ⟨pair, hpair, rfl⟩

theorem matchedEventualCanonicalEmbeddedOldPairCarrier_mem_next
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalEmbeddedOldPairCarrier
      trajectory transitionStart physicalScale offset) :
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (offset + 1) := by
  obtain ⟨currentPair, hcurrentPair, hmap⟩ := List.mem_map.mp hpair
  rw [← hmap]
  exact matchedEventualCanonicalCurrentPairToNext_mem
    trajectory transitionStart physicalScale offset currentPair hcurrentPair

/-- On the embedded-old region the forward map after constructive reverse
search returns the literal later pair. -/
theorem matchedEventualCanonicalCurrentPairToNext_nextToCurrent_of_mem_embeddedOld
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalEmbeddedOldPairCarrier
      trajectory transitionStart physicalScale offset) :
    matchedEventualCanonicalCurrentPairToNext
        trajectory transitionStart physicalScale offset
        (matchedEventualCanonicalNextPairToCurrent
          trajectory transitionStart physicalScale offset pair) = pair := by
  obtain ⟨currentPair, hcurrentPair, hmap⟩ := List.mem_map.mp hpair
  rw [← hmap]
  rw [matchedEventualCanonicalNextPairToCurrent_currentToNext
    trajectory transitionStart physicalScale offset currentPair hcurrentPair]

/-- Exact genuinely new pair shell: next carrier minus the embedded image. -/
def MatchedEventualCanonicalPairInNewShell
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (pair : Nat × Nat) : Prop :=
  pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (offset + 1) ∧
    pair ∉ matchedEventualCanonicalEmbeddedOldPairCarrier
      trajectory transitionStart physicalScale offset

theorem matchedEventualCanonicalPair_old_or_newShell
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (offset + 1)) :
    pair ∈ matchedEventualCanonicalEmbeddedOldPairCarrier
        trajectory transitionStart physicalScale offset ∨
      MatchedEventualCanonicalPairInNewShell
        trajectory transitionStart physicalScale offset pair := by
  by_cases hold : pair ∈ matchedEventualCanonicalEmbeddedOldPairCarrier
      trajectory transitionStart physicalScale offset
  · exact Or.inl hold
  · exact Or.inr ⟨hpair, hold⟩

/-! ## 2. Two independently estimable regional envelopes -/

/-- Two-sided debt transport on the literal embedded old component. -/
structure MatchedEventualCanonicalTransportedCapacityDebtEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat) : Type 1 where
  variation : Nat -> Q'
  variation_nonnegative : forall offset, (0 : Q') <= variation offset
  tailControl : AntitoneTailControl variation
  current_le_next : forall offset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale offset ->
      matchedEventualCanonicalRoutedCapacityDebtOnPair
          trajectory transitionStart physicalScale offset pair <=
        matchedEventualCanonicalRoutedCapacityDebtOnPair
            trajectory transitionStart physicalScale (offset + 1)
            (matchedEventualCanonicalCurrentPairToNext
              trajectory transitionStart physicalScale offset pair) +
          variation offset
  next_le_current : forall offset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale offset ->
      matchedEventualCanonicalRoutedCapacityDebtOnPair
          trajectory transitionStart physicalScale (offset + 1)
          (matchedEventualCanonicalCurrentPairToNext
            trajectory transitionStart physicalScale offset pair) <=
        matchedEventualCanonicalRoutedCapacityDebtOnPair
            trajectory transitionStart physicalScale offset pair +
          variation offset

/-- One comparison on the genuinely new pair shell. -/
structure MatchedEventualCanonicalNewShellCapacityDebtEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat) : Type 1 where
  variation : Nat -> Q'
  variation_nonnegative : forall offset, (0 : Q') <= variation offset
  tailControl : AntitoneTailControl variation
  next_le_current : forall offset pair,
    MatchedEventualCanonicalPairInNewShell
      trajectory transitionStart physicalScale offset pair ->
      matchedEventualCanonicalRoutedCapacityDebtOnPair
          trajectory transitionStart physicalScale (offset + 1) pair <=
        matchedEventualCanonicalRoutedCapacityDebtOnPair
            trajectory transitionStart physicalScale offset
            (matchedEventualCanonicalNextPairToCurrent
              trajectory transitionStart physicalScale offset pair) +
          variation offset

private theorem base_add_leftVariation_le_total
    (base leftVariation rightVariation : Q')
    (hright : (0 : Q') <= rightVariation) :
    base + leftVariation <= base + (leftVariation + rightVariation) := by
  exact Q'.add_le_add_left base leftVariation
    (leftVariation + rightVariation)
    (Q'.add_le_self_of_nonneg leftVariation rightVariation hright)

private theorem base_add_rightVariation_le_total
    (base leftVariation rightVariation : Q')
    (hleft : (0 : Q') <= leftVariation) :
    base + rightVariation <= base + (leftVariation + rightVariation) := by
  have hgrow : rightVariation <= rightVariation + leftVariation :=
    Q'.add_le_self_of_nonneg rightVariation leftVariation hleft
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add_left base rightVariation
      (rightVariation + leftVariation) hgrow)
    (Q'.le_of_eqv
      (Q'.add_eqv_congr_left base
        (rightVariation + leftVariation)
        (leftVariation + rightVariation)
        (Q'.add_comm_eqv rightVariation leftVariation)))

/-! ## 3. Regional estimates contract to the one correlated envelope -/

def matchedEventualCanonicalCorrelatedCapacityDebtEnvelopeOfTransportAndShell
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (transport : MatchedEventualCanonicalTransportedCapacityDebtEnvelope
      trajectory transitionStart physicalScale)
    (shell : MatchedEventualCanonicalNewShellCapacityDebtEnvelope
      trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalCorrelatedCapacityDebtEnvelope
      trajectory transitionStart physicalScale where
  variation := fun offset =>
    transport.variation offset + shell.variation offset
  variation_nonnegative := fun offset =>
    Q'.zero_le_add _ _
      (transport.variation_nonnegative offset)
      (shell.variation_nonnegative offset)
  tailControl := addAntitoneTailControl
    transport.tailControl shell.tailControl
  current_le_next := by
    intro offset pair hpair
    exact Q'.le_trans' _ _ _
      (transport.current_le_next offset pair hpair)
      (base_add_leftVariation_le_total
        (matchedEventualCanonicalRoutedCapacityDebtOnPair
          trajectory transitionStart physicalScale (offset + 1)
          (matchedEventualCanonicalCurrentPairToNext
            trajectory transitionStart physicalScale offset pair))
        (transport.variation offset) (shell.variation offset)
        (shell.variation_nonnegative offset))
  next_le_current := by
    intro offset pair hpair
    rcases matchedEventualCanonicalPair_old_or_newShell
      trajectory transitionStart physicalScale offset pair hpair with
      hold | hshell
    · obtain ⟨currentPair, hcurrentPair, hmap⟩ := List.mem_map.mp hold
      rw [← hmap]
      rw [matchedEventualCanonicalNextPairToCurrent_currentToNext
        trajectory transitionStart physicalScale offset currentPair hcurrentPair]
      exact Q'.le_trans' _ _ _
        (transport.next_le_current offset currentPair hcurrentPair)
        (base_add_leftVariation_le_total
          (matchedEventualCanonicalRoutedCapacityDebtOnPair
            trajectory transitionStart physicalScale offset currentPair)
          (transport.variation offset) (shell.variation offset)
          (shell.variation_nonnegative offset))
    · exact Q'.le_trans' _ _ _
        (shell.next_le_current offset pair hshell)
        (base_add_rightVariation_le_total
          (matchedEventualCanonicalRoutedCapacityDebtOnPair
            trajectory transitionStart physicalScale offset
            (matchedEventualCanonicalNextPairToCurrent
              trajectory transitionStart physicalScale offset pair))
          (transport.variation offset) (shell.variation offset)
          (transport.variation_nonnegative offset))

/-- Scale-indexed transported-old and shell estimates, plus the unchanged
prefix-tail closure, construct the exact matched completed family. -/
def matchedEventualCanonicalCorrelatedCapacityDebtCompletedFamilyOfTransportAndShell
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (transport : forall physicalScale,
      MatchedEventualCanonicalTransportedCapacityDebtEnvelope
        trajectory transitionStart physicalScale)
    (shell : forall physicalScale,
      MatchedEventualCanonicalNewShellCapacityDebtEnvelope
        trajectory transitionStart physicalScale)
    (tailAllowance : Nat -> Q')
    (tailAllowance_pos : forall physicalScale,
      (0 : Q') < tailAllowance physicalScale)
    (initial_closure : forall physicalScale,
      matchedEventualCanonicalRoutedCapacityDebtMaximum
            trajectory transitionStart physicalScale 0 +
          prefixTailTotalBudget
            (matchedEventualCanonicalRoutedCapacityDebtMaximumVariation
              (matchedEventualCanonicalCorrelatedCapacityDebtEnvelopeOfTransportAndShell
                (transport physicalScale) (shell physicalScale)))
            (tailAllowance physicalScale) <=
        (1 : Q')) :
    DynamicVacuumSectorCompletedFamily 0 :=
  matchedEventualCanonicalCorrelatedCapacityDebtCompletedFamily
    trajectory transitionStart
    (fun physicalScale =>
      matchedEventualCanonicalCorrelatedCapacityDebtEnvelopeOfTransportAndShell
        (transport physicalScale) (shell physicalScale))
    tailAllowance tailAllowance_pos initial_closure

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellCompiler

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellCompiler.matchedEventualCanonicalCurrentPairToNext_mem_embeddedOld
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellCompiler.matchedEventualCanonicalEmbeddedOldPairCarrier_mem_next
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellCompiler.matchedEventualCanonicalCurrentPairToNext_nextToCurrent_of_mem_embeddedOld
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellCompiler.matchedEventualCanonicalPair_old_or_newShell
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellCompiler.matchedEventualCanonicalCorrelatedCapacityDebtEnvelopeOfTransportAndShell
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellCompiler.matchedEventualCanonicalCorrelatedCapacityDebtCompletedFamilyOfTransportAndShell
