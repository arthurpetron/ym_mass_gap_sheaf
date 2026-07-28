/-
# Positive BF4 raw-row mass feeds the retained Harnack kernel

`BF4SU2OuterJointCarrierRawRowMass` turns strict positivity of the explicit
coarse raw-row sum into a literal enumerated joint carrier.  The dynamic
pointwise-heat layer already proves a quantitative Feynman--Kac floor from
such a carrier.  This module joins those statements.

The resulting lower bound is non-vacuous: raw-row positivity constructs a
singleton retained path before the conditional sum is estimated.  The
seventeen-face binary-normality counterexample is included as a checked
instance.  It has no closed-sheet multicover, yet its raw row is strictly
positive and its enlarged retained path carrier is inhabited.

This bridge does not prove raw-row positivity for every positive fine row
and does not supply the spacing-uniform kinetic/potential estimates.

## Axiom gate

Composition of already-audited constructive data only.  No `Classical.*`,
`sorry`, `native_decide`, custom axiom, or noncomputable declaration is
used.
-/

import YMGap.Continuum.BF4SU2OuterJointCarrierRawRowMass
import YMGap.Continuum.BF4SU2OuterJointCarrierStrictEnlargement
import YMGap.Continuum.SU2PointwiseHeatDynamicWindow

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

namespace YMGap.Continuum.BF4SU2OuterRawRowMassRetainedHarnack

open YMGap.Constructive
open YMGap.Continuum.BF4CompletedRetainedConditionalOrder
open YMGap.Continuum.BF4FarautJointCarrierAFBudget
open YMGap.Continuum.BF4GroupedFeynmanKacHarnack
open YMGap.Continuum.BF4SU2OuterBinaryLayerCounterexample
open YMGap.Continuum.BF4SU2OuterBinaryMulticoverReduction
open YMGap.Continuum.BF4SU2OuterBinaryMulticoverNoGo
open YMGap.Continuum.BF4SU2OuterJointCarrierEnumeration
open YMGap.Continuum.BF4SU2OuterJointCarrierRawRowMass
open YMGap.Continuum.BF4SU2OuterJointCarrierStrictEnlargement
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PointwiseHeatDynamicWindow

/-! ## 1. Raw mass makes the retained path carrier nonempty -/

theorem wholeSlabJointCarrierPaths_length_pos_of_rawRowMass
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (hmass :
      (0 : Q') < wholeSlabJointRawRowMass S fineState) :
    0 < (wholeSlabJointCarrierPaths S fineState).length :=
  wholeSlabJointCarrierPaths_length_pos
    (jointCarrierNonemptyOfRawRowMassPositive hmass)

/-! ## 2. Direct non-vacuous grouped Feynman--Kac floor -/

/-- Strict raw-row mass is the exact support input needed by the witnessed
dynamic conditional lower bound. -/
theorem wholeSlabDynamicConditionalPushforward_ge_rawRowMass_floor
    {Source Target : Type}
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (hmass :
      (0 : Q') < wholeSlabJointRawRowMass S fineState)
    (kineticWeight :
      Source → Target →
        List (WholeSlabJointCarrierCode S fineState) →
          CReal)
    (potential :
      WholeSlabJointCarrierCode S fineState → Q')
    (potentialFloor : Q')
    (potential_floor_pos :
      (0 : Q') < potentialFloor)
    (potential_lower :
      ∀ state, potentialFloor ≤ potential state)
    (sources : List Source) (targets : List Target)
    (harnack :
      DynamicCompletedRetainedHarnackData
        (wholeSlabJointCarrierPaths S fineState)
        kineticWeight sources targets)
    (source : Source) (hsource : source ∈ sources)
    (target : Target) (htarget : target ∈ targets) :
    ExpPos.geRat
      (completedConditionalPathPushforward
        (wholeSlabJointCarrierPaths S fineState)
        kineticWeight potential source target)
      (potentialFloor ^ 1 * harnack.lower) :=
  wholeSlabDynamicConditionalPushforward_ge_witnessed_floor
    (jointCarrierNonemptyOfRawRowMassPositive hmass)
    kineticWeight potential potentialFloor
    potential_floor_pos potential_lower
    sources targets harnack
    source hsource target htarget

/-! ## 3. The strict-enlargement row is a non-vacuous instance -/

theorem normalityCounter_rawRowMass_pos :
    (0 : Q') <
      wholeSlabJointRawRowMass
        counterScalePair normalityCounterState :=
  rawRowMass_pos_of_jointCarrierNonempty
    { candidates_positive :=
        normalityCounterJointCarrierCodes_length_pos }

theorem normalityCounter_retainedPaths_length_pos :
    0 <
      (wholeSlabJointCarrierPaths
        counterScalePair normalityCounterState).length :=
  wholeSlabJointCarrierPaths_length_pos_of_rawRowMass
    normalityCounter_rawRowMass_pos

/-- The enlarged analytic carrier remains nonempty exactly where the old
closed-sheet carrier fails. -/
theorem normalityCounter_no_multicover_but_rawRowMass_pos :
    (BinaryEvenSlabMulticover
        counterScalePair normalityCounterState → False) ∧
      (0 : Q') <
        wholeSlabJointRawRowMass
          counterScalePair normalityCounterState :=
  ⟨normalityCounterState_no_multicover,
    normalityCounter_rawRowMass_pos⟩

#print axioms wholeSlabJointCarrierPaths_length_pos_of_rawRowMass
#print axioms wholeSlabDynamicConditionalPushforward_ge_rawRowMass_floor
#print axioms normalityCounter_rawRowMass_pos
#print axioms normalityCounter_retainedPaths_length_pos
#print axioms normalityCounter_no_multicover_but_rawRowMass_pos

end YMGap.Continuum.BF4SU2OuterRawRowMassRetainedHarnack
