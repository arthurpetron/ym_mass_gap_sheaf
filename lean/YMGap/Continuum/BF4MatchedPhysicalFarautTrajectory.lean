/-
# Same-action Faraut windows on the exact matched BF4 trajectory

`BF4MatchedPhysicalAFBridge.physicalAFEnvelope` is the existing AF envelope
whose weight is definitionally the exact finite observable- or exponent-Gram
matched BF4 block output:

    E.w g = blockedWeight family g.

`SU2PointwiseHeatDynamicWindow.SameActionPointwiseHeatWindows` now forces the
local completed character kernel, its spacing cutoff, and its AF heat budget
to use one and the same envelope weight.  This file performs the physical
specialization.  Its executable bit schedule is therefore literally

    spacingLabelCutoff (blockedWeight family (coupling scale)).

No Padé weight is substituted for the matched block output.

The inputs `CubicMarginLaw`, `PhysicalSpacingEnvelope`, the dyadic bridge,
and the local prefix/tail windows remain explicit Type-valued obligations.
In particular, this module does not claim the still-open four-dimensional
cubic remainder, physical spacing law, or equality between the completed
pointwise character product and the full BF4 slab kernel.

## Constructivity

No `Classical.*`, `Real`, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4MatchedPhysicalAFBridge
import YMGap.Continuum.SU2PointwiseHeatDynamicWindow

namespace YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory

open YMGap.Constructive
open YMGap.Continuum.BareAFDiagnostic
open YMGap.Continuum.BF4FarautAFCutoffGrowth
open YMGap.Continuum.BF4FarautJointCarrierAFBudget
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.SU2PointwiseHeatDynamicWindow

/-! ## 1. Exact matched-action bit schedule -/

/-- The representation cutoff of the exact matched BF4 block output. -/
def matchedPhysicalSpacingBits
    (family : MatchedBlockFamily)
    (coupling : Nat → Q') (scale : Nat) : Nat :=
  SU2PointwiseHeatSpacingCompletion.spacingLabelCutoff
    (blockedWeight family (coupling scale))

/-- On the physical AF envelope, the generic same-action cutoff reduces
definitionally to the matched BF4 block cutoff. -/
theorem sameActionSpacingBits_physical_eq
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q') (scale : Nat) :
    sameActionSpacingBits
        (physicalAFEnvelope family law spacing)
        coupling scale =
      matchedPhysicalSpacingBits family coupling scale :=
  rfl

/-! ## 2. Dyadic bridge and AF growth on the matched action -/

/-- A dyadic same-action identification specialized to the exact matched
BF4 AF envelope.  Its nome field reads `blockedWeight family` by reduction. -/
abbrev MatchedDyadicSameActionAFBridge
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q') : Type :=
  DyadicSameActionAFBridge
    (physicalAFEnvelope family law spacing)
    coupling

/-- The exact matched BF4 cutoff has the uniform dyadic heat cost `≤16`. -/
def matchedPhysicalFarautAFBitGrowth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling) :
    FarautAFBitGrowth
      (physicalAFEnvelope family law spacing)
      coupling
      (matchedPhysicalSpacingBits family coupling) := by
  exact sameActionFarautAFBitGrowth bridge

/-- Consequently the moving cutoff of the exact matched block output occupies
a uniformly bounded physical core length. -/
theorem matchedPhysicalFarautCoreLength_uniform
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling) :
    ∀ scale,
      BF4AFHeatSpacing.heatSpacingRate
          (physicalAFEnvelope family law spacing) *
        (Q'.ofNat
            (46 *
              matchedPhysicalSpacingBits
                family coupling scale) *
          spacing.a (coupling scale)) ≤
      Q'.ofNat 46 * Q'.ofNat 16 := by
  exact sameAction_faraut_core_length_uniform bridge

/-! ## 3. Direct completed heat windows on `blockedWeight` -/

/-- The same-action completed character-window family specialized to the
exact matched BF4 block output.  Unfolding this abbreviation shows that every
local window is evaluated at
`blockedWeight family (coupling scale)`. -/
abbrev MatchedPhysicalPointwiseHeatWindows
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (Local : Type)
    (x : Nat → Local → Q')
    (lower upper : Nat → Q') : Type :=
  SameActionPointwiseHeatWindows
    (physicalAFEnvelope family law spacing)
    coupling Local x lower upper

/-- A matched physical window family forgets to the generic AF interface
without changing its exact `blockedWeight` nome or cutoff. -/
def matchedPhysicalPointwiseAFWindowFamily
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {Local : Type}
    {x : Nat → Local → Q'}
    {lower upper : Nat → Q'}
    (windows :
      MatchedPhysicalPointwiseHeatWindows
        family law spacing coupling
        Local x lower upper) :
    PointwiseHeatAFWindowFamily
      (physicalAFEnvelope family law spacing)
      coupling Local
      (fun scale _ =>
        blockedWeight family (coupling scale))
      x lower upper :=
  windows.toAFWindowFamily

#print axioms matchedPhysicalSpacingBits
#print axioms sameActionSpacingBits_physical_eq
#print axioms MatchedDyadicSameActionAFBridge
#print axioms matchedPhysicalFarautAFBitGrowth
#print axioms matchedPhysicalFarautCoreLength_uniform
#print axioms MatchedPhysicalPointwiseHeatWindows
#print axioms matchedPhysicalPointwiseAFWindowFamily

end YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory
