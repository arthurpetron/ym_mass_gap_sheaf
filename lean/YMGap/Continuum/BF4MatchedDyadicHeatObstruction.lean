/-
# The exact physical dyadic bridge has no rational trajectory

The existing physical envelope defines t(g)=4*g^2 with g : Q'. Its
specialized dyadic bridge requires t(coupling(s))/4 = 2^(-s) at EVERY
natural scale. At scale one this asks for a rational square equal to
1/2, which is impossible by constructive integer descent.

This refutes MatchedDyadicSameActionAFBridge as currently specified;
it does not refute CubicMarginLaw, the generic AF envelope, arbitrary
nome heat completion, or Yang--Mills theory. No field is changed here.
The conditional dyadic physical bit-growth/core-length declarations
cannot supply physical instances through this impossible input.
The matched pointwise-window interface also contains this bridge and is
therefore uninhabited. Generic heat windows without this specialization
are not refuted.
-/

import YMGap.Constructive.RationalSquareHalfObstruction
import YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory

namespace YMGap.Continuum.BF4MatchedDyadicHeatObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4AFHeatSpacing
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory
open YMGap.Continuum.BF4FarautAFCutoffGrowth

local infix:50 " ≈ " => Q'.eqv

/-- Exact square chart, before any physical-scale interpretation. -/
theorem quarter_physicalTime (g : Q') : quarter * physicalTime g ≈ g*g :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv quarter 4 (g*g)))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (by decide : quarter * (4 : Q') ≈ 1))
      (Q'.one_mul_eqv _))

/-- Any envelope with the exact square heat chart has the same obstruction.
No claim is made about envelopes with other heat-time functions. -/
theorem squareTime_dyadicBridge_uninhabited
    {E : BareAFDiagnostic.AFEnvelope} {coupling : Nat → Q'}
    (ht : ∀ g, E.t g ≈ physicalTime g)
    (bridge : DyadicSameActionAFBridge E coupling) : False := by
  have hs : quarter * E.t (coupling 1) ≈ coupling 1 * coupling 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left quarter _ _ (ht (coupling 1)))
      (quarter_physicalTime (coupling 1))
  apply Q'.square_ne_half (coupling 1)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hs) (bridge.heat_time 1)

/-- Refutation of this exact rational dyadic specialization, not closure
of any physical or continuum obligation. Only its heat_time field is used. -/
theorem matchedDyadicSameActionAFBridge_uninhabited
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁} {coupling : Nat → Q'}
    (bridge : MatchedDyadicSameActionAFBridge family law spacing coupling) : False :=
  squareTime_dyadicBridge_uninhabited (fun _ => Q'.eqv_refl _) bridge

/-- The matched pointwise windows inherit the contradictory bridge field. -/
theorem matchedPhysicalPointwiseHeatWindows_uninhabited
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁} {coupling : Nat → Q'}
    {Local : Type} {x : Nat → Local → Q'} {lower upper : Nat → Q'}
    (windows : MatchedPhysicalPointwiseHeatWindows family law spacing coupling
      Local x lower upper) : False :=
  matchedDyadicSameActionAFBridge_uninhabited windows.bridge

end YMGap.Continuum.BF4MatchedDyadicHeatObstruction

#print axioms YMGap.Continuum.BF4MatchedDyadicHeatObstruction.quarter_physicalTime
#print axioms YMGap.Continuum.BF4MatchedDyadicHeatObstruction.squareTime_dyadicBridge_uninhabited
#print axioms YMGap.Continuum.BF4MatchedDyadicHeatObstruction.matchedDyadicSameActionAFBridge_uninhabited
#print axioms YMGap.Continuum.BF4MatchedDyadicHeatObstruction.matchedPhysicalPointwiseHeatWindows_uninhabited
