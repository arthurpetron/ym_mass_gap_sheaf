/-
# Direct selected shears fix an already-integrated selected block

The existing selected left and right translations leave a projected input
fixed on the supported Haar carrier.  The raw coefficient relation is not
asserted: exposing and restoring a pair may pad trailing zero coordinates.
No inverse-orientation case or completed-space action is included.
-/

import YMGap.Continuum.SU2QuaternionSelectedConditionalTranslation
import YMGap.Continuum.SU2QuaternionSelectedHaarTranslationDegree

namespace YMGap.Continuum.SU2QuaternionSelectedProjectionFixed

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslation
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationDegree
open YMGap.Continuum.SU2QuaternionSelectedConditionalTranslation
open YMGap.Continuum.QuaternionHaarSquareCertificate

private theorem direct_project_independent
    (right : Bool) (tailBlocks selected multiplier : Nat)
    (hb : 0 < tailBlocks)
    (hs : selected < tailBlocks + 1)
    (hm : multiplier < tailBlocks + 1)
    (hne : selected ≠ multiplier) (p : RatPoly) :
    QuaternionBlockIndependent selected
      (if right then
        selectedRightTranslatedPolynomial tailBlocks selected multiplier
          hb hs hm hne (project selected p)
       else
        selectedLeftTranslatedPolynomial tailBlocks selected multiplier
          hb hs hm hne (project selected p)) := by
  let step : SelectedTranslationStep tailBlocks :=
    { selected := selected
      multiplier := multiplier
      selected_lt := hs
      multiplier_lt := hm
      distinct := hne
      side := if right then .right else .left
      multiplierOrientation := .direct }
  have hin : QuaternionBlockDegreeAtMost selected 0 (project selected p) := by
    have h := independent_has_degree_zero (project_independent selected p)
    intro term hterm
    exact Nat.le_of_eq (h term hterm)
  have hout : QuaternionBlockDegreeAtMost selected 0
      (applySelectedTranslationStep hb step (project selected p)) :=
    applySelectedTranslationStep_degreeAtMost_nonMultiplier hb step
      hs hne (project selected p) hin
  apply degree_zero_independent
  intro term hterm
  cases right with
  | false =>
      have hzero : quaternionBlockDegree term.1 selected ≤ 0 := by
        exact hout term (by simpa [step, applySelectedTranslationStep] using hterm)
      exact Nat.le_zero.mp hzero
  | true =>
      have hzero : quaternionBlockDegree term.1 selected ≤ 0 := by
        exact hout term (by simpa [step, applySelectedTranslationStep] using hterm)
      exact Nat.le_zero.mp hzero

/-- The original direct left shear fixes a conditionally projected input in
the exact supported Haar quotient, with no multiplier independence premise. -/
theorem selectedLeft_project_fixed
    (tailBlocks selected multiplier : Nat)
    (hb : 0 < tailBlocks)
    (hs : selected < tailBlocks + 1)
    (hm : multiplier < tailBlocks + 1)
    (hne : selected ≠ multiplier)
    (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tailBlocks + 1) p) :
    HaarCarrierEqv (tailBlocks + 1)
      (selectedLeftTranslatedPolynomial tailBlocks selected multiplier
        hb hs hm hne (project selected p))
      (project selected p) := by
  let r := selectedLeftTranslatedPolynomial tailBlocks selected multiplier
    hb hs hm hne (project selected p)
  have hind : QuaternionBlockIndependent selected r := by
    simpa [r] using
      (direct_project_independent false tailBlocks selected multiplier
        hb hs hm hne p)
  exact (RatPolyCoeffEqv.haarCarrier
      (project_fixed selected r hind).symm).trans
    ((project_selectedLeft tailBlocks selected multiplier hb hs hm hne
      (project selected p) (project_supported selected hp)).trans
      (RatPolyCoeffEqv.haarCarrier (project_idempotent selected p)))

/-- Right Hamilton-order companion on the same original carrier. -/
theorem selectedRight_project_fixed
    (tailBlocks selected multiplier : Nat)
    (hb : 0 < tailBlocks)
    (hs : selected < tailBlocks + 1)
    (hm : multiplier < tailBlocks + 1)
    (hne : selected ≠ multiplier)
    (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tailBlocks + 1) p) :
    HaarCarrierEqv (tailBlocks + 1)
      (selectedRightTranslatedPolynomial tailBlocks selected multiplier
        hb hs hm hne (project selected p))
      (project selected p) := by
  let r := selectedRightTranslatedPolynomial tailBlocks selected multiplier
    hb hs hm hne (project selected p)
  have hind : QuaternionBlockIndependent selected r := by
    simpa [r] using
      (direct_project_independent true tailBlocks selected multiplier
        hb hs hm hne p)
  exact (RatPolyCoeffEqv.haarCarrier
      (project_fixed selected r hind).symm).trans
    ((project_selectedRight tailBlocks selected multiplier hb hs hm hne
      (project selected p) (project_supported selected hp)).trans
      (RatPolyCoeffEqv.haarCarrier (project_idempotent selected p)))

#print axioms selectedLeft_project_fixed
#print axioms selectedRight_project_fixed

end YMGap.Continuum.SU2QuaternionSelectedProjectionFixed
