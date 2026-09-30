/-
# Finite conditional Haar equivariance for the existing gauge steps

Direct and inverse left/right shears commute with any in-range conditional
Haar projection other than integration of their multiplier. Composition
uses proved carrier congruence, not pointwise or raw coefficient equality.
The same result holds for finite physical integration schedules. This is
not yet equivariance of the weighted conditional inverse or its completion.
-/

import YMGap.Continuum.SU2QuaternionConjugationProjection
import YMGap.Continuum.SU2QuaternionSelectedProjectionFixed
import YMGap.Continuum.SU2QuaternionHaarCarrierProjection
import YMGap.Continuum.SU2QuaternionSelectedTranslationCarrier

namespace YMGap.Continuum.SU2QuaternionSelectedProjectionEquivariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslation
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2QuaternionSelectedConditionalTranslation
open YMGap.Continuum.SU2QuaternionConjugationProjection
open YMGap.Continuum.SU2QuaternionSelectedProjectionFixed
open YMGap.Continuum.SU2QuaternionHaarCarrierProjection
open YMGap.Continuum.SU2QuaternionSelectedTranslationCarrier

variable (tailBlocks selected multiplier : Nat) (hb : 0 < tailBlocks)
  (hs : selected < tailBlocks+1) (hm : multiplier < tailBlocks+1)
  (hne : selected ≠ multiplier)

private abbrev direct (right : Bool) :=
  if right then selectedRightTranslatedPolynomial tailBlocks selected multiplier hb hs hm hne
  else selectedLeftTranslatedPolynomial tailBlocks selected multiplier hb hs hm hne

private theorem direct_coeff (right : Bool) {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (direct tailBlocks selected multiplier hb hs hm hne right p)
      (direct tailBlocks selected multiplier hb hs hm hne right q) := by
  cases right
  · exact selectedLeftTranslatedPolynomial_coeffEqv tailBlocks selected multiplier hb hs hm hne h
  · exact selectedRightTranslatedPolynomial_coeffEqv tailBlocks selected multiplier hb hs hm hne h

private theorem project_direct (right : Bool) (block : Nat)
    (hk : block < tailBlocks+1) (hkm : block ≠ multiplier) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tailBlocks+1) p) :
    HaarCarrierEqv (tailBlocks+1)
      (project block (direct tailBlocks selected multiplier hb hs hm hne right p))
      (direct tailBlocks selected multiplier hb hs hm hne right (project block p)) := by
  by_cases hks : block = selected
  · subst block
    cases right
    · exact (project_selectedLeft tailBlocks selected multiplier hb hs hm hne p hp).trans
        (selectedLeft_project_fixed tailBlocks selected multiplier hb hs hm hne p hp).symm
    · exact (project_selectedRight tailBlocks selected multiplier hb hs hm hne p hp).trans
        (selectedRight_project_fixed tailBlocks selected multiplier hb hs hm hne p hp).symm
  · cases right
    · exact RatPolyCoeffEqv.haarCarrier
        (project_spectator_selectedLeft tailBlocks selected multiplier hb hs hm hne block hk hks hkm p)
    · exact RatPolyCoeffEqv.haarCarrier
        (project_spectator_selectedRight tailBlocks selected multiplier hb hs hm hne block hk hks hkm p)

private theorem project_inverse (right : Bool) (block : Nat)
    (hk : block < tailBlocks+1) (hkm : block ≠ multiplier) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tailBlocks+1) p) :
    HaarCarrierEqv (tailBlocks+1)
      (project block (conjugateQuaternionBlockPolynomial (tailBlocks+1) multiplier
        (direct tailBlocks selected multiplier hb hs hm hne right
          (conjugateQuaternionBlockPolynomial (tailBlocks+1) multiplier p))))
      (conjugateQuaternionBlockPolynomial (tailBlocks+1) multiplier
        (direct tailBlocks selected multiplier hb hs hm hne right
          (conjugateQuaternionBlockPolynomial (tailBlocks+1) multiplier (project block p)))) := by
  have hmk : multiplier ≠ block := fun h => hkm h.symm
  refine (RatPolyCoeffEqv.haarCarrier (project_conjugate (tailBlocks+1) multiplier block hmk _)).trans ?_
  refine (conjugate_carrier (project_direct tailBlocks selected multiplier hb hs hm hne
    right block hk hkm _ (conjugateQuaternionBlockPolynomial_supported _ _ p hp))).trans ?_
  exact RatPolyCoeffEqv.haarCarrier (conjugateQuaternionBlockPolynomial_coeffEqv _ _
    (direct_coeff tailBlocks selected multiplier hb hs hm hne right
      (project_conjugate (tailBlocks+1) multiplier block hmk p)))

/-- The actual step data, all four orientations, with its multiplier excluded. -/
theorem project_step {tailBlocks : Nat} (hb : 0 < tailBlocks)
    (step : SelectedTranslationStep tailBlocks) (block : Nat)
    (hk : block < tailBlocks+1) (hkm : block ≠ step.multiplier) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tailBlocks+1) p) :
    HaarCarrierEqv (tailBlocks+1) (project block (applySelectedTranslationStep hb step p))
      (applySelectedTranslationStep hb step (project block p)) := by
  cases hside : step.side <;> cases hor : step.multiplierOrientation <;>
    simp only [applySelectedTranslationStep, hside, hor]
  · exact project_direct tailBlocks step.selected step.multiplier hb step.selected_lt
      step.multiplier_lt step.distinct false block hk hkm p hp
  · exact project_inverse tailBlocks step.selected step.multiplier hb step.selected_lt
      step.multiplier_lt step.distinct false block hk hkm p hp
  · exact project_direct tailBlocks step.selected step.multiplier hb step.selected_lt
      step.multiplier_lt step.distinct true block hk hkm p hp
  · exact project_inverse tailBlocks step.selected step.multiplier hb step.selected_lt
      step.multiplier_lt step.distinct true block hk hkm p hp

/-- Composing actual steps is legitimate because they preserve the carrier
relation, including at every supported intermediate polynomial. -/
theorem project_steps {tailBlocks : Nat} (hb : 0 < tailBlocks)
    (steps : List (SelectedTranslationStep tailBlocks)) (block : Nat)
    (hk : block < tailBlocks+1)
    (hne : ∀ step, step ∈ steps → block ≠ step.multiplier)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (tailBlocks+1) p) :
    HaarCarrierEqv (tailBlocks+1) (project block (applySelectedTranslationSteps hb steps p))
      (applySelectedTranslationSteps hb steps (project block p)) := by
  induction steps generalizing p with
  | nil => exact .refl _ _
  | cons step rest ih =>
      refine (ih (fun s hs => hne s (List.mem_cons_of_mem step hs))
        (applySelectedTranslationStep hb step p)
        (applySelectedTranslationStep_supported hb step p)).trans ?_
      exact applySelectedTranslationSteps_preserves_haarCarrierEqv hb rest
        (project_supported block (applySelectedTranslationStep_supported hb step p))
        (applySelectedTranslationStep_supported hb step (project block p))
        (project_step hb step block hk (hne step List.mem_cons_self) p hp)

/-- Any physical integration schedule avoiding all ledger multipliers
commutes with that ledger, without assuming distinct schedule entries. -/
theorem familyProject_steps {tailBlocks : Nat} (hb : 0 < tailBlocks)
    (steps : List (SelectedTranslationStep tailBlocks)) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < tailBlocks+1)
    (hne : ∀ step, step ∈ steps → ∀ i, i ∈ ids → i ≠ step.multiplier)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (tailBlocks+1) p) :
    HaarCarrierEqv (tailBlocks+1)
      (familyProject ids (applySelectedTranslationSteps hb steps p))
      (applySelectedTranslationSteps hb steps (familyProject ids p)) := by
  induction ids generalizing p with
  | nil => exact .refl _ _
  | cons i ids ih =>
      have hi := hids i List.mem_cons_self
      have ht : ∀ j, j ∈ ids → j < tailBlocks+1 :=
        fun j hj => hids j (List.mem_cons_of_mem i hj)
      refine (familyProject_preserves_haarCarrierEqv (tailBlocks+1) ids ht
        (project_steps hb steps i hi
          (fun step hs => hne step hs i List.mem_cons_self) p hp)).trans ?_
      exact ih ht (fun step hs j hj => hne step hs j (List.mem_cons_of_mem i hj))
        (project i p) (project_supported i hp)

#print axioms project_step
#print axioms project_steps
#print axioms familyProject_steps

end YMGap.Continuum.SU2QuaternionSelectedProjectionEquivariance
