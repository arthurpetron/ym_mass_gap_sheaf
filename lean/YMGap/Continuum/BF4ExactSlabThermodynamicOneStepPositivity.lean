/-
# Positivity of the ORIGINAL completed geometric one-step transfer

The proved site/one-step identity and original volume comparison establish
nonnegativity of the existing dense one-step pairing. The existing Cauchy
pairing limits extend that fact to the SAME thermodynamic completion.
No new completion, operator, norm, positivity premise or root substitution
is introduced. Symmetry and composition then give positivity at every
nonnegative integer lag, not only the previously known even lags.

The SU(2) nome 1/1024 and lattice spacing remain fixed. Positivity is not
strict positivity or injectivity. Identification with rootAction, arbitrary
state range/time-zero control, the physical Hamiltonian, continuum scaling,
other compact simple groups and the Clay target remain open.
-/

import YMGap.Continuum.BF4ExactSlabSiteOneStepForm
import YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime

namespace YMGap.Continuum.BF4ExactSlabThermodynamicOneStepPositivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabSiteOneStepForm
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeStates
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeBalance
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime

theorem presented_one_step_nonnegative (p : Presentation) :
    leEv czero (presentedForm (translate 1 p) p) := by
  have h : RCnonneg (completedInner (timeState 1 p) (timeState 0 p)) := by
    rw [time_inner_bulk 1 ⟨1, by decide⟩ ⟨0, by decide⟩ p.expression p.expression]
    exact one_step_form_nonnegative p.expression
  rw [timeState_pin, timeState_zero, completedInner_embedPresentation] at h
  exact h

theorem representative_one_step_nonnegative (X : seminorm.Cauchy) :
    leEv czero (representativeInner (timeCauchy 1 X) X) :=
  leEv_of_convergesTo_le (convergesTo_const _) (pairSequence_converges (timeCauchy 1 X) X)
    (fun n => presented_one_step_nonnegative (X.seq n))

/-- The actual geometric T1 is positive on the entire original completion. -/
theorem completedTime_one_nonnegative (x : Completion) :
    RCnonneg (completedInner (completedTime 1 x) x) := by
  refine Quotient.inductionOn x ?_
  exact representative_one_step_nonnegative

/-- Odd lags now follow as well, by the existing same-object time composition. -/
theorem completedTime_nonnegative : ∀ lag : Nat, ∀ x : Completion,
    RCnonneg (completedInner x (completedTime lag x))
  | 0, x => by rw [completedTime_zero]; exact completedInner_nonnegative x
  | 1, x => by rw [completedInner_symm]; exact completedTime_one_nonnegative x
  | lag+2, x => by
      have h := completedTime_nonnegative lag (completedTime 1 x)
      rw [completedTime_comp, completedTime_moments] at h
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

end YMGap.Continuum.BF4ExactSlabThermodynamicOneStepPositivity

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicOneStepPositivity.presented_one_step_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicOneStepPositivity.representative_one_step_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicOneStepPositivity.completedTime_one_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicOneStepPositivity.completedTime_nonnegative
