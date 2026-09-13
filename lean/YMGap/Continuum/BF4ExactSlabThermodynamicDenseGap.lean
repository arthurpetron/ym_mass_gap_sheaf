/-
# Derived strict form bound on ORIGINAL centered dense states

The moments are the squared norms of the ACTUAL completed time translates
of a centered original presentation. Positivity, contraction and sharp
Cauchy--Schwarz give the dyadic moment inequalities. The proved same-object
time-decay envelope supplies a positive observable-dependent prefactor.
The existing abstract constructive dyadic theorem removes that prefactor:

  <v,T_2 v> <= (1/2)<v,v>,  v = center(embedPresentation p).

No gap premise, model operator, surrogate state or nonzero-norm assumption
is used. The bound is uniform over these centered dense presentations at
nome 1/1024, fixed lattice spacing. Extension to every completed complement
vector is downstream in BF4ExactSlabThermodynamicCompletedGap. Nonzero
excitations, vacuum isolation and continuum are not asserted here.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicTimeDecayRate
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap

namespace YMGap.Continuum.BF4ExactSlabThermodynamicDenseGap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra (PlaquetteExpression)
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation (Presentation)
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion (embedPresentation)
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion (center)
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeCorrelations
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeDecayRate
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap (dyadic_geometric_first_le)

def moment (p : Presentation) (n : Nat) : CReal := (timeCovarianceRepresentative n n p p).1

def momentCauchy (p : Presentation) (n : Nat) : QCauchy (moment p n).approx :=
  (timeCovarianceRepresentative n n p p).2.1

theorem moment_pin (p : Presentation) (n : Nat) :
    completedInner (completedTime n (center (embedPresentation p))) (completedTime n (center (embedPresentation p))) =
      Quotient.mk crealSetoid (moment p n) :=
  (timeCovariance_operator n n p p).symm.trans (timeCovarianceRepresentative n n p p).2.2

theorem moment_zero (p : Presentation) :
    completedInner (center (embedPresentation p)) (center (embedPresentation p)) = Quotient.mk crealSetoid (moment p 0) := by
  have h := moment_pin p 0
  rw [completedTime_zero] at h
  exact h

theorem moment_nonnegative (p : Presentation) (n : Nat) : leEv czero (moment p n) := by
  have h := completedInner_nonnegative (completedTime n (center (embedPresentation p)))
  rw [moment_pin] at h
  exact h

theorem moment_le_zero (p : Presentation) (n : Nat) : leEv (moment p n) (moment p 0) := by
  have h := completedTime_contraction n (center (embedPresentation p))
  rw [moment_pin, moment_zero] at h
  exact h

theorem moment_dyadic (p : Presentation) (n : Nat) :
    leEv (CReal.mul (moment p n) (moment p n)) (CReal.mul (moment p (n+n)) (moment p 0)) := by
  let x := center (embedPresentation p)
  have hn : completedInner x (completedTime (n+n) x) = Quotient.mk crealSetoid (moment p n) :=
    (completedTime_moments n n x x).symm.trans (moment_pin p n)
  have h := completedInner_cauchySchwarz x (completedTime (n+n) x)
  rw [hn, moment_zero, moment_pin] at h
  exact leEv_trans h (leEv_of_equiv (CRealAlg.cmul_comm _ _))

private theorem le_abs (a : CReal) : leEv a (CReal.abs a) := by
  intro epsilon he
  exact ⟨0, fun k _ => Q'.le_trans' _ _ _ (Q'.le_abs_self (a.approx k))
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))⟩

theorem moment_envelope (p : Presentation) (n : Nat) :
    leEv (moment p n) (ofQ' (positivePrefactor p.expression p.expression * HalfPow.half^n)) := by
  exact leEv_trans (le_abs _) (leEv_trans (timeCovariance_geometric_bound n n p.expression p.expression)
    (leEv_ofQ'_of_approx_ge (fun _ => Q'.mul_le_mul_of_nonneg_left _ _ _
      (half_pow_antitone n (n+n) (by omega)) (Q'.le_of_lt (positivePrefactor_pos _ _)))))

theorem moment_first_gap (p : Presentation) :
    leEv (moment p 1) (CReal.mul (ofQ' HalfPow.half) (moment p 0)) :=
  dyadic_geometric_first_le (moment p) HalfPow.half (positivePrefactor p.expression p.expression)
    (by decide) (positivePrefactor_pos _ _) (moment_nonnegative p) (moment_le_zero p)
    (moment_dyadic p) (moment_envelope p)

/-- The constant 1/2 is independent of the original centered dense presentation. -/
theorem dense_twoStep_form_gap (p : Presentation) :
    RCle (completedInner (center (embedPresentation p)) (twoStepTransfer (center (embedPresentation p))))
      (RCscale HalfPow.half (completedInner (center (embedPresentation p)) (center (embedPresentation p)))) := by
  have hpin : completedInner (center (embedPresentation p)) (twoStepTransfer (center (embedPresentation p))) =
      Quotient.mk crealSetoid (moment p 1) :=
    (completedTime_moments 1 1 _ _).symm.trans (moment_pin p 1)
  rw [hpin, moment_zero]
  exact moment_first_gap p

end YMGap.Continuum.BF4ExactSlabThermodynamicDenseGap

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDenseGap.moment
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDenseGap.momentCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDenseGap.moment_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDenseGap.moment_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDenseGap.moment_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDenseGap.moment_le_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDenseGap.moment_dyadic
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDenseGap.moment_envelope
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDenseGap.moment_first_gap
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDenseGap.dense_twoStep_form_gap
