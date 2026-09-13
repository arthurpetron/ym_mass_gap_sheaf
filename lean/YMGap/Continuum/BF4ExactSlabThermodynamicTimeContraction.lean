/-
# ORIGINAL geometric time is an OS-norm contraction

Reflection positivity gives 2 a(n) <= a(0)+a(2n) for the actual squared
norm a(n). The original polynomial square cap is independent of lag.
Eventual bounded midpoint doubling therefore proves a(n) <= a(0), with
no contraction premise. Linearity gives the exact squared-distance bound.

This is the original interacting thermodynamic law at nome 1/1024 and
fixed lattice spacing. The constant is one, not a strict gap constant.
No nonzero excitation, isolated physical vacuum or continuum gap follows.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicDenseTime
import YMGap.Continuum.BoundedMidpointDoublingEventual

namespace YMGap.Continuum.BF4ExactSlabThermodynamicTimeContraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeStates
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeBalance
open YMGap.Continuum.BF4ExactSlabThermodynamicDenseTime

local notation "B" => completedInner
local notation "two" => Quotient.mk crealSetoid (ofQ' 2)

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => QPoly.q_add_zero_eqv (A.approx n)))

private theorem rc_midpoint_cancel (a b c : RC) :
    RCadd (RCmul two b) (RCsub (RCsub a b) (RCsub b c)) = RCadd a c := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A0 B0 C0
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.mul (.const 2) (.var 1))
      (.add (.add (.var 0) (.neg (.var 1))) (.neg (.add (.var 1) (.neg (.var 2))))))
    (.add (.var 0) (.var 2)) (by decide)
    (fun | 0 => A0.approx n | 1 => B0.approx n | _ => C0.approx n)

theorem pairing_midpoint_bound (x y : Observable) :
    RCle (RCmul two (pairing x y)) (RCadd (pairing x x) (pairing y y)) := by
  have h := RCadd_le_add (RCle_refl (RCmul two (pairing x y)))
    (pairing_nonnegative (subtract x y))
  rw [rc_add_zero,
    RCBilinearDifference.difference_diagonal subtract pairing pairing_sub_left pairing_symm,
    pairing_symm y x, rc_midpoint_cancel] at h
  exact h

/-- The actual norm representative, retaining its original Cauchy data. -/
def timeNorm (n : Nat) (p : Presentation) : CReal :=
  presentedForm (translate n p) (translate n p)

def timeNormCauchy (n : Nat) (p : Presentation) : QCauchy (timeNorm n p).approx :=
  presentedFormCauchy (translate n p) (translate n p)

theorem timeNorm_pin (n : Nat) (p : Presentation) :
    Quotient.mk crealSetoid (timeNorm n p) = B (timeState n p) (timeState n p) :=
  (completedInner_embedPresentation (translate n p) (translate n p)).symm

theorem timeNorm_midpoint (n : Nat) (p : Presentation) :
    leEv (CReal.mul (ofQ' 2) (timeNorm n p)) (CReal.add (timeNorm 0 p) (timeNorm (2*n) p)) := by
  have h := pairing_midpoint_bound (timeObservable 0 p) (timeObservable (2*n) p)
  rw [← completedInner_embedObservable, ← completedInner_embedObservable,
    ← completedInner_embedObservable] at h
  change RCle (RCmul two (B (timeState 0 p) (timeState (2*n) p)))
    (RCadd (B (timeState 0 p) (timeState 0 p)) (B (timeState (2*n) p) (timeState (2*n) p))) at h
  have hmoment : B (timeState 0 p) (timeState (2*n) p) = B (timeState n p) (timeState n p) := by
    rw [Nat.two_mul]
    exact (time_sum n n p p).symm
  rw [hmoment, ← timeNorm_pin, ← timeNorm_pin, ← timeNorm_pin] at h
  exact h

/-- The lag-independent cap is consumed, not assumed to be a relative bound. -/
theorem timeNorm_le_anchor (n : Nat) (p : Presentation) : leEv (timeNorm n p) (timeNorm 0 p) := by
  apply BoundedMidpointDoublingEventual.bounded_midpointDoubling_leEv_anchor
    (fun k => timeNorm k p) (diagonalCeiling p)
  · intro k
    have h := timeState_norm_le k p
    rw [← timeNorm_pin] at h
    exact h
  · have h := completedInner_nonnegative (timeState 0 p)
    rw [← timeNorm_pin] at h
    exact h
  · exact fun k => timeNorm_midpoint k p

theorem timeState_contraction (n : Nat) (p : Presentation) :
    RCle (B (timeState n p) (timeState n p)) (B (embedPresentation p) (embedPresentation p)) := by
  have h := timeNorm_le_anchor n p
  change RCle (Quotient.mk crealSetoid (timeNorm n p)) (Quotient.mk crealSetoid (timeNorm 0 p)) at h
  rw [timeNorm_pin, timeNorm_pin, timeState_zero] at h
  exact h

theorem denseTime_contraction (n : Nat) (x : Carrier) :
    RCle (inner (denseTime n x) (denseTime n x)) (inner x x) := by
  refine Quotient.inductionOn x ?_
  intro o
  refine Quotient.inductionOn o ?_
  intro p
  have h := timeState_contraction n p
  rw [← denseTime_completed_pin, completedInner_embedOSQuotient] at h
  rw [completedInner_embedPresentation] at h
  exact h

theorem distSq_translate (n : Nat) (p q : Presentation) :
    leEv (distSq (translate n p) (translate n q)) (distSq p q) := by
  have h := timeState_contraction n (presentationSubtract p q)
  rw [timeState_subtract, completedInner_embedPresentation] at h
  change RCle (completedDist (timeState n p) (timeState n q)) (Quotient.mk crealSetoid (distSq p q)) at h
  rw [timeState_pin, timeState_pin, completedDist_embedPresentation] at h
  exact h

/-- Exact nonexpansiveness retains every supplied Cauchy/closeness modulus. -/
def timeNonexpansive (n : Nat) : seminorm.Nonexpansive where
  toFun := translate n
  contraction := distSq_translate n

end YMGap.Continuum.BF4ExactSlabThermodynamicTimeContraction

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeContraction.pairing_midpoint_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeContraction.timeNorm
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeContraction.timeNormCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeContraction.timeNorm_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeContraction.timeNorm_midpoint
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeContraction.timeNorm_le_anchor
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeContraction.timeState_contraction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeContraction.denseTime_contraction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeContraction.distSq_translate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeContraction.timeNonexpansive
