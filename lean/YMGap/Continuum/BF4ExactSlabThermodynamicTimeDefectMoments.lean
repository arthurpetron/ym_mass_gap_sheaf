/-
# Positive mixed moments of the ORIGINAL transfer and its defect

For the existing geometric two-step transfer T and D=I-T, construct every
mixed moment <x,T^k D^l x>. Symmetry moves T's half-time and pairs of D
factors onto the vector. The remaining form is either a squared norm or
the original one-step contraction defect. Thus all mixed moments are
nonnegative, without a spectral-resolution input. The exact splitting
m(k,l)=m(k+1,l)+m(k,l+1) is proved on the SAME completion.

For supplied Cauchy representatives, all transformed representatives,
moment reals and QCauchy moduli are returned by explicit constructions.
This is fixed-nome, fixed-spacing SU(2) operator/moment algebra, not a
spectral measure, continuous-time generator, continuum limit or Clay closure.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicResolventBound

namespace YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicRelaxation
open YMGap.Continuum.BF4ExactSlabThermodynamicResolvent (defect)

local notation "B" => completedInner
local notation "S" => seminorm

theorem sub_nonnegative (a b : RC) (h : RCle b a) : RCnonneg (RCsub a b) := by
  revert h
  refine Quotient.inductionOn₂ a b ?_
  intro A C h epsilon he
  obtain ⟨N,hN⟩ := h epsilon he
  refine ⟨N,fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _ (Q'.sub_nonneg_of_le (hN n hn))
    (Q'.le_of_eqv (RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 2)))
      (.add (.add (.var 0) (.neg (.var 2))) (.var 1)) (by decide)
      (fun | 0 => A.approx n | 1 => epsilon | _ => C.approx n)))

theorem defect_symmetric (x y : Completion) : B (defect x) y=B x (defect y) := by
  unfold defect
  rw [completedInner_sub_left,completedInner_sub_right,twoStepTransfer_symmetric]

theorem defect_positive (x : Completion) : RCnonneg (B x (defect x)) := by
  unfold defect
  rw [completedInner_sub_right]
  apply sub_nonnegative
  change RCle (B x (completedTime (1+1) x)) (B x x)
  rw [← completedTime_moments]
  exact completedTime_contraction 1 x

theorem time_defect (n : Nat) (x : Completion) :
    completedTime n (defect x)=defect (completedTime n x) := by
  unfold defect twoStepTransfer
  rw [completedTime_sub,completedTime_comp,completedTime_comp,Nat.add_comm 2 n]

def defectPower : Nat → Completion → Completion
  | 0,x => x
  | n+1,x => defect (defectPower n x)

theorem defectPower_defect (n : Nat) (x : Completion) :
    defectPower n (defect x)=defect (defectPower n x) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg defect ih

theorem defectPower_symmetric (n : Nat) (x y : Completion) :
    B (defectPower n x) y=B x (defectPower n y) := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih =>
      change B (defect (defectPower n x)) y=B x (defect (defectPower n y))
      rw [defect_symmetric,ih,defectPower_defect]

theorem defectPower_positive : ∀ (n : Nat) (x : Completion), RCnonneg (B x (defectPower n x))
  | 0,x => completedInner_nonnegative x
  | 1,x => defect_positive x
  | n+2,x => by
      change RCnonneg (B x (defect (defect (defectPower n x))))
      rw [← defect_symmetric,← defectPower_defect]
      exact defectPower_positive n (defect x)

theorem time_defectPower (n l : Nat) (x : Completion) :
    completedTime n (defectPower l x)=defectPower l (completedTime n x) := by
  induction l with
  | zero => rfl
  | succ l ih =>
      change completedTime n (defect (defectPower l x))=defect (defectPower l (completedTime n x))
      rw [time_defect,ih]

/-- Actual operator moments, not freely assigned scalar spectral data. -/
def mixedMoment (x : Completion) (k l : Nat) : RC :=
  B x (completedTime (k+k) (defectPower l x))

theorem mixedMoment_halfTime (x : Completion) (k l : Nat) :
    mixedMoment x k l=B (completedTime k x) (defectPower l (completedTime k x)) := by
  rw [← time_defectPower,completedTime_moments]
  rfl

theorem mixedMoment_nonnegative (x : Completion) (k l : Nat) : RCnonneg (mixedMoment x k l) := by
  rw [mixedMoment_halfTime]
  exact defectPower_positive l (completedTime k x)

theorem mixedMoment_zero (x : Completion) : mixedMoment x 0 0=B x x := by
  change B x (completedTime 0 x)=B x x
  rw [completedTime_zero]

theorem mixedMoment_split (x : Completion) (k l : Nat) :
    mixedMoment x k l=RCadd (mixedMoment x (k+1) l) (mixedMoment x k (l+1)) := by
  have h := completedSub_add_cancel (defectPower l x) (twoStepTransfer (defectPower l x))
  change completedAdd (defectPower (l+1) x) (twoStepTransfer (defectPower l x))=defectPower l x at h
  rw [completedAdd_comm] at h
  have ht := congrArg (fun y => B x (completedTime (k+k) y)) h
  dsimp only at ht
  rw [completedTime_add,completedInner_add_right] at ht
  change RCadd (B x (completedTime (k+k) (completedTime 2 (defectPower l x))))
    (mixedMoment x k (l+1))=mixedMoment x k l at ht
  rw [completedTime_comp,show 2+(k+k)=(k+1)+(k+1) by omega] at ht
  exact ht.symm

def defectCauchy (X : (S).Cauchy) : (S).Cauchy := differenceCauchy X (timeCauchy 2 X)

theorem defect_mk (X : (S).Cauchy) :
    defect (Quotient.mk (S).completionSetoid X)=Quotient.mk (S).completionSetoid (defectCauchy X) := rfl

def defectPowerCauchy : Nat → (S).Cauchy → (S).Cauchy
  | 0,X => X
  | l+1,X => defectCauchy (defectPowerCauchy l X)

theorem defectPower_mk (l : Nat) (X : (S).Cauchy) :
    defectPower l (Quotient.mk (S).completionSetoid X)=
      Quotient.mk (S).completionSetoid (defectPowerCauchy l X) := by
  induction l with
  | zero => rfl
  | succ l ih => change defect (defectPower l (Quotient.mk (S).completionSetoid X))=_; rw [ih]; rfl

def momentRepresentative (X : (S).Cauchy) (k l : Nat) : CReal :=
  representativeInner X (timeCauchy (k+k) (defectPowerCauchy l X))

def momentCauchy (X : (S).Cauchy) (k l : Nat) : QCauchy (momentRepresentative X k l).approx :=
  representativeInnerCauchy X (timeCauchy (k+k) (defectPowerCauchy l X))

theorem moment_pin (X : (S).Cauchy) (k l : Nat) :
    mixedMoment (Quotient.mk (S).completionSetoid X) k l=
      Quotient.mk crealSetoid (momentRepresentative X k l) := by
  unfold mixedMoment
  rw [defectPower_mk]
  rfl

def momentCertificate (X : (S).Cauchy) (k l : Nat) :
    Σ' r : CReal, QCauchy r.approx ×'
      (mixedMoment (Quotient.mk (S).completionSetoid X) k l=Quotient.mk crealSetoid r) ×'
      leEv czero r :=
  ⟨momentRepresentative X k l,momentCauchy X k l,moment_pin X k l,by
    have h := mixedMoment_nonnegative (Quotient.mk (S).completionSetoid X) k l
    rw [moment_pin] at h
    exact h⟩

end YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments.sub_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments.defect_symmetric
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments.defect_positive
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments.time_defect
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments.defectPower
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments.defectPower_defect
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments.defectPower_symmetric
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments.defectPower_positive
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments.time_defectPower
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments.mixedMoment
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments.mixedMoment_halfTime
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments.mixedMoment_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments.mixedMoment_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments.mixedMoment_split
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments.defectCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments.defect_mk
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments.defectPowerCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments.defectPower_mk
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments.momentRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments.momentCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments.moment_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments.momentCertificate
