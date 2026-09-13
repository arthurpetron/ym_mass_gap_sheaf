/-
# Explicit-modulus completion carrier for the ORIGINAL thermodynamic OS form

The squared distance is the constructed original common-base form of a
difference. Its real representative and QCauchy data remain on concrete
presentations. The proved semantic OS geometry supplies the sqrt-free
triangle and radical laws, hence the existing SquaredSeminorm completion.

Both semantic observables and the positive-definite OS quotient embed
without representative selection; the latter embedding is injective.
The completed unit is not zero. This constructs the completion carrier,
not its completed inner product, full quotient-level completeness, physical
time/vacuum/gap, observable actions, or a continuum theory.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient
import YMGap.Continuum.CRealSeminormCompletion

namespace YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_add_zero_eqv (A.approx n)))

private theorem rc_distance_symm (a b c : RC) :
    RCsub (RCsub a b) (RCsub b c) = RCsub (RCsub c b) (RCsub b a) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.add (.var 0) (.neg (.var 1))) (.neg (.add (.var 1) (.neg (.var 2)))))
    (.add (.add (.var 2) (.neg (.var 1))) (.neg (.add (.var 1) (.neg (.var 0)))))
    (by decide) (fun | 0 => A.approx n | 1 => B.approx n | _ => C.approx n)

private theorem rc_parallelogram (a b c : RC) :
    RCadd (RCadd (RCadd a b) (RCadd b c)) (RCsub (RCsub a b) (RCsub b c)) =
      RCadd (RCadd a a) (RCadd c c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.add (.add (.var 0) (.var 1)) (.add (.var 1) (.var 2)))
      (.add (.add (.var 0) (.neg (.var 1))) (.neg (.add (.var 1) (.neg (.var 2))))))
    (.add (.add (.var 0) (.var 0)) (.add (.var 2) (.var 2)))
    (by decide) (fun | 0 => A.approx n | 1 => B.approx n | _ => C.approx n)

theorem subtract_add_sub (x y z : Observable) :
    qadd (subtract x y) (subtract y z) = subtract x z := by
  unfold subtract
  rw [qadd_assoc x (qsmul (-1) y) (qadd y (qsmul (-1) z)),
    ← qadd_assoc (qsmul (-1) y) y (qsmul (-1) z), neg_add, zero_add]

theorem pairing_add_bound (x y : Observable) :
    RCle (pairing (qadd x y) (qadd x y))
      (RCadd (RCadd (pairing x x) (pairing x x)) (RCadd (pairing y y) (pairing y y))) := by
  have h := RCadd_le_add (RCle_refl (pairing (qadd x y) (qadd x y)))
    (pairing_nonnegative (subtract x y))
  rw [rc_add_zero] at h
  rw [pairing_add_left, pairing_add_right, pairing_add_right,
    RCBilinearDifference.difference_diagonal subtract pairing pairing_sub_left pairing_symm x y,
    pairing_symm y x, rc_parallelogram] at h
  rw [pairing_add_left, pairing_add_right, pairing_add_right, pairing_symm y x]
  exact h

def presentationSubtract (p q : Presentation) : Presentation := add p (smul (-1) q)

theorem embed_subtract (p q : Presentation) :
    embed (presentationSubtract p q) = subtract (embed p) (embed q) := rfl

def distSq (p q : Presentation) : CReal :=
  presentedForm (presentationSubtract p q) (presentationSubtract p q)

def distSqCauchy (p q : Presentation) : QCauchy (distSq p q).approx :=
  presentedFormCauchy (presentationSubtract p q) (presentationSubtract p q)

theorem distSq_pin (p q : Presentation) :
    Quotient.mk crealSetoid (distSq p q) = pairing (subtract (embed p) (embed q)) (subtract (embed p) (embed q)) :=
  (pairing_embed (presentationSubtract p q) (presentationSubtract p q)).symm

theorem distSq_null_iff (p q : Presentation) : Equiv (distSq p q) czero ↔ Null (embed p) (embed q) := by
  constructor
  · intro h
    change pairing (subtract (embed p) (embed q)) (subtract (embed p) (embed q)) = RCzero
    rw [← distSq_pin]
    exact Quotient.sound h
  · intro h
    apply Quotient.exact (s := crealSetoid)
    rw [distSq_pin]
    exact h

theorem distSq_refl (p : Presentation) : Equiv (distSq p p) czero :=
  (distSq_null_iff p p).mpr ((null_iff_pairing (embed p) (embed p)).mpr (fun _ => rfl))

theorem distSq_symm (p q : Presentation) : Equiv (distSq p q) (distSq q p) := by
  apply Quotient.exact (s := crealSetoid)
  rw [distSq_pin, distSq_pin,
    RCBilinearDifference.difference_diagonal subtract pairing pairing_sub_left pairing_symm (embed p) (embed q),
    RCBilinearDifference.difference_diagonal subtract pairing pairing_sub_left pairing_symm (embed q) (embed p),
    pairing_symm (embed q) (embed p)]
  exact rc_distance_symm _ _ _

theorem distSq_nonnegative (p q : Presentation) : leEv czero (distSq p q) := by
  change RCnonneg (Quotient.mk crealSetoid (distSq p q))
  rw [distSq_pin]
  exact pairing_nonnegative _

theorem distSq_triangle (p q r : Presentation) :
    leEv (distSq p r)
      (CReal.add (CReal.add (distSq p q) (distSq p q)) (CReal.add (distSq q r) (distSq q r))) := by
  change RCle (Quotient.mk crealSetoid (distSq p r))
    (RCadd (RCadd (Quotient.mk crealSetoid (distSq p q)) (Quotient.mk crealSetoid (distSq p q)))
      (RCadd (Quotient.mk crealSetoid (distSq q r)) (Quotient.mk crealSetoid (distSq q r))))
  rw [distSq_pin, distSq_pin, distSq_pin]
  have h := pairing_add_bound (subtract (embed p) (embed q)) (subtract (embed q) (embed r))
  rw [subtract_add_sub] at h
  exact h

theorem distSq_null_congr {p p' q q' : Presentation}
    (hp : Equiv (distSq p p') czero) (hq : Equiv (distSq q q') czero) :
    Equiv (distSq p q) (distSq p' q') := by
  have hp' := (distSq_null_iff p p').mp hp
  have hq' := (distSq_null_iff q q').mp hq
  have hs : Null (subtract (embed p) (embed q)) (subtract (embed p') (embed q')) :=
    null_add hp' (null_smul (-1) hq')
  apply Quotient.exact (s := crealSetoid)
  rw [distSq_pin, distSq_pin]
  exact pairing_null_congr hs hs

def seminorm : SquaredSeminorm where
  Carrier := Presentation
  distSq := distSq
  distSq_refl := distSq_refl
  distSq_symm := distSq_symm
  distSq_nonneg := distSq_nonnegative
  distSq_triangle := distSq_triangle
  null_congr := distSq_null_congr

def Completion : Type := seminorm.Completion

def embedPresentation (p : Presentation) : Completion := seminorm.embedRep p

def embedObservable : Observable → Completion :=
  Quotient.lift embedPresentation (fun p q h =>
    seminorm.embedRep_eq_of_null ((distSq_null_iff p q).mpr
      ((null_iff_pairing (embed p) (embed q)).mpr
        (fun z => congrArg (fun x => pairing x z) (Quotient.sound h)))))

theorem embedObservable_embed (p : Presentation) : embedObservable (embed p) = embedPresentation p := rfl

theorem embedObservable_of_null (x y : Observable) (h : Null x y) : embedObservable x = embedObservable y := by
  revert h
  refine Quotient.inductionOn₂ x y ?_
  intro p q h
  exact seminorm.embedRep_eq_of_null ((distSq_null_iff p q).mpr h)

def embedOSQuotient : Carrier → Completion :=
  Quotient.lift embedObservable (fun x y h => embedObservable_of_null x y h)

theorem embedOSQuotient_project (x : Observable) : embedOSQuotient (project x) = embedObservable x := rfl

theorem embedPresentation_eq_iff (p q : Presentation) :
    embedPresentation p = embedPresentation q ↔ Null (embed p) (embed q) := by
  constructor
  · intro h
    rcases Quotient.exact h with ⟨hc⟩
    have hu : leEv (distSq p q) czero := by
      intro epsilon he
      have hh := ExpNeg.half_mul_pos epsilon he
      have hd := hc.close (HalfPow.half * epsilon) hh (hc.modulus (HalfPow.half * epsilon)) (Nat.le_refl _)
      obtain ⟨N, hN⟩ := hd (HalfPow.half * epsilon) hh
      refine ⟨N, fun n hn => ?_⟩
      exact Q'.le_trans' _ _ _ (hN n hn)
        (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (ExpNeg.two_halves epsilon)
          (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' epsilon)))))
    exact (distSq_null_iff p q).mp (equiv_of_leEv_leEv hu (distSq_nonnegative p q))
  · intro h
    exact seminorm.embedRep_eq_of_null ((distSq_null_iff p q).mpr h)

theorem embedObservable_eq_iff (x y : Observable) : embedObservable x = embedObservable y ↔ Null x y := by
  refine Quotient.inductionOn₂ x y ?_
  exact embedPresentation_eq_iff

theorem embedOSQuotient_injective (x y : Carrier) (h : embedOSQuotient x = embedOSQuotient y) : x=y := by
  revert h
  refine Quotient.inductionOn₂ x y ?_
  intro a b h
  exact Quotient.sound ((embedObservable_eq_iff a b).mp h)

def completedUnit : Completion := embedOSQuotient osUnit

def completedZero : Completion := embedOSQuotient osZero

theorem completedUnit_ne_zero : completedUnit ≠ completedZero := by
  intro h
  exact osUnit_ne_zero (embedOSQuotient_injective osUnit osZero h)

end YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion.subtract_add_sub
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion.pairing_add_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion.presentationSubtract
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion.embed_subtract
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion.distSq
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion.distSqCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion.distSq_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion.distSq_null_iff
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion.distSq_refl
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion.distSq_symm
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion.distSq_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion.distSq_triangle
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion.distSq_null_congr
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion.seminorm
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion.Completion
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion.embedPresentation
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion.embedObservable
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion.embedObservable_embed
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion.embedObservable_of_null
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion.embedOSQuotient
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion.embedOSQuotient_project
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion.embedPresentation_eq_iff
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion.embedObservable_eq_iff
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion.embedOSQuotient_injective
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion.completedUnit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion.completedZero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion.completedUnit_ne_zero
