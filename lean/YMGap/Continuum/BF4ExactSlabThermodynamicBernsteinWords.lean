/-
# Finite Bernstein weights for the SAME original transfer

Length-n binary words index the uncoalesced Bernstein expansion: a word
with k time factors and l defect factors has weight <x,T^k (I-T)^l x>,
k+l=n. This finite representation retains repeated grid nodes; it does
not postulate spectral points or eigenvectors. Every weight is positive
in the non-strict sense, total mass is exactly ||x||^2, and the weighted
time count is n*<x,T x>. All are identities of the actual original operator.

These finite weights are not yet a limiting spectral measure or a
continuous-time construction. SU(2) nome and spacing remain fixed.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments

namespace YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinWords

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments

/-- A finite binary-word carrier; no real equality or choice is involved. -/
def Word : Nat → Type
  | 0 => Unit
  | n+1 => Bool × Word n

def timeCount : {n : Nat} → Word n → Nat
  | 0,_ => 0
  | _+1,(true,p) => timeCount p+1
  | _+1,(false,p) => timeCount p

def defectCount : {n : Nat} → Word n → Nat
  | 0,_ => 0
  | _+1,(true,p) => defectCount p
  | _+1,(false,p) => defectCount p+1

theorem counts_sum : {n : Nat} → (p : Word n) → timeCount p+defectCount p=n
  | 0,_ => rfl
  | n+1,(true,p) => by have h := counts_sum p; change (timeCount p+1)+defectCount p=n+1; omega
  | n+1,(false,p) => by have h := counts_sum p; change timeCount p+(defectCount p+1)=n+1; omega

def wordSum : (n : Nat) → (Word n → RC) → RC
  | 0,f => f ()
  | n+1,f => RCadd (wordSum n (fun p => f (true,p))) (wordSum n (fun p => f (false,p)))

theorem add_comm (a b : RC) : RCadd a b=RCadd b a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.add_comm_eqv (A.approx n) (B.approx n)))

theorem add_assoc (a b c : RC) : RCadd (RCadd a b) c=RCadd a (RCadd b c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.add_assoc_eqv (A.approx n) (B.approx n) (C.approx n)))

theorem add_regroup (a b c d : RC) :
    RCadd (RCadd a b) (RCadd c d)=RCadd (RCadd a c) (RCadd b d) := by
  rw [add_assoc,← add_assoc b c d,add_comm b c,add_assoc c b d,← add_assoc]

theorem wordSum_add (n : Nat) (f g : Word n → RC) :
    wordSum n (fun p => RCadd (f p) (g p))=RCadd (wordSum n f) (wordSum n g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change RCadd (wordSum n (fun p => RCadd (f (true,p)) (g (true,p))))
        (wordSum n (fun p => RCadd (f (false,p)) (g (false,p))))=_
      rw [ih,ih]
      exact add_regroup _ _ _ _

theorem wordSum_scale (n : Nat) (a : Q') (f : Word n → RC) :
    wordSum n (fun p => RCscale a (f p))=RCscale a (wordSum n f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change RCadd (wordSum n (fun p => RCscale a (f (true,p))))
        (wordSum n (fun p => RCscale a (f (false,p))))=_
      rw [ih,ih,← RCscale_RCadd]
      rfl

theorem wordSum_nonnegative (n : Nat) (f : Word n → RC) (h : ∀ p,RCnonneg (f p)) :
    RCnonneg (wordSum n f) := by
  induction n with
  | zero => exact h ()
  | succ n ih => exact RCadd_le_add (ih _ (fun p => h (true,p))) (ih _ (fun p => h (false,p)))

def wordMoment (x : Completion) (k l : Nat) {n : Nat} (p : Word n) : RC :=
  mixedMoment x (k+timeCount p) (l+defectCount p)

theorem wordMoment_time (x : Completion) (k l : Nat) {n : Nat} (p : Word n) :
    wordMoment x k l (n:=n+1) (true,p)=wordMoment x (k+1) l p := by
  change mixedMoment x (k+(timeCount p+1)) (l+defectCount p)=
    mixedMoment x ((k+1)+timeCount p) (l+defectCount p)
  rw [show k+(timeCount p+1)=(k+1)+timeCount p by omega]

theorem wordMoment_defect (x : Completion) (k l : Nat) {n : Nat} (p : Word n) :
    wordMoment x k l (n:=n+1) (false,p)=wordMoment x k (l+1) p := by
  change mixedMoment x (k+timeCount p) (l+(defectCount p+1))=
    mixedMoment x (k+timeCount p) ((l+1)+defectCount p)
  rw [show l+(defectCount p+1)=(l+1)+defectCount p by omega]

theorem wordMoment_mass (x : Completion) (n k l : Nat) :
    wordSum n (wordMoment x k l)=mixedMoment x k l := by
  induction n generalizing k l with
  | zero => rfl
  | succ n ih =>
      change RCadd (wordSum n (fun p => wordMoment x k l (n:=n+1) (true,p)))
        (wordSum n (fun p => wordMoment x k l (n:=n+1) (false,p)))=_
      simp only [wordMoment_time,wordMoment_defect,ih]
      exact (mixedMoment_split x k l).symm

theorem weight_nonnegative (x : Completion) {n : Nat} (p : Word n) :
    RCnonneg (wordMoment x 0 0 p) := mixedMoment_nonnegative x _ _

theorem weights_total (x : Completion) (n : Nat) :
    wordSum n (wordMoment x 0 0)=completedInner x x :=
  (wordMoment_mass x n 0 0).trans (mixedMoment_zero x)

theorem scale_nat_succ (n : Nat) (a : RC) :
    RCscale (Q'.ofNat (n+1)) a=RCadd (RCscale (Q'.ofNat n) a) a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun j =>
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.ofNat_add_eqv n 1))
      (Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _)
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv (A.approx j))))))

theorem weighted_time_count (x : Completion) (n k l : Nat) :
    wordSum n (fun p => RCscale (Q'.ofNat (timeCount p)) (wordMoment x k l p))=
      RCscale (Q'.ofNat n) (mixedMoment x (k+1) l) := by
  induction n generalizing k l with
  | zero =>
      change RCscale 0 (mixedMoment x k l)=RCscale 0 (mixedMoment x (k+1) l)
      refine Quotient.inductionOn₂ (mixedMoment x k l) (mixedMoment x (k+1) l) ?_
      intro A C
      exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun j =>
        Q'.eqv_trans _ _ _ (QPoly.q_zero_mul (A.approx j)) (Q'.eqv_symm (QPoly.q_zero_mul (C.approx j)))))
  | succ n ih =>
      change RCadd
        (wordSum n (fun p => RCscale (Q'.ofNat (timeCount p+1)) (wordMoment x k l (n:=n+1) (true,p))))
        (wordSum n (fun p => RCscale (Q'.ofNat (timeCount p)) (wordMoment x k l (n:=n+1) (false,p))))=_
      simp only [wordMoment_time,wordMoment_defect,scale_nat_succ,wordSum_add,ih,wordMoment_mass]
      rw [add_assoc,add_comm (mixedMoment x (k+1) l),← add_assoc,← RCscale_RCadd,
        ← mixedMoment_split]

end YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinWords

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinWords.Word
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinWords.timeCount
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinWords.defectCount
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinWords.counts_sum
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinWords.wordSum
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinWords.add_comm
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinWords.add_assoc
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinWords.add_regroup
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinWords.wordSum_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinWords.wordSum_scale
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinWords.wordSum_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinWords.wordMoment
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinWords.wordMoment_time
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinWords.wordMoment_defect
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinWords.wordMoment_mass
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinWords.weight_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinWords.weights_total
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinWords.scale_nat_succ
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinWords.weighted_time_count
