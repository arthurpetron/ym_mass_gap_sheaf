/-
# Mixed time-defect moments of the actual all-nome Wilson completion

The original completed one-step time operator is positive, symmetric, and
contractive.  Its defect `D = I - T` is positive; so is the commuting product
`T D`.  Elementary parity peeling consequently makes every mixed moment
`B(x,T^k D^l x)` nonnegative.  The moments obey the exact binomial split.

This is a fixed-width, fixed-nome Hausdorff-moment inequality on the existing
literal Wilson carrier.  It does not construct a spectral measure, prove
injectivity of time, or assert changing-width/scaling control.
-/

import YMGap.Continuum.BF4WilsonAllNomeTimeDifference
import YMGap.Continuum.RCScaleClose

namespace YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeTimeDifference

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound
    (SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_add_zero_eqv _))

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound
    (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      Q'.eqv_of_eq (Q'.zero_add' (A.approx n))))

private theorem rc_sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound
    (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.add_neg_self_eqv _))

private theorem rc_sub_nonnegative_of_le {a b : RC} (h : RCle b a) :
    RCnonneg (RCsub a b) := by
  have h' := RCadd_le_add h (RCle_refl (RCneg b))
  change RCle (RCsub b b) (RCsub a b) at h'
  rwa [rc_sub_self] at h'

private theorem rc_negative_one (a : RC) : RCscale (-1) a = RCneg a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 (A.approx n))
      (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv (A.approx n)))))

private theorem inner_sub_left (x y z : V) :
    B (completedSub hw0 hw1 x y) z = RCsub (B x z) (B y z) := by
  unfold completedSub completedNeg RCsub
  rw [completedInner_add_left, completedInner_smul_left, rc_negative_one]

private theorem inner_sub_right (x y z : V) :
    B x (completedSub hw0 hw1 y z) = RCsub (B x y) (B x z) := by
  rw [completedInner_symm hw0 hw1 x, inner_sub_left,
    completedInner_symm hw0 hw1 y x, completedInner_symm hw0 hw1 z x]

private theorem midpoint_cancel (a b c : RC) :
    RCadd (RCadd b b) (RCsub (RCsub a b) (RCsub b c)) = RCadd a c := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B' C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 1) (.var 1))
        (.add (.add (.var 0) (.neg (.var 1)))
          (.neg (.add (.var 1) (.neg (.var 2))))))
      (.add (.var 0) (.var 2)) (by decide)
      (fun | 0 => A.approx n | 1 => B'.approx n | _ => C.approx n)))

private theorem half_double (a : RC) :
    RCscale HalfPow.half (RCadd a a) = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.mul_add_eqv HalfPow.half (A.approx n) (A.approx n))
      (ExpNeg.two_halves (A.approx n))))

private theorem rc_cancel_defect (a b c : RC) :
    RCadd (RCsub (RCsub a b) (RCsub b c)) (RCsub b c) = RCsub a b := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B' C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.add (.var 0) (.neg (.var 1)))
          (.neg (.add (.var 1) (.neg (.var 2)))))
        (.add (.var 1) (.neg (.var 2))))
      (.add (.var 0) (.neg (.var 1))) (by decide)
      (fun | 0 => A.approx n | 1 => B'.approx n | _ => C.approx n)))

private theorem rc_add_sub_cancel (a b : RC) :
    RCadd b (RCsub a b) = a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.var 1) (.add (.var 0) (.neg (.var 1))))
      (.var 0) (by decide)
      (fun | 0 => A.approx n | _ => B'.approx n)))

/-- The time form is bounded above by its original completed norm form. -/
theorem completedTime_form_le (n : Nat) (x : V) :
    RCle (B x (T n x)) (B x x) := by
  have h := RCadd_le_add
    (RCle_refl (RCadd (B x (T n x)) (B x (T n x))))
    (completedInner_nonnegative hw0 hw1
      (completedSub hw0 hw1 x (T n x)))
  rw [rc_add_zero, inner_sub_left, inner_sub_right, inner_sub_right,
    completedInner_symm hw0 hw1 (T n x) x, midpoint_cancel] at h
  have hdouble := RCle_trans h (RCadd_le_add (RCle_refl (B x x))
    (completedInner_time_contraction hw0 hw1 n x))
  have hhalf := RCscale_mono (by decide : (0 : Q') ≤ HalfPow.half) hdouble
  simpa only [half_double] using hhalf

/-- The actual defect of one step of completed physical time. -/
def defect (x : V) : V := completedSub hw0 hw1 x (T 1 x)

theorem defect_symmetric (x y : V) :
    B (defect hw0 hw1 x) y = B x (defect hw0 hw1 y) := by
  unfold defect
  rw [inner_sub_left, inner_sub_right, completedInner_time_balance]

theorem defect_time (n : Nat) (x : V) :
    defect hw0 hw1 (T n x) = T n (defect hw0 hw1 x) := by
  unfold defect
  rw [completedTime_sub, ← completedTime_add, ← completedTime_add]
  exact congrArg (fun m => completedSub hw0 hw1 (T n x) (T m x))
    (show 1+n = n+1 by omega)

theorem time_add_defect (x : V) :
    completedAdd hw0 hw1 (T 1 x) (defect hw0 hw1 x) = x := by
  unfold defect completedSub
  calc
    completedAdd hw0 hw1 (T 1 x)
        (completedAdd hw0 hw1 x (completedNeg hw0 hw1 (T 1 x))) =
      completedAdd hw0 hw1 x
        (completedAdd hw0 hw1 (T 1 x) (completedNeg hw0 hw1 (T 1 x))) := by
          rw [← completedAdd_assoc, completedAdd_comm hw0 hw1 (T 1 x) x,
            completedAdd_assoc]
    _ = completedAdd hw0 hw1 x (completedZero hw0 hw1 width) := by
      rw [completedAdd_comm hw0 hw1 (T 1 x) (completedNeg hw0 hw1 (T 1 x)),
        completedNeg_add]
    _ = x := completedAdd_zero hw0 hw1 x

/-- The completed quadratic form of `I-T` is nonnegative. -/
theorem defect_nonnegative (x : V) :
    RCnonneg (B x (defect hw0 hw1 x)) := by
  rw [defect, inner_sub_right]
  exact rc_sub_nonnegative_of_le (completedTime_form_le hw0 hw1 1 x)

/-- The completed quadratic form of the commuting product `T(I-T)` is
nonnegative.  This uses only the positive one-step form and its upper bound. -/
theorem time_defect_nonnegative (x : V) :
    RCnonneg (B x (T 1 (defect hw0 hw1 x))) := by
  let y := T 1 x
  let z := defect hw0 hw1 x
  have hq := completedInner_oneStep_nonnegative hw0 hw1 z
  have hqeq : B z (T 1 z) =
      RCsub (RCsub (B x y) (B y y))
        (RCsub (B y y) (B y (T 1 y))) := by
    dsimp only [z, defect, y]
    rw [completedTime_sub, inner_sub_left, inner_sub_right, inner_sub_right]
    rw [← completedInner_time_balance hw0 hw1 1 x (T 1 x)]
  rw [hqeq] at hq
  have hrem : RCnonneg (RCsub (B y y) (B y (T 1 y))) :=
    rc_sub_nonnegative_of_le (completedTime_form_le hw0 hw1 1 y)
  have hsum := RCadd_le_add hq hrem
  rw [rc_add_zero, rc_cancel_defect] at hsum
  have htarget : B x (T 1 (defect hw0 hw1 x)) =
      RCsub (B x y) (B y y) := by
    rw [defect, completedTime_sub, inner_sub_right]
    exact congrArg (RCsub (B x (T 1 x)))
      (completedInner_time_balance hw0 hw1 1 x y).symm
  rw [htarget]
  exact hsum

/-- Constructive powers of the actual time defect, with no quotient choice. -/
def defectPower : Nat → V → V
  | 0, x => x
  | n+1, x => defect hw0 hw1 (defectPower n x)

theorem defectPower_succ_right (n : Nat) (x : V) :
    defectPower hw0 hw1 (n+1) x =
      defectPower hw0 hw1 n (defect hw0 hw1 x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change defect hw0 hw1 (defectPower hw0 hw1 (n+1) x) =
        defect hw0 hw1 (defectPower hw0 hw1 n (defect hw0 hw1 x))
      exact congrArg (defect hw0 hw1) ih

theorem defectPower_add (m n : Nat) (x : V) :
    defectPower hw0 hw1 (m+n) x =
      defectPower hw0 hw1 m (defectPower hw0 hw1 n x) := by
  induction m with
  | zero => simp only [Nat.zero_add, defectPower]
  | succ m ih =>
      rw [Nat.succ_add]
      change defect hw0 hw1 (defectPower hw0 hw1 (m+n) x) =
        defect hw0 hw1
          (defectPower hw0 hw1 m (defectPower hw0 hw1 n x))
      exact congrArg (defect hw0 hw1) ih

theorem defectPower_symmetric (n : Nat) (x y : V) :
    B (defectPower hw0 hw1 n x) y =
      B x (defectPower hw0 hw1 n y) := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih =>
      change B (defect hw0 hw1 (defectPower hw0 hw1 n x)) y =
        B x (defect hw0 hw1 (defectPower hw0 hw1 n y))
      calc
        B (defect hw0 hw1 (defectPower hw0 hw1 n x)) y =
            B (defectPower hw0 hw1 n x) (defect hw0 hw1 y) :=
              defect_symmetric hw0 hw1 _ _
        _ = B x (defectPower hw0 hw1 n (defect hw0 hw1 y)) :=
          ih x (defect hw0 hw1 y)
        _ = B x (defect hw0 hw1 (defectPower hw0 hw1 n y)) := by
          exact congrArg (B x) (defectPower_succ_right hw0 hw1 n y).symm

theorem time_defectPower (n k : Nat) (x : V) :
    T k (defectPower hw0 hw1 n x) =
      defectPower hw0 hw1 n (T k x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      change T k (defect hw0 hw1 (defectPower hw0 hw1 n x)) =
        defect hw0 hw1 (defectPower hw0 hw1 n (T k x))
      rw [← defect_time, ih]

/-- The original pairing with a time power and a defect power. -/
def mixedMoment (x : V) (k l : Nat) : RC :=
  B x (T k (defectPower hw0 hw1 l x))

theorem mixedMoment_zero (x : V) :
    mixedMoment hw0 hw1 x 0 0 = B x x := by
  simp only [mixedMoment, defectPower, completedTime_zero]

private theorem mixedMoment_time_two (x : V) (k l : Nat) :
    mixedMoment hw0 hw1 x (k+2) l =
      mixedMoment hw0 hw1 (T 1 x) k l := by
  unfold mixedMoment
  have ht : T (k+2) (defectPower hw0 hw1 l x) =
      T 1 (T k (T 1 (defectPower hw0 hw1 l x))) := by
    rw [← completedTime_add, ← completedTime_add]
    congr 1
    omega
  rw [ht, ← completedInner_time_balance hw0 hw1 1 x
    (T k (T 1 (defectPower hw0 hw1 l x))),
    time_defectPower hw0 hw1 l 1 x]

private theorem mixedMoment_defect_two (x : V) (k l : Nat) :
    mixedMoment hw0 hw1 x k (l+2) =
      mixedMoment hw0 hw1 (defect hw0 hw1 x) k l := by
  unfold mixedMoment
  calc
    B x (T k (defectPower hw0 hw1 (l+2) x)) =
        B x (T k (defect hw0 hw1
          (defectPower hw0 hw1 l (defect hw0 hw1 x)))) := by
            rw [show l+2 = (l+1)+1 by omega,
              defectPower_succ_right]
            rfl
    _ = B x (defect hw0 hw1
          (T k (defectPower hw0 hw1 l (defect hw0 hw1 x)))) := by
            rw [← defect_time]
    _ = B (defect hw0 hw1 x)
          (T k (defectPower hw0 hw1 l (defect hw0 hw1 x))) :=
            (defect_symmetric hw0 hw1 x _).symm

private theorem mixedMoment_zero_time_nonnegative (l : Nat) :
    ∀ x : V, RCnonneg (mixedMoment hw0 hw1 x 0 l) := by
  induction l using Nat.strongRecOn with
  | ind l ih =>
      intro x
      cases l with
      | zero =>
          rw [mixedMoment_zero]
          exact completedInner_nonnegative hw0 hw1 x
      | succ l =>
          cases l with
          | zero =>
              simpa only [mixedMoment, defectPower, completedTime_zero] using
                defect_nonnegative hw0 hw1 x
          | succ l =>
              rw [show l+1+1 = l+2 by omega,
                mixedMoment_defect_two]
              exact ih l (by omega) (defect hw0 hw1 x)

private theorem mixedMoment_one_time_nonnegative (l : Nat) :
    ∀ x : V, RCnonneg (mixedMoment hw0 hw1 x 1 l) := by
  induction l using Nat.strongRecOn with
  | ind l ih =>
      intro x
      cases l with
      | zero =>
          change RCnonneg (B x (T 1 x))
          exact completedInner_oneStep_nonnegative hw0 hw1 x
      | succ l =>
          cases l with
          | zero =>
              change RCnonneg (B x (T 1 (defect hw0 hw1 x)))
              exact time_defect_nonnegative hw0 hw1 x
          | succ l =>
              rw [show l+1+1 = l+2 by omega,
                mixedMoment_defect_two]
              exact ih l (by omega) (defect hw0 hw1 x)

private theorem mixedMoment_nonnegative_aux (k : Nat) :
    ∀ (x : V) (l : Nat), RCnonneg (mixedMoment hw0 hw1 x k l) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
      intro x l
      cases k with
      | zero => exact mixedMoment_zero_time_nonnegative hw0 hw1 l x
      | succ k =>
          cases k with
          | zero => exact mixedMoment_one_time_nonnegative hw0 hw1 l x
          | succ k =>
              rw [show k+1+1 = k+2 by omega,
                mixedMoment_time_two]
              exact ih k (by omega) (T 1 x) l

/-- Every all-degree mixed time/defect moment is nonnegative on the SAME
literal-width completed Wilson carrier. -/
theorem mixedMoment_nonnegative (x : V) (k l : Nat) :
    RCnonneg (mixedMoment hw0 hw1 x k l) :=
  mixedMoment_nonnegative_aux hw0 hw1 k x l

/-- The exact positive Hausdorff split `m(k,l)=m(k+1,l)+m(k,l+1)`.
No measure or operator inverse is introduced. -/
theorem mixedMoment_split (x : V) (k l : Nat) :
    mixedMoment hw0 hw1 x k l =
      RCadd (mixedMoment hw0 hw1 x (k+1) l)
        (mixedMoment hw0 hw1 x k (l+1)) := by
  let y := defectPower hw0 hw1 l x
  have htime : T (k+1) y = T 1 (T k y) := by
    rw [← completedTime_add]
    congr 1
    omega
  have hdef : T k (defectPower hw0 hw1 (l+1) x) =
      defect hw0 hw1 (T k y) := by
    change T k (defect hw0 hw1 y) = _
    exact (defect_time hw0 hw1 k y).symm
  unfold mixedMoment
  rw [htime, hdef, defect, inner_sub_right]
  exact (rc_add_sub_cancel (B x (T k y)) (B x (T 1 (T k y)))).symm

#print axioms completedTime_form_le
#print axioms defect
#print axioms defect_symmetric
#print axioms defect_time
#print axioms time_add_defect
#print axioms defect_nonnegative
#print axioms time_defect_nonnegative
#print axioms defectPower
#print axioms defectPower_succ_right
#print axioms defectPower_add
#print axioms defectPower_symmetric
#print axioms time_defectPower
#print axioms mixedMoment
#print axioms mixedMoment_zero
#print axioms mixedMoment_nonnegative
#print axioms mixedMoment_split

end YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
