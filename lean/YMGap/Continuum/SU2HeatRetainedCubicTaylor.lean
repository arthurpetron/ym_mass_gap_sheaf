/-
The signed cubic remainder on a RETAINED finite SU(2) heat mode.

The coefficient and remainder are rational-setoid expressions.  In particular
this file does not replace the original finite heat cutoff by an untruncated
operator: the omitted coefficient is accounted for by the caller.
-/

import YMGap.Continuum.BulkModeCrux
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.HalfPow

namespace YMGap.Continuum.SU2HeatRetainedCubicTaylor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BulkModeCrux

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast,
               Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Q'.neg_den, neg_num_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.natCast_mul, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg,
               Int.zero_mul, Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

/-- The exact second-order coefficient `n(n-1)/2`, written without Nat
subtraction.  This expression is also the public coefficient used by the
original-cutoff mode-tree consumer. -/
def quadraticCoeff (n : Nat) : Q' :=
  HalfPow.half * (Q'.ofNat n * Q'.ofNat n - Q'.ofNat n)

/-- The exact signed remainder after the quadratic term of `w^n`. -/
def cubicRemainder (w : Q') (n : Nat) : Q' :=
  qpow w n - 1 + Q'.ofNat n * ((1 : Q') - w) -
    quadraticCoeff n * (((1 : Q') - w) * ((1 : Q') - w))

/-- Finite cubic budget `∑_{j<n} j(j-1)/2`.  It is recursive to keep the
induction denominator-free. -/
def cubicBudget : Nat → Q'
  | 0 => 0
  | n + 1 => cubicBudget n + quadraticCoeff n

private theorem half_two : HalfPow.half * (2 : Q') ≈ 1 := by decide

/-- The half-form coefficient coincides with the existing constructive
triangular sum. -/
theorem quadraticCoeff_triSum (n : Nat) :
    quadraticCoeff n ≈ triSum n := by
  have hc := triSum_closed n
  have hsub :
      (Q'.ofNat n * Q'.ofNat n - Q'.ofNat n) ≈
        ((2 : Q') * triSum n) := by
    have h1 := Q'.add_eqv_congr_right _ _ (-Q'.ofNat n) (Q'.eqv_symm hc)
    exact Q'.eqv_trans _ _ _ h1
      (add_sub_cancel ((2 : Q') * triSum n) (Q'.ofNat n))
  unfold quadraticCoeff
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hsub) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv HalfPow.half 2 (triSum n))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ half_two) ?_
  exact Q'.one_mul_eqv (triSum n)

theorem quadraticCoeff_nonnegative (n : Nat) :
    (0 : Q') ≤ quadraticCoeff n :=
  Q'.le_trans' _ _ _ (triSum_nonneg n)
    (Q'.le_of_eqv (Q'.eqv_symm (quadraticCoeff_triSum n)))

theorem quadraticCoeff_succ (n : Nat) :
    quadraticCoeff (n + 1) ≈ quadraticCoeff n + Q'.ofNat n := by
  exact Q'.eqv_trans _ _ _ (quadraticCoeff_triSum (n + 1))
    (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm (quadraticCoeff_triSum n)))

/-- The exact power recurrence leaves one nonnegative cubic payment. -/
theorem cubicRemainder_succ (w : Q') (n : Nat) :
    cubicRemainder w (n + 1) ≈
      w * cubicRemainder w n -
        quadraticCoeff n *
          ((((1 : Q') - w) * ((1 : Q') - w)) * ((1 : Q') - w)) := by
  let N := Q'.ofNat n
  let C := quadraticCoeff n
  let h := (1 : Q') - w
  have hN : Q'.ofNat (n + 1) ≈ N + 1 := Q'.ofNat_add_eqv n 1
  have hC : quadraticCoeff (n + 1) ≈ C + N := quadraticCoeff_succ n
  have hstart : cubicRemainder w (n + 1) ≈
      (qpow w n * w - 1 + (N + 1) * h) - (C + N) * (h * h) := by
    unfold cubicRemainder
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.eqv_refl _)
        (Q'.mul_eqv_congr_right _ _ _ hN))
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_right _ _ _ hC))
  refine Q'.eqv_trans _ _ _ hstart ?_
  unfold cubicRemainder N C h
  let H : RingNormaliser.PolyExpr := .add (.const 1) (.neg (.var 1))
  let H2 : RingNormaliser.PolyExpr := .mul H H
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add
      (.add
        (.add (.mul (.var 0) (.var 1)) (.neg (.const 1)))
        (.mul (.add (.var 2) (.const 1)) H))
      (.neg (.mul (.add (.var 3) (.var 2)) H2)))
    (.add
      (.mul (.var 1)
        (.add
          (.add (.add (.var 0) (.neg (.const 1))) (.mul (.var 2) H))
          (.neg (.mul (.var 3) H2))))
      (.neg (.mul (.var 3) (.mul H2 H))))
    (by decide)
    (fun
      | 0 => qpow w n
      | 1 => w
      | 2 => Q'.ofNat n
      | _ => quadraticCoeff n)

private theorem cubicRemainder_zero (w : Q') : cubicRemainder w 0 ≈ 0 := by
  let H := (1 : Q') - w
  have hc : quadraticCoeff 0 ≈ 0 := quadraticCoeff_triSum 0
  have hz : Q'.ofNat 0 ≈ 0 := Q'.ofNat_zero_eqv
  have hpoly : cubicRemainder w 0 ≈
      Q'.ofNat 0 * H - quadraticCoeff 0 * (H * H) := by
    unfold cubicRemainder qpow
    exact RingNormaliser.poly_identity_of_normal_eq
      (.add
        (.add
          (.add (.const 1) (.neg (.const 1)))
          (.mul (.var 0) (.var 1)))
        (.neg (.mul (.var 2) (.mul (.var 1) (.var 1)))))
      (.add (.mul (.var 0) (.var 1))
        (.neg (.mul (.var 2) (.mul (.var 1) (.var 1)))))
      (by decide)
      (fun
        | 0 => Q'.ofNat 0
        | 1 => H
        | _ => quadraticCoeff 0)
  have hreplace :
      Q'.ofNat 0 * H - quadraticCoeff 0 * (H * H) ≈
        (0 : Q') * H - (0 : Q') * (H * H) :=
    Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_right _ _ _ hz)
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_right _ _ _ hc))
  have hlast : (0 : Q') * H - (0 : Q') * (H * H) ≈ 0 := by
    exact RingNormaliser.poly_identity_of_normal_eq
      (.add (.mul (.const 0) (.var 0))
        (.neg (.mul (.const 0) (.mul (.var 0) (.var 0)))))
      (.const 0) (by decide) (fun _ => H)
  exact Q'.eqv_trans _ _ _ hpoly (Q'.eqv_trans _ _ _ hreplace hlast)

theorem cubicBudget_nonnegative : ∀ n, (0 : Q') ≤ cubicBudget n
  | 0 => Q'.le_refl' _
  | n + 1 =>
      Q'.zero_le_add _ _ (cubicBudget_nonnegative n)
        (quadraticCoeff_nonnegative n)

private theorem one_sub_nonnegative {w : Q'} (hw1 : w ≤ (1 : Q')) :
    (0 : Q') ≤ (1 : Q') - w := Q'.sub_nonneg_of_le hw1

private theorem cube_nonnegative {w : Q'} (hw1 : w ≤ (1 : Q')) :
    (0 : Q') ≤
      ((((1 : Q') - w) * ((1 : Q') - w)) * ((1 : Q') - w)) := by
  have hh := one_sub_nonnegative hw1
  exact Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hh hh) hh

/-- The retained cubic remainder has the negative sign expected from the
third binomial term, for every exponent including `0,1,2`. -/
theorem cubicRemainder_nonpositive {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    ∀ n, cubicRemainder w n ≤ (0 : Q')
  | 0 => Q'.le_of_eqv (cubicRemainder_zero w)
  | n + 1 => by
      have ih := cubicRemainder_nonpositive hw0 hw1 n
      have hmul := Q'.mul_le_mul_of_nonneg_left
        (cubicRemainder w n) 0 w ih hw0
      have hpayment := Q'.mul_nonneg _ _
        (quadraticCoeff_nonnegative n) (cube_nonnegative hw1)
      have hstep :
          w * cubicRemainder w n -
              quadraticCoeff n *
                ((((1 : Q') - w) * ((1 : Q') - w)) * ((1 : Q') - w)) ≤ 0 := by
        have hd := Q'.neg_le_neg hpayment
        exact Q'.le_trans' _ _ _
          (Q'.add_le_add_right _ _ _ hmul)
          (Q'.le_trans' _ _ _
            (Q'.add_le_add_left _ _ _ hd)
            (Q'.le_of_eqv (by ring_qeqv)))
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (cubicRemainder_succ w n)) hstep

/-- A sharper-than-`n³` cubic bound, with a finite recursively computed
coefficient.  This is the invariant behind the lower estimate. -/
theorem cubicRemainder_budget_lower {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    ∀ n, -(cubicBudget n *
      ((((1 : Q') - w) * ((1 : Q') - w)) * ((1 : Q') - w))) ≤
        cubicRemainder w n := by
  let h := (1 : Q') - w
  have hh : (0 : Q') ≤ h := one_sub_nonnegative hw1
  have h3 : (0 : Q') ≤ (h * h) * h :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hh hh) hh
  have hinv : ∀ n,
      (0 : Q') ≤ cubicRemainder w n + cubicBudget n * ((h * h) * h) := by
    intro n
    induction n with
    | zero =>
        have hbase : cubicRemainder w 0 + cubicBudget 0 * ((h * h) * h) ≈ 0 := by
          exact Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr_right _ _ _ (cubicRemainder_zero w))
            (RingNormaliser.poly_identity_of_normal_eq
              (.add (.const 0) (.mul (.const 0) (.var 0)))
              (.const 0) (by decide) (fun _ => (h * h) * h))
        exact Q'.le_of_eqv (Q'.eqv_symm hbase)
    | succ n ih =>
        have hrec :
            cubicRemainder w (n + 1) +
                cubicBudget (n + 1) * ((h * h) * h) ≈
              w * (cubicRemainder w n + cubicBudget n * ((h * h) * h)) +
                h * (cubicBudget n * ((h * h) * h)) := by
          have hr := cubicRemainder_succ w n
          have hrew := Q'.add_eqv_congr_right _ _
            (cubicBudget (n + 1) * ((h * h) * h)) hr
          refine Q'.eqv_trans _ _ _ hrew ?_
          change
            w * cubicRemainder w n - quadraticCoeff n * ((h * h) * h) +
                (cubicBudget n + quadraticCoeff n) * ((h * h) * h) ≈
              w * (cubicRemainder w n + cubicBudget n * ((h * h) * h)) +
                h * (cubicBudget n * ((h * h) * h))
          let H : RingNormaliser.PolyExpr := .add (.const 1) (.neg (.var 0))
          let H3 : RingNormaliser.PolyExpr := .mul (.mul H H) H
          exact RingNormaliser.poly_identity_of_normal_eq
            (.add
              (.add (.mul (.var 0) (.var 1))
                (.neg (.mul (.var 2) H3)))
              (.mul (.add (.var 3) (.var 2)) H3))
            (.add
              (.mul (.var 0) (.add (.var 1) (.mul (.var 3) H3)))
              (.mul H (.mul (.var 3) H3)))
            (by decide)
            (fun
              | 0 => w
              | 1 => cubicRemainder w n
              | 2 => quadraticCoeff n
              | _ => cubicBudget n)
        have hright :
            (0 : Q') ≤
              w * (cubicRemainder w n + cubicBudget n * ((h * h) * h)) +
                h * (cubicBudget n * ((h * h) * h)) :=
          Q'.zero_le_add _ _
            (Q'.mul_nonneg _ _ hw0 ih)
            (Q'.mul_nonneg _ _ hh
              (Q'.mul_nonneg _ _ (cubicBudget_nonnegative n) h3))
        exact Q'.le_trans' _ _ _ hright
          (Q'.le_of_eqv (Q'.eqv_symm hrec))
  intro n
  have hi := hinv n
  have hrel :
      -(cubicBudget n * ((h * h) * h)) ≤
        cubicRemainder w n := by
    have hs := Q'.add_le_add_left
      (-(cubicBudget n * ((h * h) * h))) 0
      (cubicRemainder w n + cubicBudget n * ((h * h) * h)) hi
    have hleft : -(cubicBudget n * ((h * h) * h)) ≈
        -(cubicBudget n * ((h * h) * h)) + 0 :=
      Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' _))
    have hright :
        -(cubicBudget n * ((h * h) * h)) +
            (cubicRemainder w n + cubicBudget n * ((h * h) * h)) ≈
          cubicRemainder w n := by
      exact RingNormaliser.poly_identity_of_normal_eq
        (.add (.neg (.var 0)) (.add (.var 1) (.var 0)))
        (.var 1) (by decide)
        (fun
          | 0 => cubicBudget n * ((h * h) * h)
          | _ => cubicRemainder w n)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hright))
  exact hrel

end YMGap.Continuum.SU2HeatRetainedCubicTaylor

#print axioms YMGap.Continuum.SU2HeatRetainedCubicTaylor.quadraticCoeff_triSum
#print axioms YMGap.Continuum.SU2HeatRetainedCubicTaylor.quadraticCoeff
#print axioms YMGap.Continuum.SU2HeatRetainedCubicTaylor.cubicRemainder
#print axioms YMGap.Continuum.SU2HeatRetainedCubicTaylor.cubicBudget
#print axioms YMGap.Continuum.SU2HeatRetainedCubicTaylor.quadraticCoeff_nonnegative
#print axioms YMGap.Continuum.SU2HeatRetainedCubicTaylor.quadraticCoeff_succ
#print axioms YMGap.Continuum.SU2HeatRetainedCubicTaylor.cubicBudget_nonnegative
#print axioms YMGap.Continuum.SU2HeatRetainedCubicTaylor.cubicRemainder_succ
#print axioms YMGap.Continuum.SU2HeatRetainedCubicTaylor.cubicRemainder_nonpositive
#print axioms YMGap.Continuum.SU2HeatRetainedCubicTaylor.cubicRemainder_budget_lower
