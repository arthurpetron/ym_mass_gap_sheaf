/-
# Scalar complement-root masses with a computable rational tail

The recursion `m ↦ (1+m²)/2` is a scalar companion for positive
polynomial iterations. Its explicit residual modulus has no spectral-floor
assumption and asserts nothing about a continuum operator.
-/

import YMGap.Constructive.CRealExp
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.ComplementRootMass

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

def mass : Nat → Q'
  | 0 => 0
  | n+1 => HalfPow.half * (1 + mass n * mass n)

theorem mass_zero : mass 0 = 0 := rfl
theorem mass_succ (n : Nat) :
    mass (n+1) = HalfPow.half * (1 + mass n * mass n) := rfl

private theorem half_two : HalfPow.half * (1+1 : Q') ≈ 1 := by decide

theorem mass_nonnegative : ∀ n : Nat, (0 : Q') ≤ mass n
  | 0 => Q'.le_refl' _
  | n+1 =>
      Q'.mul_nonneg _ _ HalfPow.half_nonneg
        (Q'.zero_le_add _ _ Q'.zero_le_one
          (SumOfSquares.q_mul_self_nonneg (mass n)))

theorem mass_le_one : ∀ n : Nat, mass n ≤ (1 : Q')
  | 0 => Q'.zero_le_one
  | n+1 => by
      let a := mass n
      have ha0 : (0 : Q') ≤ a := mass_nonnegative n
      have ha1 : a ≤ (1 : Q') := mass_le_one n
      have haa : a*a ≤ a :=
        Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_left a 1 a ha1 ha0)
          (Q'.le_of_eqv (Q'.mul_one_eqv a))
      have hsq : a*a ≤ (1 : Q') := Q'.le_trans' _ _ _ haa ha1
      have hs : 1 + a*a ≤ (1+1 : Q') :=
        Q'.add_le_add_left 1 _ _ hsq
      exact Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half hs
          HalfPow.half_nonneg)
        (Q'.le_of_eqv half_two)

def residual (n : Nat) : Q' := 1 + -(mass n)

theorem residual_nonnegative (n : Nat) : (0 : Q') ≤ residual n :=
  Q'.sub_nonneg_of_le (mass_le_one n)

theorem residual_le_one (n : Nat) : residual n ≤ (1 : Q') := by
  have h := Q'.neg_le_neg (mass_nonnegative n)
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add_left 1 _ _ h)
    (Q'.le_of_eqv (QPoly.q_add_zero_eqv 1))

private def step (r : Q') : Q' := r + -(HalfPow.half * (r*r))

/-- The exact logistic residual recursion, with no discarded error. -/
theorem residual_step (n : Nat) : residual (n+1) ≈ step (residual n) := by
  let a := mass n
  let h := HalfPow.half
  have hring :
      (1 + -(h*(1+a*a))) ≈
      ((1 + -a) + -(h*((1 + -a)*(1 + -a)))) +
        a*(1 + -(h*(1+1))) :=
    poly_identity_of_normal_eq
      (.add (.const 1)
        (.neg (.mul (.var 1) (.add (.const 1) (.mul (.var 0) (.var 0))))))
      (.add
        (.add (.add (.const 1) (.neg (.var 0)))
          (.neg (.mul (.var 1)
            (.mul (.add (.const 1) (.neg (.var 0)))
              (.add (.const 1) (.neg (.var 0)))))))
        (.mul (.var 0)
          (.add (.const 1)
            (.neg (.mul (.var 1) (.add (.const 1) (.const 1)))))))
      (by decide) (fun | 0 => a | _ => h)
  have hz : a*(1 + -(h*(1+1))) ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (by decide : (1 + -(HalfPow.half*(1+1 : Q'))) ≈ (0 : Q')))
      (Q'.mul_zero_eqv a)
  exact Q'.eqv_trans _ _ _ hring
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ hz)
      (QPoly.q_add_zero_eqv _))

private theorem step_mono {r s : Q'}
    (hrs : r ≤ s) (hr1 : r ≤ (1 : Q')) (hs1 : s ≤ (1 : Q')) :
    step r ≤ step s := by
  have hgap : (0 : Q') ≤ s + -r := Q'.sub_nonneg_of_le hrs
  have hsum : r+s ≤ (1+1 : Q') := Q'.add_le_add hr1 hs1
  have hhalf : HalfPow.half * (r+s) ≤ (1 : Q') :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half hsum
        HalfPow.half_nonneg)
      (Q'.le_of_eqv half_two)
  have hfactor : (0 : Q') ≤ 1 + -(HalfPow.half*(r+s)) :=
    Q'.sub_nonneg_of_le hhalf
  have hprod : (0 : Q') ≤ (s + -r) *
      (1 + -(HalfPow.half*(r+s))) :=
    Q'.mul_nonneg _ _ hgap hfactor
  have he : (step s + -(step r)) ≈
      (s + -r) * (1 + -(HalfPow.half*(r+s))) :=
    poly_identity_of_normal_eq
      (.add
        (.add (.var 1)
          (.neg (.mul (.var 2) (.mul (.var 1) (.var 1)))))
        (.neg (.add (.var 0)
          (.neg (.mul (.var 2) (.mul (.var 0) (.var 0)))))))
      (.mul (.add (.var 1) (.neg (.var 0)))
        (.add (.const 1)
          (.neg (.mul (.var 2) (.add (.var 0) (.var 1))))))
      (by decide) (fun | 0 => r | 1 => s | _ => HalfPow.half)
  exact Q'.le_of_sub_nonneg
    (Q'.le_trans' _ _ _ hprod (Q'.ge_of_eqv he))

theorem mass_monotone (n : Nat) : mass n ≤ mass (n+1) := by
  have hgap : (0 : Q') ≤ (1 + -(mass n))*(1 + -(mass n)) :=
    SumOfSquares.q_mul_self_nonneg _
  have he : mass (n+1) + -(mass n) ≈
      HalfPow.half * ((1 + -(mass n))*(1 + -(mass n))) := by
    have h2 : HalfPow.half * (1+1 : Q') ≈ 1 := half_two
    have hr := poly_identity_of_normal_eq
      (.add (.mul (.var 1) (.add (.const 1) (.mul (.var 0) (.var 0))))
        (.neg (.var 0)))
      (.add
        (.mul (.var 1)
          (.mul (.add (.const 1) (.neg (.var 0)))
            (.add (.const 1) (.neg (.var 0)))))
        (.mul (.var 0)
          (.add (.mul (.var 1) (.add (.const 1) (.const 1)))
            (.neg (.const 1)))))
      (by decide) (fun | 0 => mass n | _ => HalfPow.half)
    have hz : mass n * (HalfPow.half*(1+1) + -1) ≈ 0 :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr_right _ _ _ h2)
            (Q'.add_neg_self_eqv 1)))
        (Q'.mul_zero_eqv _)
    exact Q'.eqv_trans _ _ _ hr
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _ hz)
        (QPoly.q_add_zero_eqv _))
  exact Q'.le_of_sub_nonneg
    (Q'.le_trans' _ _ _
      (Q'.mul_nonneg _ _ HalfPow.half_nonneg hgap)
      (Q'.ge_of_eqv he))

private theorem step_two_invSucc (n : Nat) :
    step (2*Q'.invSucc (n+1)) ≤ 2*Q'.invSucc (n+2) := by
  let a := Q'.invSucc (n+1)
  let b := Q'.invSucc (n+2)
  have hba : b ≤ a := ExpNeg.invSucc_le_of_le (by omega)
  have ha0 : (0 : Q') ≤ a := Q'.invSucc_nonneg _
  have hprod : (0 : Q') ≤ 2*a*(a + -b) :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (by decide) ha0)
      (Q'.sub_nonneg_of_le hba)
  have hrel : b*(a+1) ≈ a := ExpNeg.invSucc_cancel (n+1)
  have hrel0 : b*(a+1) + -a ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ hrel)
      (Q'.add_neg_self_eqv a)
  have hstep : step (2*a) ≈ 2*a + -(2*(a*a)) := by
    have hcoef : HalfPow.half * (2*2 : Q') ≈ 2 := by decide
    have hs : HalfPow.half * ((2*a)*(2*a)) ≈ 2*(a*a) :=
      Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq
          (.mul (.var 0)
            (.mul (.mul (.const 2) (.var 1))
              (.mul (.const 2) (.var 1))))
          (.mul (.mul (.var 0) (.mul (.const 2) (.const 2)))
            (.mul (.var 1) (.var 1)))
          (by decide) (fun | 0 => HalfPow.half | _ => a))
        (Q'.mul_eqv_congr_right _ _ _ hcoef)
    exact Q'.add_eqv_congr_left (2*a) _ _ (Q'.neg_eqv_congr _ _ hs)
  have hpoly : 2*b + -(2*a + -(2*(a*a))) ≈
      2*a*(a + -b) + 2*(b*(a+1) + -a) :=
    poly_identity_of_normal_eq
      (.add (.mul (.const 2) (.var 1))
        (.neg (.add (.mul (.const 2) (.var 0))
          (.neg (.mul (.const 2) (.mul (.var 0) (.var 0)))))))
      (.add
        (.mul (.mul (.const 2) (.var 0))
          (.add (.var 0) (.neg (.var 1))))
        (.mul (.const 2)
          (.add (.mul (.var 1) (.add (.var 0) (.const 1)))
            (.neg (.var 0)))))
      (by decide) (fun | 0 => a | _ => b)
  have hzero : 2*(b*(a+1) + -a) ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ hrel0)
      (Q'.mul_zero_eqv _)
  have hdiff : 2*b + -(step (2*a)) ≈ 2*a*(a + -b) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (2*b) _ _
        (Q'.neg_eqv_congr _ _ hstep))
      (Q'.eqv_trans _ _ _ hpoly
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ _ _ hzero)
          (QPoly.q_add_zero_eqv _)))
  exact Q'.le_of_sub_nonneg
    (Q'.le_trans' _ _ _ hprod (Q'.ge_of_eqv hdiff))

/-- Explicit rational O(1/n) residual majorant. -/
theorem residual_tail_le : ∀ n : Nat,
    residual n ≤ 2 * Q'.invSucc (n+1)
  | 0 => by
      change (1 : Q') ≤ 2 * Q'.invSucc 1
      exact Q'.le_of_eqv (by decide)
  | n+1 => by
      let b := 2*Q'.invSucc (n+1)
      have hb1 : b ≤ (1 : Q') := by
        have h := ExpNeg.invSucc_le_of_le (by omega : 1 ≤ n+1)
        exact Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_left _ _ 2 h (by decide))
          (Q'.le_of_eqv (by decide : 2*Q'.invSucc 1 ≈ (1 : Q')))
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (residual_step n))
        (Q'.le_trans' _ _ _
          (step_mono (residual_tail_le n) (residual_le_one n) hb1)
          (step_two_invSucc n))

/-- The explicit bound under a name used by the operator consumer. -/
theorem residual_le_two_invSucc (n : Nat) :
    residual n ≤ 2 * Q'.invSucc (n+1) := residual_tail_le n

/-- Type-level rational precision modulus; its value is executable from
the supplied positive tolerance. -/
def tailModulus (epsilon : Q') : Nat := (HalfPow.half*epsilon).den

theorem residual_small {epsilon : Q'} (hepsilon : (0 : Q') < epsilon)
    {n : Nat} (hn : tailModulus epsilon ≤ n) : residual n ≤ epsilon := by
  let delta := HalfPow.half*epsilon
  have hdelta : (0 : Q') < delta :=
    Q'.mul_pos (by decide : (0 : Q') < HalfPow.half) hepsilon
  have htail : Q'.invSucc (n+1) ≤ delta :=
    Q'.le_trans' _ _ _
      (ExpNeg.invSucc_le_of_le (show delta.den ≤ n+1 from
        Nat.le_trans hn (Nat.le_succ n)))
      (HalfPow.invSucc_den_le delta hdelta)
  have hscale : 2*Q'.invSucc (n+1) ≤ 2*delta :=
    Q'.mul_le_mul_of_nonneg_left _ _ 2 htail (by decide)
  have hpin : 2*delta ≈ epsilon := by
    unfold delta
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv 2 HalfPow.half epsilon))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (by decide : 2*HalfPow.half ≈ (1 : Q')))
        (Q'.one_mul_eqv epsilon))
  exact Q'.le_trans' _ _ _ (residual_tail_le n)
    (Q'.le_trans' _ _ _ hscale (Q'.le_of_eqv hpin))

end YMGap.Continuum.ComplementRootMass

#print axioms YMGap.Continuum.ComplementRootMass.mass
#print axioms YMGap.Continuum.ComplementRootMass.mass_nonnegative
#print axioms YMGap.Continuum.ComplementRootMass.mass_le_one
#print axioms YMGap.Continuum.ComplementRootMass.mass_monotone
#print axioms YMGap.Continuum.ComplementRootMass.residual_step
#print axioms YMGap.Continuum.ComplementRootMass.residual_tail_le
#print axioms YMGap.Continuum.ComplementRootMass.residual_le_two_invSucc
#print axioms YMGap.Continuum.ComplementRootMass.tailModulus
#print axioms YMGap.Continuum.ComplementRootMass.residual_small
