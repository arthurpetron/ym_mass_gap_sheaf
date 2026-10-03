/-
# A symmetric form bound controls the norm on the ORIGINAL completion

Polarization of the two diagonal inequalities gives a cross-form estimate.
Testing it against the rational reciprocal multiple of E x then gives the
squared norm estimate. No scalar linearity of E, spectral theorem, inverse
operator, or comparison between derivative and logarithm is assumed.
-/

import YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
import YMGap.Continuum.RCSignedPairBudget
import YMGap.Continuum.RCScaleClose

namespace YMGap.Continuum.BF4WilsonAllNomeSymmetricFormNorm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RCSignedPairBudget (neg_mono scale_congr)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
  (completedInner_sub_left completedInner_sub_right)

local infix:50 " ≈ " => Q'.eqv

private theorem cross_collect (a b c : RC) :
    RCsub (RCadd (RCadd a b) (RCadd b c))
      (RCsub (RCsub a b) (RCsub b c)) = RCscale 4 b := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.add (.var 0) (.var 1)) (.add (.var 1) (.var 2)))
        (.neg (.add (.add (.var 0) (.neg (.var 1)))
          (.neg (.add (.var 1) (.neg (.var 2)))))))
      (.mul (.const 4) (.var 1)) (by decide)
      (fun | 0 => A.approx n | 1 => B.approx n | _ => C.approx n)))

private theorem norm_collect (a b c : RC) :
    RCadd (RCadd (RCadd a b) (RCadd b c))
      (RCsub (RCsub a b) (RCsub b c)) = RCscale 2 (RCadd a c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.add (.var 0) (.var 1)) (.add (.var 1) (.var 2)))
        (.add (.add (.var 0) (.neg (.var 1)))
          (.neg (.add (.var 1) (.neg (.var 2))))))
      (.mul (.const 2) (.add (.var 0) (.var 2))) (by decide)
      (fun | 0 => A.approx n | 1 => B.approx n | _ => C.approx n)))

private theorem scale_comm (s t : Q') (a : RC) :
    RCscale (s*t) a = RCscale (t*s) a := scale_congr (Q'.mul_comm_eqv s t) a

private theorem cancel_norm (u v : RC)
    (h : RCle (RCscale 4 v) (RCadd (RCscale 2 u) (RCscale 2 v))) :
    RCle v u := by
  have hh := RCadd_le_add h (RCle_refl (RCneg (RCscale 2 v)))
  have hl : RCsub (RCscale 4 v) (RCscale 2 v) = RCscale 2 v := by
    refine Quotient.inductionOn v ?_
    intro V
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.mul (.const 4) (.var 0)) (.neg (.mul (.const 2) (.var 0))))
        (.mul (.const 2) (.var 0)) (by decide) (fun _ => V.approx n)))
  have hr : RCsub (RCadd (RCscale 2 u) (RCscale 2 v)) (RCscale 2 v) =
      RCscale 2 u := by
    refine Quotient.inductionOn₂ u v ?_
    intro U V
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.add (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 1)))
          (.neg (.mul (.const 2) (.var 1))))
        (.mul (.const 2) (.var 0)) (by decide)
        (fun | 0 => U.approx n | _ => V.approx n)))
  change RCle (RCsub (RCscale 4 v) (RCscale 2 v))
    (RCsub (RCadd (RCscale 2 u) (RCscale 2 v)) (RCscale 2 v)) at hh
  rw [hl, hr] at hh
  have hs := RCscale_mono HalfPow.half_nonneg hh
  have htwo : HalfPow.half * 2 ≈ 1 := by decide
  simpa only [RCscale_RCscale, scale_congr htwo, RCscale_one] using hs

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "A" => completedAdd hw0 hw1
local notation "D" => completedSub hw0 hw1

/-- The two actual diagonal bounds imply the polarized cross-form bound.
No boundedness or scalar-linearity premise on E is required. -/
theorem symmetric_form_pair_bound (E : V → V)
    (hadd : ∀ x y, E (A x y) = A (E x) (E y))
    (hsub : ∀ x y, E (D x y) = D (E x) (E y))
    (hsym : ∀ x y, B (E x) y = B x (E y)) (e : Q')
    (hupper : ∀ z, RCle (B z (E z)) (RCscale e (B z z)))
    (hlower : ∀ z, RCle (RCneg (RCscale e (B z z))) (B z (E z)))
    (x y : V) :
    RCle (RCscale 4 (B (E x) y))
      (RCscale (2*e) (RCadd (B x x) (B y y))) := by
  have h := RCadd_le_add (hupper (A x y)) (neg_mono (hlower (D x y)))
  have hneg : RCneg (RCneg (RCscale e (B (D x y) (D x y)))) =
      RCscale e (B (D x y) (D x y)) := by
    refine Quotient.inductionOn (RCscale e (B (D x y) (D x y))) ?_
    intro R
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun n => Q'.neg_neg_eqv (R.approx n)))
  rw [hneg] at h
  change RCle (RCsub (B (A x y) (E (A x y))) (B (D x y) (E (D x y))))
    (RCadd (RCscale e (B (A x y) (A x y)))
      (RCscale e (B (D x y) (D x y)))) at h
  rw [hadd, hsub] at h
  simp only [completedInner_add_left, completedInner_add_right,
    completedInner_sub_left, completedInner_sub_right] at h
  rw [← hsym x y, completedInner_symm hw0 hw1 y (E x),
    completedInner_symm hw0 hw1 y x, cross_collect, ← RCscale_RCadd,
    norm_collect, RCscale_RCscale, scale_comm e 2] at h
  exact h

/-- A positive rational two-sided diagonal form bound controls the squared
norm on the SAME original Wilson completion. This is an algebraic implication,
not a construction of the diagonal estimates for any particular operator. -/
theorem symmetric_form_norm_bound (E : V → V)
    (hadd : ∀ x y, E (A x y) = A (E x) (E y))
    (hsub : ∀ x y, E (D x y) = D (E x) (E y))
    (hsym : ∀ x y, B (E x) y = B x (E y)) (e : Q') (he : (0 : Q') < e)
    (hupper : ∀ z, RCle (B z (E z)) (RCscale e (B z z)))
    (hlower : ∀ z, RCle (RCneg (RCscale e (B z z))) (B z (E z)))
    (x : V) : RCle (B (E x) (E x)) (RCscale (e*e) (B x x)) := by
  let r := Q'.recipPos e he
  have her : e*r ≈ 1 := Q'.mul_recipPos_eqv e he
  have h := symmetric_form_pair_bound hw0 hw1 E hadd hsub hsym e hupper hlower
    x (completedSmul hw0 hw1 r (E x))
  simp only [completedInner_smul_left, completedInner_smul_right,
    RCscale_RCscale] at h
  have hs := RCscale_mono (Q'.le_of_lt he) h
  rw [RCscale_RCscale, RCscale_RCscale, RCscale_RCadd, RCscale_RCscale] at hs
  have hleft : e*(4*r) ≈ 4 :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.const 4) (.var 1)))
        (.mul (.const 4) (.mul (.var 0) (.var 1))) (by decide)
        (fun | 0 => e | _ => r))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 4 _ _ her) (Q'.mul_one_eqv 4))
  have hbase : e*(2*e) ≈ 2*(e*e) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.const 2) (.var 0)))
      (.mul (.const 2) (.mul (.var 0) (.var 0))) (by decide) (fun _ => e)
  have htail : (e*(2*e))*(r*r) ≈ 2 :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.mul (.const 2) (.var 0)))
          (.mul (.var 1) (.var 1)))
        (.mul (.const 2) (.mul (.mul (.var 0) (.var 1))
          (.mul (.var 0) (.var 1)))) (by decide) (fun | 0 => e | _ => r))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left 2 _ _
          (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ (e*r) her)
            (Q'.mul_eqv_congr_left 1 _ _ her)))
        (by decide : (2 : Q')*(1*1) ≈ 2))
  rw [scale_congr hleft, scale_congr htail, scale_congr hbase,
    ← RCscale_RCscale 2 (e*e) (B x x)] at hs
  exact cancel_norm (RCscale (e*e) (B x x)) (B (E x) (E x)) hs

#print axioms symmetric_form_pair_bound
#print axioms symmetric_form_norm_bound

end YMGap.Continuum.BF4WilsonAllNomeSymmetricFormNorm
