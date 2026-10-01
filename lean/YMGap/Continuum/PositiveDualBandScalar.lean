/-
# A cleared positive dual-band scalar estimate

This finite scalar implication keeps the zero-mass case explicit and does not
form a reciprocal of F.
-/

import YMGap.Constructive.RationalsMul
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.PositiveDualBandScalar

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private theorem le_of_mul_le_mul_right_pos {a b c : Q'}
    (hc : (0 : Q') < c) (h : a*c ≤ b*c) : a ≤ b := by
  have hcnum : (0 : Int) < c.num := by
    change (0 : Int) * (c.den : Int) < c.num * (1 : Int) at hc
    simpa using hc
  have hraw := h
  change (a*c).num * ((b*c).den : Int) ≤ (b*c).num * ((a*c).den : Int) at hraw
  rw [Q'.mul_den_cast b c, Q'.mul_den_cast a c] at hraw
  change (a.num*c.num) * ((b.den : Int)*(c.den : Int)) ≤
    (b.num*c.num) * ((a.den : Int)*(c.den : Int)) at hraw
  have hleft : (a.num*c.num) * ((b.den : Int)*(c.den : Int)) =
      (a.num*(b.den : Int)) * (c.num*(c.den : Int)) := by
    calc
      _ = a.num * (c.num * ((b.den : Int)*(c.den : Int))) := by
        rw [Int.mul_assoc]
      _ = a.num * ((b.den : Int) * (c.num*(c.den : Int))) := by
        rw [Int.mul_left_comm c.num (b.den : Int) (c.den : Int)]
      _ = (a.num*(b.den : Int)) * (c.num*(c.den : Int)) := by
        rw [← Int.mul_assoc]
  have hright : (b.num*c.num) * ((a.den : Int)*(c.den : Int)) =
      (b.num*(a.den : Int)) * (c.num*(c.den : Int)) := by
    calc
      _ = b.num * (c.num * ((a.den : Int)*(c.den : Int))) := by
        rw [Int.mul_assoc]
      _ = b.num * ((a.den : Int) * (c.num*(c.den : Int))) := by
        rw [Int.mul_left_comm c.num (a.den : Int) (c.den : Int)]
      _ = (b.num*(a.den : Int)) * (c.num*(c.den : Int)) := by
        rw [← Int.mul_assoc]
  have hcden : (0 : Int) < (c.den : Int) := by
    exact_mod_cast Q'.den_pos c
  have hfactor : (0 : Int) < c.num * (c.den : Int) :=
    Int.mul_pos hcnum hcden
  have hscaled : (a.num*(b.den : Int)) * (c.num*(c.den : Int)) ≤
      (b.num*(a.den : Int)) * (c.num*(c.den : Int)) := by
    calc
      _ = (a.num*c.num) * ((b.den : Int)*(c.den : Int)) := hleft.symm
      _ ≤ (b.num*c.num) * ((a.den : Int)*(c.den : Int)) := hraw
      _ = (b.num*(a.den : Int)) * (c.num*(c.den : Int)) := hright
  exact Int.le_of_mul_le_mul_right hscaled hfactor

/-- Cleared scalar dual-band estimate. All quantities are nonnegative, and
the F=0 branch is proved directly, so no reciprocal or strict positivity
assumption on F is needed. -/
theorem response_cleared {lambda l u F M C B D : Q'}
    (hlambda0 : (0 : Q') < lambda) (hlambda1 : lambda ≤ 1)
    (hl : (0 : Q') ≤ l) (hu : (0 : Q') ≤ u)
    (hF : (0 : Q') ≤ F) (hM0 : (0 : Q') ≤ M)
    (hB : (0 : Q') ≤ B) (hD0 : (0 : Q') ≤ D)
    (hC : lambda*l*F ≤ C) (hCS : C*C ≤ B*D)
    (hD : D ≤ lambda*F) (hM : M ≤ u*u*F) :
    lambda*(l*l)*M ≤ (u*u)*B := by
  by_cases hFpos : (0 : Q') < F
  · let x := lambda*l*F
    let y := lambda*F
    let a := lambda*(l*l)*F
    have hLambda0 : (0 : Q') ≤ lambda := Int.le_of_lt hlambda0
    have hll : (0 : Q') ≤ l*l := Q'.mul_nonneg l l hl hl
    have hLambdaL : (0 : Q') ≤ lambda*l := Q'.mul_nonneg lambda l hLambda0 hl
    have hx0 : (0 : Q') ≤ x := Q'.mul_nonneg (lambda*l) F hLambdaL hF
    have hLambdaLF : (0 : Q') ≤ lambda*l*F :=
      Q'.mul_nonneg (lambda*l) F hLambdaL hF
    have hC0 : (0 : Q') ≤ C := Q'.le_trans' _ _ _ hLambdaLF hC
    have hxC : x ≤ C := hC
    have hxxC : x*x ≤ C*C :=
      Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right x C x hxC hx0)
        (Q'.mul_le_mul_of_nonneg_left x C C hxC hC0)
    have hBD : B*D ≤ B*y :=
      Q'.mul_le_mul_of_nonneg_left D y B hD hB
    have hxx : x*x ≤ B*y :=
      Q'.le_trans' _ _ _ hxxC (Q'.le_trans' _ _ _ hCS hBD)
    have hxy : x*x ≈ a*y :=
      poly_identity_of_normal_eq
        (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2))
          (.mul (.mul (.var 0) (.var 1)) (.var 2)))
        (.mul (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 2))
          (.mul (.var 0) (.var 2)))
        (by decide) (fun | 0 => lambda | 1 => l | _ => F)
    have hay : a*y ≤ B*y :=
      Q'.le_trans' _ _ _ (Q'.ge_of_eqv hxy) hxx
    have hypos : (0 : Q') < y := by
      have hLambdaNum : (0 : Int) < lambda.num := by
        change (0 : Int) * (lambda.den : Int) < lambda.num * (1 : Int) at hlambda0
        simpa using hlambda0
      have hFnum : (0 : Int) < F.num := by
        change (0 : Int) * (F.den : Int) < F.num * (1 : Int) at hFpos
        simpa using hFpos
      change (0 : Int) * ((lambda*F).den : Int) <
        (lambda*F).num * (1 : Int)
      simpa [Q'.mul] using Int.mul_pos hLambdaNum hFnum
    have haB : a ≤ B := le_of_mul_le_mul_right_pos hypos hay
    have hLambdaL2 : (0 : Q') ≤ lambda*(l*l) := Q'.mul_nonneg lambda (l*l) hLambda0 hll
    have hstep1 : lambda*(l*l)*M ≤ lambda*(l*l)*(u*u*F) :=
      Q'.mul_le_mul_of_nonneg_left M (u*u*F) (lambda*(l*l)) hM hLambdaL2
    have hmove : lambda*(l*l)*(u*u*F) ≈ (u*u)*(lambda*(l*l)*F) :=
      poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.mul (.var 1) (.var 1)))
          (.mul (.mul (.var 2) (.var 2)) (.var 3)))
        (.mul (.mul (.var 2) (.var 2))
          (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 3)))
        (by decide) (fun | 0 => lambda | 1 => l | 2 => u | _ => F)
    have huu : (0 : Q') ≤ u*u := Q'.mul_nonneg u u hu hu
    have hstep2 : (u*u)*a ≤ (u*u)*B :=
      Q'.mul_le_mul_of_nonneg_left a B (u*u) haB huu
    exact Q'.le_trans' _ _ _ hstep1
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hmove) hstep2)
  · have hFnum : F.num = 0 := by
      have hnum0 : (0 : Int) ≤ F.num := (Q'.zero_le_iff_num_nonneg F).mp hF
      have hnotnum : ¬ (0 : Int) < F.num := by
        intro hn
        apply hFpos
        change (0 : Int) * (F.den : Int) < F.num * (1 : Int)
        simpa using hn
      omega
    have hMF : M ≤ 0 := by
      have hUF : (u*u*F).eqv 0 := by
        change ((u*u).num*F.num) * 1 = 0 * ((u*u*F).den : Int)
        simp [hFnum]
      exact Q'.le_trans' _ _ _ hM (Q'.le_of_eqv hUF)
    have hMnum : M.num = 0 := by
      have hnle : M.num ≤ 0 := by
        change M.num * 1 ≤ 0 * (M.den : Int) at hMF
        simpa using hMF
      have hnge : (0 : Int) ≤ M.num := (Q'.zero_le_iff_num_nonneg M).mp hM0
      omega
    have hleft : (lambda*(l*l)*M).eqv 0 := by
      change ((lambda*(l*l)).num*M.num) * 1 = 0 * ((lambda*(l*l)*M).den : Int)
      simp [hMnum]
    have hrhs : (0 : Q') ≤ (u*u)*B :=
      Q'.mul_nonneg (u*u) B (Q'.mul_nonneg u u hu hu) hB
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft) hrhs

#print axioms response_cleared

end YMGap.Continuum.PositiveDualBandScalar
