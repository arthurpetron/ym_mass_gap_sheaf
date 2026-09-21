/-
# Rational elimination of a common Ward coefficient budget

If an energy has a coercive lower bound by a common nonnegative budget and
its square is bounded by a variance times the same budget, then the budget
can be eliminated without division or square roots.  Positive budgets are
cancelled only after an explicit product inequality; the null-setoid branch
is handled directly from rational order.

This is scalar algebra only.  It assumes neither a Ward identity nor an
analytic coercivity estimate; those remain inputs of the consumer.
-/

import YMGap.Constructive.Sqrt
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.RationalWardResponseCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

/-- Eliminate the common nonnegative coefficient budget `C` from a lower
energy estimate and a squared-energy upper estimate. -/
theorem response_coercivity
    (a b g C V E : Q')
    (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b)
    (hg : (0 : Q') ≤ g) (hC : (0 : Q') ≤ C)
    (hV : (0 : Q') ≤ V) (hE : (0 : Q') ≤ E)
    (hlower : a * C ≤ b * E)
    (hupper : E * E ≤ V * (g * C)) :
    (a * a) * C ≤ ((b * b) * g) * V := by
  have haa : (0 : Q') ≤ a * a := Q'.mul_nonneg _ _ ha ha
  have hbb : (0 : Q') ≤ b * b := Q'.mul_nonneg _ _ hb hb
  have hAC : (0 : Q') ≤ a * C := Q'.mul_nonneg _ _ ha hC
  have hBE : (0 : Q') ≤ b * E := Q'.mul_nonneg _ _ hb hE
  have hrhs : (0 : Q') ≤ ((b * b) * g) * V :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hbb hg) hV
  by_cases hCpos : (0 : Q') < C
  · have hsquare : (a * C) * (a * C) ≤ (b * E) * (b * E) :=
      Q'.mul_le_mul_of_nonneg hlower hlower hBE hAC
    have hscaled : (b * b) * (E * E) ≤
        (b * b) * (V * (g * C)) :=
      Q'.mul_le_mul_of_nonneg_left _ _ (b * b) hupper hbb
    have hleft : (a * C) * (a * C) ≈ C * ((a * a) * C) :=
      poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
        (.mul (.var 1) (.mul (.mul (.var 0) (.var 0)) (.var 1)))
        (by decide) (fun | 0 => a | _ => C)
    have hmiddle : (b * E) * (b * E) ≈ (b * b) * (E * E) :=
      poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
        (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
        (by decide) (fun | 0 => b | _ => E)
    have hright : (b * b) * (V * (g * C)) ≈
        C * (((b * b) * g) * V) :=
      poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 0))
          (.mul (.var 1) (.mul (.var 2) (.var 3))))
        (.mul (.var 3)
          (.mul (.mul (.mul (.var 0) (.var 0)) (.var 2)) (.var 1)))
        (by decide) (fun | 0 => b | 1 => V | 2 => g | _ => C)
    have hcancel : C * ((a * a) * C) ≤
        C * (((b * b) * g) * V) :=
      Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
        (Q'.le_trans' _ _ _ hsquare
          (Q'.le_trans' _ _ _ (Q'.le_of_eqv hmiddle)
            (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright))))
    exact Q'.le_of_mul_le_mul_left hcancel hCpos
  · have hnum : C.num ≤ (0 : Int) :=
      Int.not_lt.mp (fun h => hCpos (by
        show (0 : Int) * (C.den : Int) < C.num * (1 : Int)
        simpa only [Int.zero_mul, Int.mul_one] using h))
    have hCle : C ≤ (0 : Q') := by
      change C.num * (1 : Int) ≤ (0 : Int) * (C.den : Int)
      simpa only [Int.mul_one, Int.zero_mul] using hnum
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ (a * a) hCle haa)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_zero_eqv (a * a))) hrhs)

end YMGap.Continuum.RationalWardResponseCoercivity

#print axioms YMGap.Continuum.RationalWardResponseCoercivity.response_coercivity
