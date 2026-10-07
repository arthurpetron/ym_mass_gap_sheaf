/-
# Square order reflection for the constructive real quotient

If the right real is nonnegative and the left square is at most the right
square in eventual order, the left real is at most the right real. The proof
uses only rational epsilon estimates: at tolerance `t = epsilon/4`, eventual
nonnegativity gives `0 <= b+t`, while square order gives `a^2 <= b^2+8t^2`.
Then `(b+4t)^2 = b^2+8t^2+8t(b+t)` and `b+4t > 0`.

No comparison of arbitrary reals, square root, chosen quotient representative,
operator or physical gap hypothesis is used.
-/

import YMGap.Continuum.RCCauchySchwarz
import YMGap.Continuum.RingNormaliser

namespace YMGap.Constructive.CReal

set_option autoImplicit false

open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)

local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩

/-- Rational square order with explicit slack and approximate nonnegativity. -/
theorem rational_square_reflect_slack {a b t : Q'} (ht : (0 : Q') < t)
    (hb : (0 : Q') ≤ b + t)
    (hsq : a * a ≤ b * b + 8 * (t * t)) : a ≤ b + 4 * t := by
  let V := PolyExpr.var
  have hu : (0 : Q') < b + 4 * t := by
    have hp : (0 : Q') < 3 * t := Q'.mul_pos (by decide) ht
    have h := Q'.pos_add_nonneg hp hb
    exact Q'.pos_of_lt_of_le h
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.const 3 * V 1 + (V 0 + V 1)) (V 0 + .const 4 * V 1)
        (by decide) (fun | 0 => b | _ => t)))
  have hrem : (0 : Q') ≤ (8 * t) * (b + t) :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) (Q'.le_of_lt ht)) hb
  have hs : a * a ≤ (b + 4 * t) * (b + 4 * t) :=
    Q'.le_trans' _ _ _ hsq
      (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg (b * b + 8 * (t * t)) _ hrem)
        (Q'.le_of_eqv (poly_identity_of_normal_eq
          (V 0 * V 0 + .const 8 * (V 1 * V 1) + (.const 8 * V 1) * (V 0 + V 1))
          ((V 0 + .const 4 * V 1) * (V 0 + .const 4 * V 1)) (by decide)
          (fun | 0 => b | _ => t))))
  exact Q'.le_trans' _ _ _ (Q'.le_abs_self a) (Q'.abs_le_of_sq_le_sq hu hs)

/-- Eventual square order reflects to eventual order when the right real is
nonnegative. All estimates use rational tolerances. -/
theorem leEv_square_reflect_right_nonnegative {A B : CReal}
    (hb : leEv czero B) (hsq : leEv (mul A A) (mul B B)) : leEv A B := by
  intro epsilon hepsilon
  let quarter : Q' := ⟨1, 3⟩
  let t : Q' := quarter * epsilon
  have ht : (0 : Q') < t := Q'.mul_pos (by decide : (0 : Q') < quarter) hepsilon
  have hslack : (0 : Q') < 8 * (t * t) :=
    Q'.mul_pos (by decide) (Q'.mul_pos ht ht)
  obtain ⟨Nb, hNb⟩ := hb t ht
  obtain ⟨Ns, hNs⟩ := hsq (8 * (t * t)) hslack
  refine ⟨max Nb Ns, fun n hn => ?_⟩
  have hbn : (0 : Q') ≤ B.approx n + t :=
    hNb n (Nat.le_trans (Nat.le_max_left _ _) hn)
  have hsn : A.approx n * A.approx n ≤ B.approx n * B.approx n + 8 * (t * t) :=
    hNs n (Nat.le_trans (Nat.le_max_right _ _) hn)
  have h : A.approx n ≤ B.approx n + 4 * t :=
    rational_square_reflect_slack (a := A.approx n) (b := B.approx n) (t := t) ht hbn hsn
  have hfour_quarter : ((4 : Q') * quarter).eqv (1 : Q') := by decide
  have hfour_epsilon : (4 * t).eqv epsilon :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv 4 quarter epsilon))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ epsilon hfour_quarter)
        (Q'.one_mul_eqv epsilon))
  exact Q'.le_trans' (A.approx n) (B.approx n + 4 * t) (B.approx n + epsilon) h
    (Q'.le_of_eqv (Q'.add_eqv_congr_left (B.approx n) (4 * t) epsilon hfour_epsilon))

/-- The same square order reflection on `RC = CReal/Equiv`. Quotient induction
uses arbitrary representatives and does not choose a representative. -/
theorem RCsquare_le_reflect_right_nonnegative {a b : RC}
    (hb : RCle RCzero b) (hsq : RCle (RCmul a a) (RCmul b b)) : RCle a b := by
  revert hb hsq
  refine Quotient.inductionOn₂ a b ?_
  intro A B hb hsq
  exact leEv_square_reflect_right_nonnegative hb hsq

end YMGap.Constructive.CReal

#print axioms YMGap.Constructive.CReal.rational_square_reflect_slack
#print axioms YMGap.Constructive.CReal.leEv_square_reflect_right_nonnegative
#print axioms YMGap.Constructive.CReal.RCsquare_le_reflect_right_nonnegative
