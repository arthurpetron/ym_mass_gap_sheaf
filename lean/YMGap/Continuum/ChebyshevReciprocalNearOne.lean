/-
# Reciprocal first-kind Chebyshev values near one

If an argument lies in the rational half-window above one and its degree-
dependent excess is at most h ≤ 1, the actual positive reciprocal of its
Chebyshev value lies in [1-h,1]. This is a scalar estimate only; it is not
a lower bound on any Yang--Mills covariance.
-/

import YMGap.Continuum.ChebyshevNearOneUpper

namespace YMGap.Continuum.ChebyshevReciprocalNearOne

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

/-- Elementary reciprocal band; the denominator is the actual positive rational. -/
theorem reciprocal_band (a h : Q') (ha : (0 : Q') < a)
    (ha1 : (1 : Q') ≤ a) (hah : a ≤ 1+h)
    (h0 : (0 : Q') ≤ h) (h1 : h ≤ 1) :
    1 + -h ≤ Q'.recipPos a ha ∧ Q'.recipPos a ha ≤ 1 := by
  have hupper : Q'.recipPos a ha ≤ 1 := by
    apply Q'.le_of_mul_le_mul_left (c := a) ?_ ha
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_recipPos_eqv a ha))
      (Q'.le_trans' _ _ _ ha1 (Q'.ge_of_eqv (Q'.mul_one_eqv a)))
  refine ⟨?_, hupper⟩
  have hn : (0 : Q') ≤ 1 + -h := Q'.sub_nonneg_of_le h1
  have hp : (1 + -h)*(1+h) ≤ (1 : Q') := by
    apply Q'.le_of_sub_nonneg
    have he : (1 : Q') + -((1 + -h)*(1+h)) ≈ h*h :=
      poly_identity_of_normal_eq
        (.add (.const 1) (.neg (.mul (.add (.const 1) (.neg (.var 0)))
          (.add (.const 1) (.var 0)))))
        (.mul (.var 0) (.var 0)) (by decide) (fun _ => h)
    exact Q'.le_trans' _ _ _ (Q'.mul_nonneg _ _ h0 h0) (Q'.ge_of_eqv he)
  apply Q'.le_of_mul_le_mul_left (c := a) ?_ ha
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv a (1 + -h)))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hah hn)
      (Q'.le_trans' _ _ _ hp (Q'.ge_of_eqv (Q'.mul_recipPos_eqv a ha))))

/-- Construct the actual positive reciprocal; its positivity proof is
computed from the first-kind recurrence, not an extra hypothesis. -/
def nearOneReciprocal (e : Q') (he0 : (0 : Q') ≤ e) (n : Nat) : Q' :=
  Q'.recipPos (Cheb.T n (1+e))
    (ChebyshevAboveOne.T_positive (1+e) (Q'.add_le_self_of_nonneg 1 e he0) n)

/-- A degree-dependent excess budget bounds the reciprocal near one. -/
theorem nearOne_reciprocal_bounds (e h : Q')
    (he0 : (0 : Q') ≤ e)
    (hehalf : e ≤ Q'.mkPos 1 2 (by decide))
    (h0 : (0 : Q') ≤ h) (h1 : h ≤ 1)
    (n : Nat) (hbudget : e*(4 : Q')^n ≤ h) :
    1 + -h ≤ nearOneReciprocal e he0 n ∧ nearOneReciprocal e he0 n ≤ 1 := by
  have hx : (1 : Q') ≤ 1+e := Q'.add_le_self_of_nonneg 1 e he0
  have hlo := (ChebyshevAboveOne.T_lower_and_step (1+e) hx n).1
  have hhi : Cheb.T n (1+e) ≤ 1+h :=
    Q'.le_trans' _ _ _ (ChebyshevNearOneUpper.T_near_one_upper e he0 hehalf n)
      (Q'.add_le_add_left 1 _ _ hbudget)
  exact reciprocal_band _ _
    (ChebyshevAboveOne.T_positive (1+e) hx n) hlo hhi h0 h1

end YMGap.Continuum.ChebyshevReciprocalNearOne

#print axioms YMGap.Continuum.ChebyshevReciprocalNearOne.reciprocal_band
#print axioms YMGap.Continuum.ChebyshevReciprocalNearOne.nearOneReciprocal
#print axioms YMGap.Continuum.ChebyshevReciprocalNearOne.nearOne_reciprocal_bounds
