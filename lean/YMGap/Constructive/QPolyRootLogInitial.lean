/-
Zero initial values of the ORIGINAL finite root/log S and F polynomials.
All endpoint calculations use their actual finite coefficient data and the
finite-log/polynomial-power evaluation pins.  No sign of S or F is assumed.
-/

import YMGap.Constructive.QPolyRootLogDifference

namespace YMGap.Constructive.QPolyRootLogInitial

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyCoefficient
open YMGap.Constructive.QPolyPositivePrimitive
open YMGap.Constructive.QPolyFiniteGeometric
open YMGap.Constructive.QPolyFiniteLogDerivative
open YMGap.Constructive.QPolyRootLogDifference
open YMGap.Constructive.RationalTail

/-- Actual F = D^(M+1)/(M+1) - u^N*S, with the SAME root and S data. -/
def rootLogRemainder (n m : Nat) : Poly :=
  psub
    (pscale (Q'.invSucc m) (polynomialPower (rootDefect n) (m + 1)))
    (pmul (rootPower n) (rootLogDifference n m))

private theorem power_at_one (x : Q') (hx : x.eqv 1) (n : Nat) :
    (x ^ n).eqv 1 := by
  induction n with
  | zero => exact Q'.eqv_refl 1
  | succ n ih =>
      exact Q'.eqv_trans _ _ _ (q_mul_congr hx ih) (Q'.one_mul_eqv 1)

private theorem power_at_zero (x : Q') (hx : x.eqv 0) (n : Nat) :
    (x ^ (n + 1)).eqv 0 :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right x 0 (x ^ n) hx)
    (q_zero_mul _)

private theorem finiteLog_at_zero (p : Poly) (hp : (eval p 0).eqv 0)
    (n : Nat) : (eval (finiteLog p n) 0).eqv 0 := by
  have hsum : forall k : Nat,
      (finSum (fun j => Q'.invSucc j * (eval p 0) ^ (j + 1)) k).eqv 0 := by
    intro k
    induction k with
    | zero => exact Q'.eqv_refl 0
    | succ k ih =>
        have hterm : (Q'.invSucc k * (eval p 0) ^ (k + 1)).eqv 0 :=
          Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left _ _ 0 (power_at_zero _ hp k))
            (q_mul_zero _)
        exact Q'.eqv_trans _ _ _ (q_add_congr ih hterm) (q_add_zero_eqv 0)
  exact Q'.eqv_trans _ _ _ (finiteLog_eval p n 0) (hsum n)

/-- The actual root power at h=0 is one, for every positive exponent N=n+1. -/
theorem rootPower_zero (n : Nat) : (eval (rootPower n) 0).eqv 1 :=
  Q'.eqv_trans _ _ _ (polynomialPower_eval complement (n + 1) 0)
    (power_at_one _ (by decide : (eval complement 0).eqv 1) (n + 1))

/-- The actual root defect vanishes at the zero endpoint. -/
theorem rootDefect_zero (n : Nat) : (eval (rootDefect n) 0).eqv 0 :=
  Q'.eqv_trans _ _ _ (eval_psub [1] (rootPower n) 0)
    (Q'.eqv_trans _ _ _
      (q_add_congr (by decide : (eval [1] 0).eqv 1)
        (Q'.neg_eqv_congr _ _ (rootPower_zero n)))
      (by decide : ((1 : Q') + -(1 : Q')).eqv 0))

/-- S(0)=0 is calculated from BOTH original finite truncated series. -/
theorem rootLogDifference_zero (n m : Nat) :
    (eval (rootLogDifference n m) 0).eqv 0 := by
  have hl : (eval
      (pscale (Q'.ofNat (n + 1)) (finiteLog coordinate ((n + 1) * m))) 0).eqv 0 :=
    Q'.eqv_trans _ _ _ (eval_pscale _ _ 0)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ 0
          (finiteLog_at_zero coordinate (by decide) ((n + 1) * m)))
        (q_mul_zero _))
  have hr : (eval (finiteLog (rootDefect n) m) 0).eqv 0 :=
    finiteLog_at_zero _ (rootDefect_zero n) m
  exact Q'.eqv_trans _ _ _ (eval_psub _ _ 0)
    (Q'.eqv_trans _ _ _ (q_add_congr hl (Q'.neg_eqv_congr _ _ hr))
      (by decide : ((0 : Q') + -(0 : Q')).eqv 0))

/-- F(0)=0, including the empty-log case M=0. -/
theorem rootLogRemainder_zero (n m : Nat) :
    (eval (rootLogRemainder n m) 0).eqv 0 := by
  have hl : (eval
      (pscale (Q'.invSucc m) (polynomialPower (rootDefect n) (m + 1))) 0).eqv 0 :=
    Q'.eqv_trans _ _ _ (eval_pscale _ _ 0)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ 0
          (Q'.eqv_trans _ _ _ (polynomialPower_eval (rootDefect n) (m + 1) 0)
            (power_at_zero _ (rootDefect_zero n) m)))
        (q_mul_zero _))
  have hr : (eval (pmul (rootPower n) (rootLogDifference n m)) 0).eqv 0 :=
    Q'.eqv_trans _ _ _ (eval_pmul _ _ 0)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ 0 (rootLogDifference_zero n m))
        (q_mul_zero _))
  exact Q'.eqv_trans _ _ _ (eval_psub _ _ 0)
    (Q'.eqv_trans _ _ _ (q_add_congr hl (Q'.neg_eqv_congr _ _ hr))
      (by decide : ((0 : Q') + -(0 : Q')).eqv 0))

end YMGap.Constructive.QPolyRootLogInitial

#print axioms YMGap.Constructive.QPolyRootLogInitial.rootLogRemainder
#print axioms YMGap.Constructive.QPolyRootLogInitial.rootPower_zero
#print axioms YMGap.Constructive.QPolyRootLogInitial.rootDefect_zero
#print axioms YMGap.Constructive.QPolyRootLogInitial.rootLogDifference_zero
#print axioms YMGap.Constructive.QPolyRootLogInitial.rootLogRemainder_zero
