/-
# A completed self-pairing identity bounds the squared norm

If <x,x> = <x,p>, then x is orthogonal to p-x. Nonnegativity of the
squared norm of this actual difference gives <x,x> <= <p,p> in the
constructive-real quotient. No inverse, strict-positivity decision,
linearity hypothesis on an operator, or additional analytic data is used.
-/

import YMGap.Continuum.FCLimitContinuity

namespace YMGap.Continuum.GNSPairingNormBound

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient

private theorem rc_sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (CReal.sub_self_eqv_zero A)

private theorem rc_sub_zero (a : RC) : RCsub a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.eqv (-0) 0))
      (Q'.eqv_of_eq (Q'.add_zero' (A.approx n)))))

private theorem le_of_sub_nonnegative (a b : RC)
    (h : RCnonneg (RCsub b a)) : RCle a b := by
  have hz : RCadd RCzero a = a := by
    refine Quotient.inductionOn a ?_
    intro A
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun n => Q'.eqv_of_eq (Q'.zero_add' (A.approx n))))
  have hc : RCadd (RCsub b a) a = b := by
    refine Quotient.inductionOn₂ b a ?_
    intro B A
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun n => Q'.sub_add_cancel_eqv (B.approx n) (A.approx n)))
  have hb := RCadd_le_add h (RCle_refl a)
  rw [hz, hc] at hb
  exact hb

/-- The actual residual is orthogonal to a vector whose self-pairing
agrees with its pairing against the original input. -/
theorem residual_orthogonal (D : GNSData) (x p : GNSCompletionSpace D)
    (h : D.cinnerCompl x x = D.cinnerCompl x p) :
    D.cinnerCompl x (D.cSub p x) = CReal.RCzero := by
  rw [D.cinnerCompl_comm x (D.cSub p x), D.cinnerCompl_cSub_left,
    D.cinnerCompl_comm p x, ← h, rc_sub_self]

/-- A completed self-pairing identity implies the sharp squared-norm bound. -/
theorem norm_le_of_self_pairing (D : GNSData) (x p : GNSCompletionSpace D)
    (h : D.cinnerCompl x x = D.cinnerCompl x p) :
    CReal.RCle (D.cinnerCompl x x) (D.cinnerCompl p p) := by
  have hd : D.cinnerCompl (D.cSub p x) (D.cSub p x) =
      RCsub (D.cinnerCompl p p) (D.cinnerCompl x x) := by
    rw [D.cinnerCompl_cSub_left, residual_orthogonal D x p h,
      rc_sub_zero, D.cinnerCompl_comm p (D.cSub p x),
      D.cinnerCompl_cSub_left, ← h]
  apply le_of_sub_nonnegative
  rw [← hd]
  exact D.cinner_self_nonneg (D.cSub p x)

end YMGap.Continuum.GNSPairingNormBound

#print axioms YMGap.Continuum.GNSPairingNormBound.residual_orthogonal
#print axioms YMGap.Continuum.GNSPairingNormBound.norm_le_of_self_pairing
