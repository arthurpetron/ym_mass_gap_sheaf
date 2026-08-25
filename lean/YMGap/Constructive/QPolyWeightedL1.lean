/-
# Weighted coefficient bounds for constructive rational polynomials

For a low-to-high coefficient list `p`, `weightedL1 rho p` is

    sum_i |p_i| rho^i.

The main theorem proves directly from Horner evaluation that
`|eval p z| <= weightedL1 rho p` whenever `|z| <= rho`.  This is the
constructive coefficient-to-window compiler used by finite analytic
certificates.  It assumes no decidable normalization of `Q'` polynomials.
-/

import YMGap.Constructive.QPoly
import YMGap.Constructive.CRealExp

namespace YMGap.Constructive.QPolyWeightedL1

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly

/-- Weighted coefficient `L1` norm, in Horner order. -/
def weightedL1 (rho : Q') : Poly -> Q'
  | [] => 0
  | c :: cs => Q'.abs c + rho * weightedL1 rho cs

/-- The weighted coefficient norm is nonnegative for a nonnegative radius. -/
theorem weightedL1_nonnegative
    (rho : Q') (hrho : (0 : Q') <= rho) :
    forall p : Poly, (0 : Q') <= weightedL1 rho p
  | [] => Q'.le_refl' 0
  | c :: cs =>
      Q'.zero_le_add (Q'.abs c) (rho * weightedL1 rho cs)
        (Q'.abs_nonneg c)
        (Q'.mul_nonneg rho (weightedL1 rho cs) hrho
          (weightedL1_nonnegative rho hrho cs))

/-- Horner evaluation is bounded by the weighted coefficient norm throughout
the closed radius-`rho` window. -/
theorem abs_eval_le_weightedL1
    {rho z : Q'} (hrho : (0 : Q') <= rho)
    (hz : Q'.abs z <= rho) :
    forall p : Poly, Q'.abs (eval p z) <= weightedL1 rho p
  | [] => by
      change Q'.abs (0 : Q') <= 0
      decide
  | c :: cs => by
      change Q'.abs (c + z * eval cs z) <=
        Q'.abs c + rho * weightedL1 rho cs
      have htail : Q'.abs (z * eval cs z) <=
          rho * weightedL1 rho cs := by
        refine Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le z (eval cs z)) ?_
        refine Q'.le_trans' _ (rho * Q'.abs (eval cs z)) _ ?_ ?_
        · exact Q'.mul_le_mul_of_nonneg_right
            (Q'.abs z) rho (Q'.abs (eval cs z)) hz
            (Q'.abs_nonneg (eval cs z))
        · exact Q'.mul_le_mul_of_nonneg_left
            (Q'.abs (eval cs z)) (weightedL1 rho cs) rho
            (abs_eval_le_weightedL1 hrho hz cs) hrho
      exact Q'.le_trans' _ _ _ (ExpNeg.abs_add_le c (z * eval cs z))
        (Q'.add_le_add_left (Q'.abs c)
          (Q'.abs (z * eval cs z)) (rho * weightedL1 rho cs) htail)

end YMGap.Constructive.QPolyWeightedL1

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Constructive.QPolyWeightedL1.weightedL1_nonnegative
#print axioms
  YMGap.Constructive.QPolyWeightedL1.abs_eval_le_weightedL1
