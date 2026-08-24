/-
# The universal artanh-ratio Euler inverse frontier

The direct rational logarithm is represented through the coordinate

    y = (m - 1) / (m + 1),      m = (1 + y) / (1 - y).

This module removes the rational mantissa `m`, its logarithm wrapper, and all
Wilson/reconstruction data from the remaining exponential evaluation.  It
packages the one universal analytic statement still required: for a negative
`y` in the direct artanh window, the negative exponential of four times the
artanh partial sum converges to the square of the Mobius ratio
`(1+y)/(1-y)`.

The compiler is deliberately not inhabited here.  The exact inverse
calculation is the next analytic frontier.  What is proved here is the complete
rational algebra needed to compile that future family-independent witness back
to any direct-window rational logarithm.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Constructive.CRealExpRationalStreamContinuity
import YMGap.Constructive.CRealLogRatCongruence

namespace YMGap.Constructive.CRealArtanhEulerRatio

set_option autoImplicit false

open YMGap.Constructive

/-- For a strictly negative artanh coordinate, the denominator `1-y` of the
inverse Mobius transform is strictly positive. -/
theorem one_sub_pos_of_neg (y : Q') (hy : y < (0 : Q')) :
    (0 : Q') < (1 : Q') + -y :=
  Q'.pos_add_nonneg (by decide)
    (Q'.nonneg_neg_of_nonpos (Q'.le_of_lt hy))

/-- The inverse Mobius transform of the artanh coordinate. -/
def artanhRatio (y : Q') (hy : y < (0 : Q')) : Q' :=
  ((1 : Q') + y) * Q'.recipPos ((1 : Q') + -y) (one_sub_pos_of_neg y hy)

/-- Four times the negative artanh partial sum, written in the same literal
factorization used by the direct logarithm-square exponent. -/
def negativeArtanhSquareExponent (y : Q') (stage : Nat) : Q' :=
  (-(CRealLog.partialSum y stage + CRealLog.partialSum y stage)) *
    ((1 : Q') + 1)

/-- The universal artanh-square exponent is pointwise nonnegative on the
negative branch. -/
theorem negativeArtanhSquareExponent_nonnegative
    (y : Q') (hy : y < (0 : Q')) (stage : Nat) :
    (0 : Q') <= negativeArtanhSquareExponent y stage := by
  have hyNonpositive : y <= (0 : Q') := Q'.le_of_lt hy
  have hpartial : CRealLog.partialSum y stage <= (0 : Q') := by
    have hanti := CRealLog.partialSum_anti_of_nonpos y hyNonpositive 0 stage
    rw [CRealLog.partialSum_zero, Nat.zero_add] at hanti
    exact hanti
  have hsum : CRealLog.partialSum y stage + CRealLog.partialSum y stage <=
      (0 : Q') :=
    Q'.le_trans' _ _ _ (Q'.add_le_add hpartial hpartial)
      (Q'.le_of_eqv (by decide : ((0 : Q') + 0).eqv 0))
  exact Q'.mul_nonneg _ _ (Q'.nonneg_neg_of_nonpos hsum) (by decide)

/-- The family-independent analytic evaluation at one negative artanh
coordinate. -/
structure NegativeWindowArtanhSquareEulerEvaluation
    (y : Q') (hy : y < (0 : Q'))
    (_hyb : Q'.abs y <= CRealLog.recipOdd 1) : Type 1 where
  exponentialConverges : CReal.ConvergesTo
    (fun stage => ExpNeg.expNeg
      (negativeArtanhSquareExponent y stage)
      (negativeArtanhSquareExponent_nonnegative y hy stage))
    (CReal.ofQ' (artanhRatio y hy * artanhRatio y hy))

/-- One uniform analytic compiler for the entire negative direct artanh
window.  It contains no logarithm, mantissa, Wilson datum, cutoff family, or
continuum structure. -/
structure NegativeWindowArtanhSquareEulerCompiler : Type 2 where
  evaluate :
    (y : Q') -> (hy : y < (0 : Q')) ->
    (hyb : Q'.abs y <= CRealLog.recipOdd 1) ->
    NegativeWindowArtanhSquareEulerEvaluation y hy hyb

/-- The inverse Mobius transform recovers the original rational exactly:
if `y = (m-1)/(m+1)`, then `(1+y)/(1-y) = m`.  The proof uses only the positive
reciprocal law and commutative-ring normalization in `Q'`. -/
theorem artanhRatio_yOf_eqv
    (m : Q') (hm1 : (0 : Q') < m + 1)
    (hy : CRealLog.yOf m hm1 < (0 : Q')) :
    (artanhRatio (CRealLog.yOf m hm1) hy).eqv m := by
  let d : Q' := m + 1
  let r : Q' := Q'.recipPos d hm1
  let y : Q' := (m + -1) * r
  have hdr : (d * r).eqv (1 : Q') := Q'.mul_recipPos_eqv d hm1
  have hplusCollapse : ((m + 1) + (m + -1)).eqv (m + m) := by
    refine Q'.eqv_trans _ ((m + m) + ((1 : Q') + -1)) _
      (Q'.add_swap_inner m 1 m (-1)) ?_
    refine Q'.eqv_trans _ ((m + m) + 0) _ ?_ ?_
    · exact Q'.add_eqv_congr_left (m + m) _ _
        (Q'.add_neg_self_eqv (1 : Q'))
    · exact QPoly.q_add_zero_eqv (m + m)
  have hminusCollapse : ((m + 1) + -(m + -1)).eqv
      ((1 : Q') + 1) := by
    have hneg : (-(m + -1)).eqv ((-m) + 1) := by
      refine Q'.eqv_trans _ ((-m) + -(-1 : Q')) _
        (Q'.neg_add_eqv m (-1)) ?_
      exact Q'.add_eqv_congr_left (-m) _ _
        (Q'.neg_neg_eqv (1 : Q'))
    refine Q'.eqv_trans _ ((m + 1) + ((-m) + 1)) _ ?_ ?_
    · exact Q'.add_eqv_congr_left (m + 1) _ _ hneg
    refine Q'.eqv_trans _ ((m + -m) + ((1 : Q') + 1)) _
      (Q'.add_swap_inner m 1 (-m) 1) ?_
    refine Q'.eqv_trans _ (0 + ((1 : Q') + 1)) _ ?_ ?_
    · exact Q'.add_eqv_congr_right _ _ ((1 : Q') + 1)
        (Q'.add_neg_self_eqv m)
    · exact QPoly.q_zero_add_eqv ((1 : Q') + 1)
  have hnum : ((1 : Q') + y).eqv ((m + m) * r) := by
    refine Q'.eqv_trans _ ((d * r) + y) _ ?_ ?_
    · exact Q'.add_eqv_congr' (Q'.eqv_symm hdr) (Q'.eqv_refl y)
    · refine Q'.eqv_trans _ (((m + 1) + (m + -1)) * r) _ ?_ ?_
      · exact Q'.eqv_symm (Q'.add_mul_eqv (m + 1) (m + -1) r)
      · exact Q'.mul_eqv_congr_right _ _ r hplusCollapse
  have hden : ((1 : Q') + -y).eqv (((1 : Q') + 1) * r) := by
    refine Q'.eqv_trans _ ((d * r) + -y) _ ?_ ?_
    · exact Q'.add_eqv_congr' (Q'.eqv_symm hdr) (Q'.eqv_refl (-y))
    · have hnegMul : (-y).eqv ((-(m + -1)) * r) := by
        dsimp [y]
        exact Q'.eqv_symm (Q'.neg_mul_eqv (m + -1) r)
      refine Q'.eqv_trans _ (((m + 1) * r) + ((-(m + -1)) * r)) _ ?_ ?_
      · exact Q'.add_eqv_congr_left ((m + 1) * r) _ _ hnegMul
      refine Q'.eqv_trans _ (((m + 1) + -(m + -1)) * r) _ ?_ ?_
      · exact Q'.eqv_symm (Q'.add_mul_eqv (m + 1) (-(m + -1)) r)
      · exact Q'.mul_eqv_congr_right _ _ r hminusCollapse
  have hmden : (m * ((1 : Q') + -y)).eqv ((1 : Q') + y) := by
    refine Q'.eqv_trans _ (m * (((1 : Q') + 1) * r)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left m _ _ hden
    · refine Q'.eqv_trans _ ((m + m) * r) _ ?_ ?_
      · refine Q'.eqv_trans _ ((m * ((1 : Q') + 1)) * r) _ ?_ ?_
        · exact Q'.eqv_symm (Q'.mul_assoc_eqv m ((1 : Q') + 1) r)
        · exact Q'.mul_eqv_congr_right _ _ r
            (Q'.eqv_trans _ (m * 1 + m * 1) _
              (Q'.mul_add_eqv m 1 1)
              (Q'.add_eqv_congr'
                (Q'.mul_one_eqv m) (Q'.mul_one_eqv m)))
      · exact Q'.eqv_symm hnum
  change
    ((((1 : Q') + y) *
      Q'.recipPos ((1 : Q') + -y) (one_sub_pos_of_neg y hy)).eqv m)
  refine Q'.eqv_trans _
    ((m * ((1 : Q') + -y)) *
      Q'.recipPos ((1 : Q') + -y) (one_sub_pos_of_neg y hy)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hmden)
  · refine Q'.eqv_trans _
      (m * (((1 : Q') + -y) *
        Q'.recipPos ((1 : Q') + -y) (one_sub_pos_of_neg y hy))) _
      (Q'.mul_assoc_eqv m _ _) ?_
    refine Q'.eqv_trans _ (m * (1 : Q')) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left m _ _
        (Q'.mul_recipPos_eqv ((1 : Q') + -y)
          (one_sub_pos_of_neg y hy))
    · exact Q'.mul_one_eqv m

end YMGap.Constructive.CRealArtanhEulerRatio

#print axioms YMGap.Constructive.CRealArtanhEulerRatio.one_sub_pos_of_neg
#print axioms YMGap.Constructive.CRealArtanhEulerRatio.negativeArtanhSquareExponent_nonnegative
#print axioms YMGap.Constructive.CRealArtanhEulerRatio.artanhRatio_yOf_eqv
