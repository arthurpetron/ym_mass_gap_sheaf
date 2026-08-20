/-
M2o -- a constructive quadratic remainder for the direct logarithm.

For a half-window physical separator, put `d = 1 - q` and
`z = |(q - 1)/(q + 1)|`.  The artanh series is controlled directly at the
rational approximation level:

    d <= -log(q) <= d + 3*d^2.

The constant `3` is intentionally relaxed.  Its role is to expose the
quadratic finite-spacing error, not to optimize the elementary logarithm
inequality.  The proof uses the existing `1/9` geometric block estimate and
keeps every modulus explicit; it does not appeal to a classical real
logarithm.
-/

import YMGap.Continuum.PhysicalSeparatorFullLogHalfWindow
import YMGap.Continuum.CRealRationalProxyTracking
import YMGap.Continuum.EventualCRealRationalProxyTracking
import YMGap.Constructive.QPoly
import YMGap.Constructive.RegularCRealArith

namespace YMGap.Continuum.DirectLogQuadraticRemainder

open YMGap.Constructive
open YMGap.Constructive.CRealLog
open YMGap.Continuum
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.PhysicalSeparatorFullLogRate
open YMGap.Continuum.PhysicalSeparatorFullLogHalfWindow
open YMGap.Continuum.PhysicalSeparatorHalfWindow
open YMGap.Continuum.CRealRationalProxyTracking
open YMGap.Continuum.EventualCRealRationalProxyTracking

/-! ## 1. A quadratic block bound for the artanh tail -/

/-- The first omitted magnitude term is at most `1/9 * |y|^2` on the
artanh window. -/
theorem termAbs_one_le_oneNinth_square (y : Q')
    (hy : Q'.abs y <= recipOdd 1) :
    termAbs y 1 <= oneNinth * (Q'.abs y * Q'.abs y) := by
  let z := Q'.abs y
  have hz : (0 : Q') <= z := Q'.abs_nonneg y
  have hzsq : (0 : Q') <= z * z := SumOfSquares.q_mul_self_nonneg z
  have hcubic : z ^ (2 * 1 + 1) <= (z * z) * recipOdd 1 := by
    have hraw : (z * z) * z <= (z * z) * recipOdd 1 :=
      Q'.mul_le_mul_of_nonneg_left z (recipOdd 1) (z * z) hy hzsq
    have hpowOne : (z ^ (2 * 0 + 1)).eqv z := by
      show (z * z ^ 0).eqv z
      exact Q'.mul_one_eqv z
    have hcubicEq : (z ^ (2 * 1 + 1)).eqv ((z * z) * z) :=
      Q'.eqv_trans _ _ _ (pow_odd_step_eqv z 0)
        (Q'.mul_eqv_congr_left (z * z) _ _ hpowOne)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv hcubicEq) hraw
  have hscaled :
      z ^ (2 * 1 + 1) * recipOdd 1 <=
        ((z * z) * recipOdd 1) * recipOdd 1 :=
    Q'.mul_le_mul_of_nonneg_right _ _ (recipOdd 1) hcubic
      (recipOdd_nonneg 1)
  have hcollapse :
      (((z * z) * recipOdd 1) * recipOdd 1).eqv
        (oneNinth * (z * z)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (z * z) (recipOdd 1) (recipOdd 1)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (z * z)
        (recipOdd 1 * recipOdd 1) oneNinth (by decide)) ?_
    exact Q'.mul_comm_eqv (z * z) oneNinth
  exact Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hcollapse)

/-- The square of the artanh argument closes the `1/9` tail recurrence from
the first omitted term onward. -/
theorem termAbs_one_square_recurrence (y : Q')
    (hy : Q'.abs y <= recipOdd 1) :
    termAbs y 1 + oneNinth * (Q'.abs y * Q'.abs y) <=
      Q'.abs y * Q'.abs y := by
  let zsq := Q'.abs y * Q'.abs y
  have hzsq : (0 : Q') <= zsq := SumOfSquares.q_mul_self_nonneg (Q'.abs y)
  have hterm := termAbs_one_le_oneNinth_square y hy
  have hadd :
      termAbs y 1 + oneNinth * zsq <=
        oneNinth * zsq + oneNinth * zsq :=
    Q'.add_le_add_right _ _ (oneNinth * zsq) hterm
  have hcoeff : oneNinth + oneNinth <= (1 : Q') := by decide
  have hscale : (oneNinth + oneNinth) * zsq <= (1 : Q') * zsq :=
    Q'.mul_le_mul_of_nonneg_right _ _ zsq hcoeff hzsq
  have hleft :
      (oneNinth * zsq + oneNinth * zsq).eqv
        ((oneNinth + oneNinth) * zsq) :=
    Q'.eqv_symm (ExpNeg.add_mul_eqv oneNinth oneNinth zsq)
  exact Q'.le_trans' _ _ _ hadd
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hscale (Q'.le_of_eqv (Q'.one_mul_eqv zsq))))

/-- Every finite artanh tail after the linear term is bounded by `|y|^2`. -/
theorem blockAbs_one_le_square (y : Q')
    (hy : Q'.abs y <= recipOdd 1) (length : Nat) :
    blockAbs y 1 length <= Q'.abs y * Q'.abs y :=
  blockAbs_le y hy (Q'.abs y * Q'.abs y) 1
    (SumOfSquares.q_mul_self_nonneg (Q'.abs y))
    (termAbs_one_square_recurrence y hy) length

/-- A negative partial sum is bounded by its linear magnitude plus the
quadratic tail.  This statement is sign-free because `-y <= |y|`. -/
theorem neg_partialSum_le_abs_add_square (y : Q')
    (hy : Q'.abs y <= recipOdd 1) (n : Nat) :
    -(partialSum y n) <= Q'.abs y + Q'.abs y * Q'.abs y := by
  cases n with
  | zero =>
      have hnonneg : (0 : Q') <= Q'.abs y + Q'.abs y * Q'.abs y :=
        Q'.zero_le_add _ _ (Q'.abs_nonneg y)
          (SumOfSquares.q_mul_self_nonneg (Q'.abs y))
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.neg_eqv_congr 0 0 (Q'.eqv_refl 0))) hnonneg
  | succ length =>
      have hblock := block_lower y 1 length
      have htail := blockAbs_one_le_square y hy length
      have hwithSquare :
          partialSum y 1 <=
            partialSum y (1 + length) +
              (Q'.abs y * Q'.abs y) :=
        Q'.le_trans' _ _ _ hblock
          (Q'.add_le_add_left _ _ _ htail)
      have hneg :
          -(partialSum y (1 + length)) <=
            -(partialSum y 1) + (Q'.abs y * Q'.abs y) :=
        Q'.neg_le_neg_add hwithSquare
      have hlinearEq : (-(partialSum y 1)).eqv (-y) := by
        have hfirst : (partialSum y 1).eqv y := by
          refine Q'.eqv_trans _ _ _ ?_ (term_zero_eqv_self y)
          show ((0 : Q') + term y 0).eqv (term y 0)
          exact Q'.eqv_of_eq (Q'.zero_add' (term y 0))
        exact Q'.neg_eqv_congr _ _ hfirst
      have hlinear : -(partialSum y 1) <= Q'.abs y :=
        Q'.le_trans' _ _ _ (Q'.le_of_eqv hlinearEq) (Q'.neg_le_abs y)
      have hfinal :
          -(partialSum y 1) + (Q'.abs y * Q'.abs y) <=
            Q'.abs y + (Q'.abs y * Q'.abs y) :=
        Q'.add_le_add_right _ _ _ hlinear
      simpa only [Nat.add_comm] using Q'.le_trans' _ _ _ hneg hfinal

/-- On a nonpositive argument, retain the signed linear term instead of
relaxing it to `|y|`.  This is the form needed to recover leading coefficient
one in the logarithmic remainder. -/
theorem neg_partialSum_le_neg_term_add_square (y : Q')
    (hy : Q'.abs y <= recipOdd 1) (hyNonpos : y <= (0 : Q')) (n : Nat) :
    -(partialSum y n) <= -(term y 0) + Q'.abs y * Q'.abs y := by
  cases n with
  | zero =>
      have htermNonpos : term y 0 <= (0 : Q') :=
        term_nonpos_of_nonpos y hyNonpos 0
      have hnegTerm : (0 : Q') <= -(term y 0) := by
        have := Q'.neg_le_neg htermNonpos
        exact Q'.le_trans' _ _ _
          (Q'.le_of_eqv (Q'.neg_eqv_congr 0 0 (Q'.eqv_refl 0))) this
      have hsum : (0 : Q') <= -(term y 0) + Q'.abs y * Q'.abs y :=
        Q'.zero_le_add _ _ hnegTerm
          (SumOfSquares.q_mul_self_nonneg (Q'.abs y))
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.neg_eqv_congr 0 0 (Q'.eqv_refl 0))) hsum
  | succ length =>
      have hblock := block_lower y 1 length
      have htail := blockAbs_one_le_square y hy length
      have hwithSquare :
          partialSum y 1 <=
            partialSum y (1 + length) +
              (Q'.abs y * Q'.abs y) :=
        Q'.le_trans' _ _ _ hblock
          (Q'.add_le_add_left _ _ _ htail)
      have hneg :
          -(partialSum y (1 + length)) <=
            -(partialSum y 1) + (Q'.abs y * Q'.abs y) :=
        Q'.neg_le_neg_add hwithSquare
      have hfirst : (partialSum y 1).eqv (term y 0) := by
        show ((0 : Q') + term y 0).eqv (term y 0)
        exact Q'.eqv_of_eq (Q'.zero_add' (term y 0))
      have hreplace :
          (-(partialSum y 1) + Q'.abs y * Q'.abs y).eqv
            (-(term y 0) + Q'.abs y * Q'.abs y) :=
        Q'.add_eqv_congr_right _ _ _ (Q'.neg_eqv_congr _ _ hfirst)
      simpa only [Nat.add_comm] using
        Q'.le_trans' _ _ _ hneg (Q'.le_of_eqv hreplace)

/-! ## 2. The exact linear coefficient from `y = -d/(2-d)` -/

/-- Evaluation of the linear polynomial `1 + X`. -/
private theorem eval_one_add (x : Q') :
    (QPoly.eval [1, 1] x).eqv (1 + x) := by
  show (1 + x * (1 + x * 0)).eqv (1 + x)
  have hz : (x * (0 : Q')).eqv 0 := QPoly.q_mul_zero x
  have hi : (1 + x * (0 : Q')).eqv 1 :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left 1 _ 0 hz)
      (QPoly.q_add_zero_eqv 1)
  have hx : (x * (1 + x * (0 : Q'))).eqv x :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left x _ _ hi)
      (Q'.mul_one_eqv x)
  exact Q'.add_eqv_congr_left 1 _ _ hx

/-- Evaluation of the linear polynomial `2 - X`. -/
private theorem eval_two_sub (x : Q') :
    (QPoly.eval [2, -1] x).eqv (2 + -x) := by
  show (2 + x * (-1 + x * 0)).eqv (2 + -x)
  have hz : (x * (0 : Q')).eqv 0 := QPoly.q_mul_zero x
  have hi : (-1 + x * (0 : Q')).eqv (-1) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (-1) _ 0 hz)
      (QPoly.q_add_zero_eqv (-1))
  have hxneg : (x * (-1)).eqv (-x) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv x 1) ?_
    exact Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv x)
  have hx : (x * (-1 + x * (0 : Q'))).eqv (-x) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left x _ _ hi) hxneg
  exact Q'.add_eqv_congr_left 2 _ _ hx

/-- Evaluation of `2 + X - X^2`. -/
private theorem eval_two_add_sub_square (x : Q') :
    (QPoly.eval [2, 1, -1] x).eqv
      (2 + (x + -(x * x))) := by
  show (2 + x * (1 + x * (-1 + x * 0))).eqv
    (2 + (x + -(x * x)))
  have hz : (x * (0 : Q')).eqv 0 := QPoly.q_mul_zero x
  have hminusOne : (-1 + x * (0 : Q')).eqv (-1) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (-1) _ 0 hz)
      (QPoly.q_add_zero_eqv (-1))
  have hxneg : (x * (-1 + x * (0 : Q'))).eqv (-x) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left x _ _ hminusOne) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv x 1) ?_
    exact Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv x)
  have hinner : (1 + x * (-1 + x * 0)).eqv (1 + -x) :=
    Q'.add_eqv_congr_left 1 _ _ hxneg
  have hproduct : (x * (1 + x * (-1 + x * 0))).eqv
      (x + -(x * x)) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left x _ _ hinner) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv x 1 (-x)) ?_
    refine Q'.add_eqv_congr' (Q'.mul_one_eqv x) ?_
    exact Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv x x)
      (Q'.eqv_refl (-(x * x)))
  exact Q'.add_eqv_congr_left 2 _ _ hproduct

/-- Elementary polynomial identity `(1+d)(2-d) = 2+d-d^2`, checked by the
constructive `Q'` polynomial normalizer. -/
private theorem one_add_mul_two_sub_eqv (d : Q') :
    ((1 + d) * (2 + -d)).eqv (2 + (d + -(d * d))) := by
  have hpoly :
      (QPoly.eval (QPoly.pmul [1, 1] [2, -1]) d).eqv
        (QPoly.eval [2, 1, -1] d) :=
    QPoly.poly_eqv _ _ d (by decide)
  have hleft :
      (QPoly.eval (QPoly.pmul [1, 1] [2, -1]) d).eqv
        ((1 + d) * (2 + -d)) :=
    Q'.eqv_trans _ _ _ (QPoly.eval_pmul [1, 1] [2, -1] d)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (eval_one_add d))
        (Q'.mul_eqv_congr_left (1 + d) _ _ (eval_two_sub d)))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hleft)
    (Q'.eqv_trans _ _ _ hpoly (eval_two_add_sub_square d))

/-- A physical margin lies in `[0,1]`. -/
theorem physMargin_le_one (P : PhysicalSeparator) (j : Nat) :
    P.physMargin j <= (1 : Q') := by
  have hneg : -(P.sep j) <= (0 : Q') := by
    have h := Q'.neg_le_neg (P.sep_nonneg j)
    exact Q'.le_trans' _ _ _ h
      (Q'.le_of_eqv (Q'.neg_eqv_congr 0 0 (Q'.eqv_refl 0)))
  unfold PhysicalSeparator.physMargin
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add_left 1 (-(P.sep j)) 0 hneg)
    (Q'.le_of_eqv (QPoly.q_add_zero_eqv 1))

/-- `q+1` is represented by `2-d` for `d=1-q`. -/
theorem sep_add_one_eqv_two_sub_margin (P : PhysicalSeparator) (j : Nat) :
    (P.sep j + 1).eqv (2 + -(P.physMargin j)) := by
  have hneg : (-(P.physMargin j)).eqv (-1 + P.sep j) := by
    unfold PhysicalSeparator.physMargin
    refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv 1 (-(P.sep j))) ?_
    exact Q'.add_eqv_congr_left (-1) _ _ (Q'.neg_neg_eqv (P.sep j))
  have hright : (2 + -(P.physMargin j)).eqv (P.sep j + 1) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left 2 _ _ hneg) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv 2 (-1) (P.sep j))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right (2 + -1) 1 (P.sep j) (by decide)) ?_
    exact Q'.add_comm_eqv 1 (P.sep j)
  exact Q'.eqv_symm hright

/-- The exact reciprocal identity implies
`2/(q+1) <= 1 + (1-q)`.  This is the source of the leading coefficient one
in the quadratic logarithm estimate. -/
theorem twice_reciprocal_sep_add_one_le_one_add_margin
    (P : PhysicalSeparator) (j : Nat) :
    Q'.recipPos (P.sep j + 1) (separatorPlusOne_pos P j) +
        Q'.recipPos (P.sep j + 1) (separatorPlusOne_pos P j) <=
      1 + P.physMargin j := by
  let d := P.physMargin j
  let denominator := P.sep j + 1
  let r := Q'.recipPos denominator (separatorPlusOne_pos P j)
  have hd0 : (0 : Q') <= d := Q'.le_of_lt (P.physMargin_pos j)
  have hd1 : d <= (1 : Q') := physMargin_le_one P j
  have hdsq : d * d <= d := by
    have hraw := Q'.mul_le_mul_of_nonneg_right d 1 d hd1 hd0
    exact Q'.le_trans' _ _ _ hraw (Q'.le_of_eqv (Q'.one_mul_eqv d))
  have hdiff : (0 : Q') <= d + -(d * d) := Q'.sub_nonneg_of_le hdsq
  have hbase : (2 : Q') <= 2 + (d + -(d * d)) :=
    Q'.add_le_self_of_nonneg 2 (d + -(d * d)) hdiff
  have hproductEq :
      ((1 + d) * denominator).eqv (2 + (d + -(d * d))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (1 + d) denominator (2 + -d) ?_) ?_
    · exact sep_add_one_eqv_two_sub_margin P j
    · exact one_add_mul_two_sub_eqv d
  have hdenominator : (2 : Q') <= (1 + d) * denominator :=
    Q'.le_trans' _ _ _ hbase (Q'.ge_of_eqv hproductEq)
  have hdiv : Q'.divPos 2 denominator (separatorPlusOne_pos P j) <= 1 + d :=
    Q'.divPos_le_of_le_mul 2 denominator (separatorPlusOne_pos P j) hdenominator
  have hrr : (r + r).eqv
      (Q'.divPos 2 denominator (separatorPlusOne_pos P j)) := by
    unfold Q'.divPos
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.eqv_symm (Q'.one_mul_eqv r))
        (Q'.eqv_symm (Q'.one_mul_eqv r))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (ExpNeg.add_mul_eqv 1 1 r)) ?_
    exact Q'.mul_eqv_congr_right (1 + 1) 2 r (by decide)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hrr) hdiv

/-- The doubled linear artanh term is at most `d+d^2`. -/
theorem neg_two_term_le_margin_add_square
    (P : PhysicalSeparator) (j : Nat) :
    -(term (yOf (P.sep j) (separatorPlusOne_pos P j)) 0 +
        term (yOf (P.sep j) (separatorPlusOne_pos P j)) 0) <=
      P.physMargin j + P.physMargin j * P.physMargin j := by
  let d := P.physMargin j
  let r := Q'.recipPos (P.sep j + 1) (separatorPlusOne_pos P j)
  let y := yOf (P.sep j) (separatorPlusOne_pos P j)
  have hd0 : (0 : Q') <= d := Q'.le_of_lt (P.physMargin_pos j)
  have hcoeff : r + r <= 1 + d :=
    twice_reciprocal_sep_add_one_le_one_add_margin P j
  have hscaled : (r + r) * d <= (1 + d) * d :=
    Q'.mul_le_mul_of_nonneg_right _ _ d hcoeff hd0
  have hright : ((1 + d) * d).eqv (d + d * d) := by
    refine Q'.eqv_trans _ _ _ (ExpNeg.add_mul_eqv 1 d d) ?_
    exact Q'.add_eqv_congr_right (1 * d) d (d * d) (Q'.one_mul_eqv d)
  have hnum : (P.sep j + -1).eqv (-d) := by
    unfold d PhysicalSeparator.physMargin
    refine Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.neg_add_eqv 1 (-(P.sep j))) ?_)
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (-1) (-(-(P.sep j))) (P.sep j)
        (Q'.neg_neg_eqv (P.sep j))) ?_
    exact Q'.add_comm_eqv (-1) (P.sep j)
  have hy : y.eqv (-(d * r)) := by
    unfold y CRealLog.yOf r
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (P.sep j + -1) (-d) _ hnum) ?_
    exact Q'.neg_mul_eqv d
      (Q'.recipPos (P.sep j + 1) (separatorPlusOne_pos P j))
  have hterm : (term y 0).eqv (-(d * r)) :=
    Q'.eqv_trans _ _ _ (term_zero_eqv_self y) hy
  have hleft : (-(term y 0 + term y 0)).eqv ((r + r) * d) := by
    refine Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ (Q'.add_eqv_congr' hterm hterm)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv (-(d * r)) (-(d * r))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_neg_eqv (d * r))
        (Q'.neg_neg_eqv (d * r))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.mul_comm_eqv d r) (Q'.mul_comm_eqv d r)) ?_
    exact Q'.eqv_symm (ExpNeg.add_mul_eqv r r d)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright))

/-- The artanh argument magnitude is bounded by the physical margin. -/
theorem abs_yOf_sep_le_margin (P : PhysicalSeparator) (j : Nat) :
    Q'.abs (yOf (P.sep j) (separatorPlusOne_pos P j)) <= P.physMargin j := by
  have hsepOne : (1 : Q') <= P.sep j + 1 := by
    have h := Q'.add_le_add_left 1 0 (P.sep j) (P.sep_nonneg j)
    rw [Q'.add_zero'] at h
    exact Q'.le_trans' _ _ _ h
      (Q'.le_of_eqv (Q'.add_comm_eqv 1 (P.sep j)))
  exact Q'.le_trans' _ _ _
    (EffMassConvergence.absYOf_le
      (P.sep j) (separatorPlusOne_pos P j) hsepOne)
    (Q'.le_of_eqv (abs_sep_sub_one_eqv_margin P j))

/-! ## 3. Approximation-level logarithm and rate bounds -/

/-- Three copies of the margin square, retained in an addition-only form so
no normalization of rational representatives is needed. -/
def quadraticLogRemainder (P : PhysicalSeparator) (j : Nat) : Q' :=
  let square := P.physMargin j * P.physMargin j
  square + (square + square)

theorem quadraticLogRemainder_nonneg (P : PhysicalSeparator) (j : Nat) :
    (0 : Q') <= quadraticLogRemainder P j := by
  let square := P.physMargin j * P.physMargin j
  have hsquare : (0 : Q') <= square :=
    SumOfSquares.q_mul_self_nonneg (P.physMargin j)
  exact Q'.zero_le_add _ _ hsquare (Q'.zero_le_add _ _ hsquare hsquare)

/-- Every rational approximation of the direct logarithmic mass satisfies
the quadratic upper estimate. -/
theorem directLogMassAt_approx_le_margin_add_quadratic
    (P : PhysicalSeparator) (j n : Nat)
    (hhalf : HalfPow.half <= P.sep j) :
    (directLogMassAt P j hhalf).approx n <=
      P.physMargin j + quadraticLogRemainder P j := by
  let y := yOf (P.sep j) (separatorPlusOne_pos P j)
  let zsquare := Q'.abs y * Q'.abs y
  let dsquare := P.physMargin j * P.physMargin j
  have hyWindow : Q'.abs y <= recipOdd 1 := directWindowAt P j hhalf
  have hyNonpos : y <= (0 : Q') :=
    Q'.le_of_lt (YMGap.Continuum.yOf_sep_neg
      (P.sep j) (separatorPlusOne_pos P j) (P.sep_lt_one j))
  have hpart := neg_partialSum_le_neg_term_add_square y hyWindow hyNonpos n
  have hsum :
      -(partialSum y n) + -(partialSum y n) <=
        (-(term y 0) + zsquare) + (-(term y 0) + zsquare) :=
    Q'.add_le_add hpart hpart
  have hleft :
      (-((partialSum y n) + (partialSum y n))).eqv
        (-(partialSum y n) + -(partialSum y n)) :=
    Q'.neg_add_eqv (partialSum y n) (partialSum y n)
  have hregroup :
      ((-(term y 0) + zsquare) + (-(term y 0) + zsquare)).eqv
        (-(term y 0 + term y 0) + (zsquare + zsquare)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_swap_inner (-(term y 0)) zsquare (-(term y 0)) zsquare) ?_
    exact Q'.add_eqv_congr_right
      (-(term y 0) + -(term y 0)) (-(term y 0 + term y 0))
      (zsquare + zsquare)
      (Q'.eqv_symm (Q'.neg_add_eqv (term y 0) (term y 0)))
  have hlinear : -(term y 0 + term y 0) <=
      P.physMargin j + dsquare :=
    neg_two_term_le_margin_add_square P j
  have hz : Q'.abs y <= P.physMargin j := abs_yOf_sep_le_margin P j
  have hz0 : (0 : Q') <= Q'.abs y := Q'.abs_nonneg y
  have hd0 : (0 : Q') <= P.physMargin j :=
    Q'.le_of_lt (P.physMargin_pos j)
  have hzsquare : zsquare <= dsquare := by
    have hfirst : Q'.abs y * Q'.abs y <= P.physMargin j * Q'.abs y :=
      Q'.mul_le_mul_of_nonneg_right _ _ (Q'.abs y) hz hz0
    have hsecond : P.physMargin j * Q'.abs y <=
        P.physMargin j * P.physMargin j :=
      Q'.mul_le_mul_of_nonneg_left _ _ (P.physMargin j) hz hd0
    exact Q'.le_trans' _ _ _ hfirst hsecond
  have htail : zsquare + zsquare <= dsquare + dsquare :=
    Q'.add_le_add hzsquare hzsquare
  have hcombined :
      -(term y 0 + term y 0) + (zsquare + zsquare) <=
        (P.physMargin j + dsquare) + (dsquare + dsquare) :=
    Q'.add_le_add hlinear htail
  have hfinal :
      ((P.physMargin j + dsquare) + (dsquare + dsquare)).eqv
        (P.physMargin j + quadraticLogRemainder P j) := by
    unfold quadraticLogRemainder dsquare
    exact Q'.add_assoc_eqv (P.physMargin j) _ _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hsum
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hregroup)
        (Q'.le_trans' _ _ _ hcombined (Q'.le_of_eqv hfinal))))

/-- From approximation index one onward, the direct logarithmic mass is at
least the linear margin. -/
theorem margin_le_directLogMassAt_approx_of_one_le
    (P : PhysicalSeparator) (j n : Nat)
    (hhalf : HalfPow.half <= P.sep j) (hn : 1 <= n) :
    P.physMargin j <= (directLogMassAt P j hhalf).approx n := by
  let y := yOf (P.sep j) (separatorPlusOne_pos P j)
  have hyNonpos : y <= (0 : Q') :=
    Q'.le_of_lt (YMGap.Continuum.yOf_sep_neg
      (P.sep j) (separatorPlusOne_pos P j) (P.sep_lt_one j))
  obtain ⟨length, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hanti : partialSum y (1 + length) <= partialSum y 1 :=
    partialSum_anti_of_nonpos y hyNonpos 1 length
  have hneg : -(partialSum y 1) <= -(partialSum y (1 + length)) :=
    Q'.neg_le_neg hanti
  have hdouble :
      -(partialSum y 1) + -(partialSum y 1) <=
        -(partialSum y (1 + length)) + -(partialSum y (1 + length)) :=
    Q'.add_le_add hneg hneg
  have hfirst : (partialSum y 1).eqv (term y 0) := by
    show ((0 : Q') + term y 0).eqv (term y 0)
    exact Q'.eqv_of_eq (Q'.zero_add' (term y 0))
  have hlinearEq : (-(term y 0 + term y 0)).eqv
      (-(partialSum y 1) + -(partialSum y 1)) := by
    refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv (term y 0) (term y 0)) ?_
    exact Q'.add_eqv_congr'
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hfirst))
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hfirst))
  have htargetEq :
      (-(partialSum y (1 + length)) + -(partialSum y (1 + length))).eqv
        (-((partialSum y (1 + length)) + partialSum y (1 + length))) :=
    Q'.eqv_symm
      (Q'.neg_add_eqv (partialSum y (1 + length)) (partialSum y (1 + length)))
  exact Q'.le_trans' _ _ _ (margin_le_neg_two_y P j)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hlinearEq)
      (Q'.le_trans' _ _ _ hdouble (Q'.le_of_eqv htargetEq)))

/-- The physical-rate error `3(1-q_j)^2/a_j`. -/
def quadraticRateError
    (P : PhysicalSeparator) (A : PhysicalSpacing) (j : Nat) : Q' :=
  Q'.divPos (quadraticLogRemainder P j) (A.spacing j) (A.spacing_pos j)

theorem quadraticRateError_nonneg
    (P : PhysicalSeparator) (A : PhysicalSpacing) (j : Nat) :
    (0 : Q') <= quadraticRateError P A j :=
  Q'.mul_nonneg _ _ (quadraticLogRemainder_nonneg P j)
    (Q'.le_of_lt (Q'.recipPos_pos (A.spacing j) (A.spacing_pos j)))

/-- The exact full-range rate is at most the margin proxy plus the quadratic
rate error at every approximation index on the half-window. -/
theorem fullMassRate_approx_le_marginRate_add_quadraticRateError
    (P : PhysicalSeparator) (A : PhysicalSpacing) (j n : Nat)
    (hhalf : HalfPow.half <= P.sep j) :
    (fullMassRate P A j).approx n <=
      marginRate P A j + quadraticRateError P A j := by
  let reciprocal := reciprocalSpacing A j
  have hlog := directLogMassAt_approx_le_margin_add_quadratic
    P j n hhalf
  have hscaled :
      (directLogMassAt P j hhalf).approx n * reciprocal <=
        (P.physMargin j + quadraticLogRemainder P j) * reciprocal :=
    Q'.mul_le_mul_of_nonneg_right _ _ reciprocal hlog
      (Q'.le_of_lt (reciprocalSpacing_pos A j))
  have hfull := fullMassRate_approx_eqv_directMassRateAt P A j n hhalf
  have htarget :
      ((P.physMargin j + quadraticLogRemainder P j) * reciprocal).eqv
        (marginRate P A j + quadraticRateError P A j) := by
    refine Q'.eqv_trans _ _ _
      (ExpNeg.add_mul_eqv (P.physMargin j)
        (quadraticLogRemainder P j) reciprocal) ?_
    unfold marginRate quadraticRateError reciprocal reciprocalSpacing Q'.divPos
    exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfull)
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv htarget))

/-- From approximation index one onward, the exact full-range rate dominates
the rational margin rate on the half-window. -/
theorem marginRate_le_fullMassRate_approx_of_one_le
    (P : PhysicalSeparator) (A : PhysicalSpacing) (j n : Nat)
    (hhalf : HalfPow.half <= P.sep j) (hn : 1 <= n) :
    marginRate P A j <= (fullMassRate P A j).approx n := by
  let reciprocal := reciprocalSpacing A j
  have hlog := margin_le_directLogMassAt_approx_of_one_le P j n hhalf hn
  have hscaled :
      P.physMargin j * reciprocal <=
        (directLogMassAt P j hhalf).approx n * reciprocal :=
    Q'.mul_le_mul_of_nonneg_right _ _ reciprocal hlog
      (Q'.le_of_lt (reciprocalSpacing_pos A j))
  have hproxy : (marginRate P A j).eqv (P.physMargin j * reciprocal) := by
    unfold marginRate reciprocal reciprocalSpacing Q'.divPos
    exact Q'.eqv_refl _
  have hfull := fullMassRate_approx_eqv_directMassRateAt P A j n hhalf
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hproxy)
    (Q'.le_trans' _ _ _ hscaled (Q'.ge_of_eqv hfull))

/-- A uniform half-window supplies the exact modulus-carrying approximation
of the full logarithmic rate by the rational margin rate, with explicit
quadratic finite-spacing error. -/
def fullMassRateMarginProxyApproximation
    (P : PhysicalSeparator) (A : PhysicalSpacing)
    (H : SeparatorHalfWindow P) :
    CRealRationalProxyApproximation
      (fullMassRate P A) (marginRate P A) (quadraticRateError P A) where
  proxyRate := fun _ _ => 1
  approximates := by
    intro j epsilon hepsilon k hk
    have hupper :=
      fullMassRate_approx_le_marginRate_add_quadraticRateError
        P A j k (H.sep_ge_half j)
    have hlower := marginRate_le_fullMassRate_approx_of_one_le
      P A j k (H.sep_ge_half j) hk
    have hepsilon0 : (0 : Q') <= epsilon := Q'.le_of_lt hepsilon
    constructor
    · exact Q'.le_trans' _ _ _ hupper
        (Q'.add_le_self_of_nonneg
          (marginRate P A j + quadraticRateError P A j)
          epsilon hepsilon0)
    · have herror0 := quadraticRateError_nonneg P A j
      have hwithError :
          (fullMassRate P A j).approx k <=
            (fullMassRate P A j).approx k + quadraticRateError P A j :=
        Q'.add_le_self_of_nonneg _ _ herror0
      have hwithEpsilon :
          (fullMassRate P A j).approx k + quadraticRateError P A j <=
            ((fullMassRate P A j).approx k + quadraticRateError P A j) + epsilon :=
        Q'.add_le_self_of_nonneg _ _ hepsilon0
      exact Q'.le_trans' _ _ _ hlower
        (Q'.le_trans' _ _ _ hwithError hwithEpsilon)

/-- An eventual half-window gives the same exact quadratic proxy comparison
on the named cutoff tail.  This is the form used by AF/Faraut data, where the
separator approaches one but need not begin in the direct artanh window. -/
def eventualFullMassRateMarginProxyApproximation
    (P : PhysicalSeparator) (A : PhysicalSpacing) (start : Nat)
    (H : EventualSeparatorHalfWindow P start) :
    EventualCRealRationalProxyApproximation
      (fullMassRate P A) (marginRate P A) (quadraticRateError P A) start where
  proxyRate := fun _ _ => 1
  approximates := by
    intro j hj epsilon hepsilon k hk
    have hupper :=
      fullMassRate_approx_le_marginRate_add_quadraticRateError
        P A j k (H.sep_ge_half j hj)
    have hlower := marginRate_le_fullMassRate_approx_of_one_le
      P A j k (H.sep_ge_half j hj) hk
    have hepsilon0 : (0 : Q') <= epsilon := Q'.le_of_lt hepsilon
    constructor
    · exact Q'.le_trans' _ _ _ hupper
        (Q'.add_le_self_of_nonneg
          (marginRate P A j + quadraticRateError P A j)
          epsilon hepsilon0)
    · have herror0 := quadraticRateError_nonneg P A j
      have hwithError :
          (fullMassRate P A j).approx k <=
            (fullMassRate P A j).approx k + quadraticRateError P A j :=
        Q'.add_le_self_of_nonneg _ _ herror0
      have hwithEpsilon :
          (fullMassRate P A j).approx k + quadraticRateError P A j <=
            ((fullMassRate P A j).approx k + quadraticRateError P A j) +
              epsilon :=
        Q'.add_le_self_of_nonneg _ _ hepsilon0
      exact Q'.le_trans' _ _ _ hlower
        (Q'.le_trans' _ _ _ hwithError hwithEpsilon)

end YMGap.Continuum.DirectLogQuadraticRemainder

#print axioms YMGap.Continuum.DirectLogQuadraticRemainder.termAbs_one_le_oneNinth_square
#print axioms YMGap.Continuum.DirectLogQuadraticRemainder.blockAbs_one_le_square
#print axioms YMGap.Continuum.DirectLogQuadraticRemainder.neg_partialSum_le_abs_add_square
#print axioms YMGap.Continuum.DirectLogQuadraticRemainder.neg_two_term_le_margin_add_square
#print axioms YMGap.Continuum.DirectLogQuadraticRemainder.directLogMassAt_approx_le_margin_add_quadratic
#print axioms YMGap.Continuum.DirectLogQuadraticRemainder.margin_le_directLogMassAt_approx_of_one_le
#print axioms YMGap.Continuum.DirectLogQuadraticRemainder.fullMassRateMarginProxyApproximation
#print axioms YMGap.Continuum.DirectLogQuadraticRemainder.eventualFullMassRateMarginProxyApproximation
