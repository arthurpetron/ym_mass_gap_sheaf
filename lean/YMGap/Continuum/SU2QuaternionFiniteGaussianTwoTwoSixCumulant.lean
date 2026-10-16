/-
# Connected two-quadratic/one-sextic finite Gaussian row cumulant

The square of the actual spatial Cayley cubic coefficient enters the second
heat-action density coefficient as a sextic polynomial.  Term by term, its
connected insertion against two quadratic source observables has row degrees
`2+2+6`.

This leaf records that literal connected subtraction and reduces its degree
ten, degree eight and degree six moments by the checked arbitrary-row Wick
recursion.  Degree two and degree four moments reduce to explicit Gram
contractions.  No determinant expansion, plaquette sum, sign, uniform bound,
ORIGINAL interacting-law comparison, higher-remainder estimate or physical
mass gap is asserted here.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoFourCumulant

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoSixCumulant

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianPositivity
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianIBP
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowWordWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoFourCumulant

local infix:50 " ≈ " => Q'.eqv

/-- Ten-row specialization needed by one sextic insertion against two
quadratic source observables.  It lives here rather than changing the already
audited arbitrary-row Wick leaf. -/
theorem finiteProductGaussian_ten_rows_wick
    (N : Nat) (a b c d e f g h i j : Nat → Q') :
    finiteProductGaussian N
        (finiteGaussianRowWord N [a, b, c, d, e, f, g, h, i, j]) ≈
      finiteGaussianRowWickStep N a [b, c, d, e, f, g, h, i, j] :=
  finiteProductGaussian_row_word_wick N a b [c, d, e, f, g, h, i, j]

/-- Literal connected cumulant of two ordered quadratic row words and one
ordered sextic row word. -/
def finiteGaussianTwoTwoSixCumulant
    (N : Nat) (a b c d e f g h i j : Nat → Q') : Q' :=
  let moment := fun rows =>
    finiteProductGaussian N (finiteGaussianRowWord N rows)
  (((moment [a, b, c, d, e, f, g, h, i, j] +
          -(moment [a, b, c, d] * moment [e, f, g, h, i, j])) +
        -(moment [a, b, e, f, g, h, i, j] * moment [c, d])) +
      -(moment [c, d, e, f, g, h, i, j] * moment [a, b])) +
    2 * (moment [a, b] *
      (moment [c, d] * moment [e, f, g, h, i, j]))

/-- One exact Wick reduction of the connected `2+2+6` row cumulant.  Every
remaining evaluator call occurs inside a strictly lower-degree Wick step. -/
def finiteGaussianTwoTwoSixWickReduction
    (N : Nat) (a b c d e f g h i j : Nat → Q') : Q' :=
  (((finiteGaussianRowWickStep N a [b, c, d, e, f, g, h, i, j] +
          -(finiteRowFourWickValue N a b c d *
            finiteGaussianRowWickStep N e [f, g, h, i, j])) +
        -(finiteGaussianRowWickStep N a [b, e, f, g, h, i, j] *
          finiteRowGram N c d)) +
      -(finiteGaussianRowWickStep N c [d, e, f, g, h, i, j] *
        finiteRowGram N a b)) +
    2 * (finiteRowGram N a b *
      (finiteRowGram N c d *
        finiteGaussianRowWickStep N e [f, g, h, i, j]))

private theorem mul_congr {left left' right right' : Q'}
    (hleft : left ≈ left') (hright : right ≈ right') :
    left * right ≈ left' * right' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hleft)
    (Q'.mul_eqv_congr_left _ _ _ hright)

/-- The abstract polynomial third cumulant of two quadratic row blocks and
one sextic row block is exactly the ordered `2+2+6` row cumulant above. -/
theorem finiteGaussianThirdCumulant_row_blocks_six
    (N : Nat) (a b c d e f g h i j : Nat → Q') :
    finiteGaussianThirdCumulant N
        (finiteGaussianRowWord N [a, b])
        (finiteGaussianRowWord N [c, d])
        (finiteGaussianRowWord N [e, f, g, h, i, j]) ≈
      finiteGaussianTwoTwoSixCumulant N a b c d e f g h i j := by
  let left := finiteGaussianRowWord N [a, b]
  let right := finiteGaussianRowWord N [c, d]
  let insertion := finiteGaussianRowWord N [e, f, g, h, i, j]
  have hpq : RatPolyCoeffEqv (polyMul left right)
      (finiteGaussianRowWord N [a, b, c, d]) :=
    finiteGaussianRowWord_append_nonempty N a c [b] [d]
  have hpr : RatPolyCoeffEqv (polyMul left insertion)
      (finiteGaussianRowWord N [a, b, e, f, g, h, i, j]) :=
    finiteGaussianRowWord_append_nonempty N a e [b] [f, g, h, i, j]
  have hqr : RatPolyCoeffEqv (polyMul right insertion)
      (finiteGaussianRowWord N [c, d, e, f, g, h, i, j]) :=
    finiteGaussianRowWord_append_nonempty N c e [d] [f, g, h, i, j]
  have hpqr : RatPolyCoeffEqv (polyMul (polyMul left right) insertion)
      (finiteGaussianRowWord N [a, b, c, d, e, f, g, h, i, j]) :=
    RatPolyCoeffEqv.trans (hpq.mul_right insertion)
      (finiteGaussianRowWord_append_nonempty N a e [b, c, d]
        [f, g, h, i, j])
  have h10 := finiteProductGaussian_coeffEqv N hpqr
  have h4left := finiteProductGaussian_coeffEqv N hpq
  have h8left := finiteProductGaussian_coeffEqv N hpr
  have h8right := finiteProductGaussian_coeffEqv N hqr
  unfold finiteGaussianThirdCumulant finiteGaussianTwoTwoSixCumulant
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr' h10
          (Q'.neg_eqv_congr _ _
            (mul_congr h4left (Q'.eqv_refl _))))
        (Q'.neg_eqv_congr _ _
          (mul_congr h8left (Q'.eqv_refl _))))
      (Q'.neg_eqv_congr _ _
        (mul_congr h8right (Q'.eqv_refl _))))
    (Q'.mul_eqv_congr_left 2 _ _
      (mul_congr (Q'.eqv_refl _)
        (mul_congr (Q'.eqv_refl _) (Q'.eqv_refl _))))

/-- Exact reduction of the connected `2+2+6` row cumulant to checked ten-,
eight- and six-row Wick steps and explicit Gram bases. -/
theorem finiteGaussian_two_two_six_cumulant_wick
    (N : Nat) (a b c d e f g h i j : Nat → Q') :
    finiteGaussianTwoTwoSixCumulant N a b c d e f g h i j ≈
      finiteGaussianTwoTwoSixWickReduction N a b c d e f g h i j := by
  have h10 := finiteProductGaussian_ten_rows_wick
    N a b c d e f g h i j
  have h8left := finiteProductGaussian_eight_rows_wick N a b e f g h i j
  have h8right := finiteProductGaussian_eight_rows_wick N c d e f g h i j
  have h6insertion := finiteProductGaussian_six_rows_wick N e f g h i j
  have h4left := finiteProductGaussian_four_row_word N a b c d
  have h2left := finiteProductGaussian_two_row_word N a b
  have h2right := finiteProductGaussian_two_row_word N c d
  unfold finiteGaussianTwoTwoSixCumulant
    finiteGaussianTwoTwoSixWickReduction finiteRowFourWickValue
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr' h10
          (Q'.neg_eqv_congr _ _ (mul_congr h4left h6insertion)))
        (Q'.neg_eqv_congr _ _ (mul_congr h8left h2right)))
      (Q'.neg_eqv_congr _ _ (mul_congr h8right h2left)))
    (Q'.mul_eqv_congr_left 2 _ _
      (mul_congr h2left (mul_congr h2right h6insertion)))

/-- Direct consumer form: the ordinary polynomial cumulant of two quadratic
row blocks and one sextic row block reduces to the finite Wick expression. -/
theorem finiteGaussianThirdCumulant_row_blocks_six_wick
    (N : Nat) (a b c d e f g h i j : Nat → Q') :
    finiteGaussianThirdCumulant N
        (finiteGaussianRowWord N [a, b])
        (finiteGaussianRowWord N [c, d])
        (finiteGaussianRowWord N [e, f, g, h, i, j]) ≈
      finiteGaussianTwoTwoSixWickReduction N a b c d e f g h i j :=
  Q'.eqv_trans _ _ _
    (finiteGaussianThirdCumulant_row_blocks_six
      N a b c d e f g h i j)
    (finiteGaussian_two_two_six_cumulant_wick
      N a b c d e f g h i j)

end YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoSixCumulant

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoSixCumulant.finiteProductGaussian_ten_rows_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoSixCumulant.finiteGaussianThirdCumulant_row_blocks_six
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoSixCumulant.finiteGaussian_two_two_six_cumulant_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoSixCumulant.finiteGaussianThirdCumulant_row_blocks_six_wick
