/-
# Connected two-quadratic/one-quartic finite Gaussian row cumulant

The normalized Cayley quartic enters the signed source response together with
two quadratic source observables.  Term by term, the required connected
Gaussian insertion is therefore a cumulant of row degrees `2+2+4`.

This leaf records that literal connected subtraction and replaces its degree
eight and degree six raw moments by the checked arbitrary-row Wick recursion,
while replacing every degree two and degree four moment by computed Gram
contractions.  It is the exact finite-row primitive needed before summing the
bulk-source and normalized-Cayley term lists.

No sign, uniform estimate, OLD-center coefficient, ORIGINAL interacting-law
comparison, higher-remainder bound or physical mass gap is asserted here.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianRowWordWick

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoFourCumulant

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianPositivity
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianIBP
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowWordWick

local infix:50 " ≈ " => Q'.eqv

/-- Ordinary third cumulant under the existing finite product-Gaussian
evaluator.  The order of the three polynomial blocks is retained literally. -/
def finiteGaussianThirdCumulant
    (N : Nat) (left right insertion : RatPoly) : Q' :=
  let mean := finiteProductGaussian N
  ((((mean (polyMul (polyMul left right) insertion) +
          -(mean (polyMul left right) * mean insertion)) +
        -(mean (polyMul left insertion) * mean right)) +
      -(mean (polyMul right insertion) * mean left)) +
    2 * (mean left * (mean right * mean insertion)))

/-- Computed four-row Wick value used by the lower-degree cumulant pieces. -/
def finiteRowFourWickValue
    (N : Nat) (a b c d : Nat → Q') : Q' :=
  finiteRowGram N a b * finiteRowGram N c d +
    (finiteRowGram N a c * finiteRowGram N b d +
      finiteRowGram N a d * finiteRowGram N b c)

/-- Literal connected cumulant of two ordered quadratic row words and one
ordered quartic row word. -/
def finiteGaussianTwoTwoFourCumulant
    (N : Nat) (a b c d e f g h : Nat → Q') : Q' :=
  let moment := fun rows =>
    finiteProductGaussian N (finiteGaussianRowWord N rows)
  (((moment [a, b, c, d, e, f, g, h] +
          -(moment [a, b, c, d] * moment [e, f, g, h])) +
        -(moment [a, b, e, f, g, h] * moment [c, d])) +
      -(moment [c, d, e, f, g, h] * moment [a, b])) +
    2 * (moment [a, b] * (moment [c, d] * moment [e, f, g, h]))

/-- One exact Wick reduction of the same connected cumulant.  The only
remaining evaluator calls occur inside strictly lower-degree six-row Wick
steps; repeated use of the generic recursion terminates at the Gram bases. -/
def finiteGaussianTwoTwoFourWickReduction
    (N : Nat) (a b c d e f g h : Nat → Q') : Q' :=
  (((finiteGaussianRowWickStep N a [b, c, d, e, f, g, h] +
          -(finiteRowFourWickValue N a b c d *
            finiteRowFourWickValue N e f g h)) +
        -(finiteGaussianRowWickStep N a [b, e, f, g, h] *
          finiteRowGram N c d)) +
      -(finiteGaussianRowWickStep N c [d, e, f, g, h] *
        finiteRowGram N a b)) +
    2 * (finiteRowGram N a b *
      (finiteRowGram N c d * finiteRowFourWickValue N e f g h))

private theorem mul_congr {left left' right right' : Q'}
    (hleft : left ≈ left') (hright : right ≈ right') :
    left * right ≈ left' * right' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hleft)
    (Q'.mul_eqv_congr_left _ _ _ hright)

/-- The abstract polynomial third cumulant of two quadratic row blocks and
one quartic row block is exactly the ordered `2+2+4` row cumulant above. -/
theorem finiteGaussianThirdCumulant_row_blocks
    (N : Nat) (a b c d e f g h : Nat → Q') :
    finiteGaussianThirdCumulant N
        (finiteGaussianRowWord N [a, b])
        (finiteGaussianRowWord N [c, d])
        (finiteGaussianRowWord N [e, f, g, h]) ≈
      finiteGaussianTwoTwoFourCumulant N a b c d e f g h := by
  let left := finiteGaussianRowWord N [a, b]
  let right := finiteGaussianRowWord N [c, d]
  let insertion := finiteGaussianRowWord N [e, f, g, h]
  have hpq : RatPolyCoeffEqv (polyMul left right)
      (finiteGaussianRowWord N [a, b, c, d]) :=
    finiteGaussianRowWord_append_nonempty N a c [b] [d]
  have hpr : RatPolyCoeffEqv (polyMul left insertion)
      (finiteGaussianRowWord N [a, b, e, f, g, h]) :=
    finiteGaussianRowWord_append_nonempty N a e [b] [f, g, h]
  have hqr : RatPolyCoeffEqv (polyMul right insertion)
      (finiteGaussianRowWord N [c, d, e, f, g, h]) :=
    finiteGaussianRowWord_append_nonempty N c e [d] [f, g, h]
  have hpqr : RatPolyCoeffEqv (polyMul (polyMul left right) insertion)
      (finiteGaussianRowWord N [a, b, c, d, e, f, g, h]) :=
    RatPolyCoeffEqv.trans (hpq.mul_right insertion)
      (finiteGaussianRowWord_append_nonempty N a e [b, c, d] [f, g, h])
  have h8 := finiteProductGaussian_coeffEqv N hpqr
  have h4left := finiteProductGaussian_coeffEqv N hpq
  have h6left := finiteProductGaussian_coeffEqv N hpr
  have h6right := finiteProductGaussian_coeffEqv N hqr
  unfold finiteGaussianThirdCumulant finiteGaussianTwoTwoFourCumulant
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr' h8
          (Q'.neg_eqv_congr _ _
            (mul_congr h4left (Q'.eqv_refl _))))
        (Q'.neg_eqv_congr _ _
          (mul_congr h6left (Q'.eqv_refl _))))
      (Q'.neg_eqv_congr _ _
        (mul_congr h6right (Q'.eqv_refl _))))
    (Q'.mul_eqv_congr_left 2 _ _
      (mul_congr (Q'.eqv_refl _)
        (mul_congr (Q'.eqv_refl _) (Q'.eqv_refl _))))

/-- Exact reduction of the connected `2+2+4` row cumulant to the checked
eight- and six-row Wick steps and explicit Gram bases. -/
theorem finiteGaussian_two_two_four_cumulant_wick
    (N : Nat) (a b c d e f g h : Nat → Q') :
    finiteGaussianTwoTwoFourCumulant N a b c d e f g h ≈
      finiteGaussianTwoTwoFourWickReduction N a b c d e f g h := by
  have h8 := finiteProductGaussian_eight_rows_wick
    N a b c d e f g h
  have h6left := finiteProductGaussian_six_rows_wick N a b e f g h
  have h6right := finiteProductGaussian_six_rows_wick N c d e f g h
  have h4left := finiteProductGaussian_four_row_word N a b c d
  have h4quartic := finiteProductGaussian_four_row_word N e f g h
  have h2left := finiteProductGaussian_two_row_word N a b
  have h2right := finiteProductGaussian_two_row_word N c d
  unfold finiteGaussianTwoTwoFourCumulant
    finiteGaussianTwoTwoFourWickReduction finiteRowFourWickValue
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr' h8
          (Q'.neg_eqv_congr _ _ (mul_congr h4left h4quartic)))
        (Q'.neg_eqv_congr _ _ (mul_congr h6left h2right)))
      (Q'.neg_eqv_congr _ _ (mul_congr h6right h2left)))
    (Q'.mul_eqv_congr_left 2 _ _
      (mul_congr h2left (mul_congr h2right h4quartic)))

/-- Direct consumer form: the ordinary polynomial cumulant of two quadratic
row blocks and one quartic row block reduces to the finite Wick expression. -/
theorem finiteGaussianThirdCumulant_row_blocks_wick
    (N : Nat) (a b c d e f g h : Nat → Q') :
    finiteGaussianThirdCumulant N
        (finiteGaussianRowWord N [a, b])
        (finiteGaussianRowWord N [c, d])
        (finiteGaussianRowWord N [e, f, g, h]) ≈
      finiteGaussianTwoTwoFourWickReduction N a b c d e f g h :=
  Q'.eqv_trans _ _ _
    (finiteGaussianThirdCumulant_row_blocks N a b c d e f g h)
    (finiteGaussian_two_two_four_cumulant_wick N a b c d e f g h)

end YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoFourCumulant

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoFourCumulant.finiteGaussian_two_two_four_cumulant_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoFourCumulant.finiteGaussianThirdCumulant_row_blocks
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoFourCumulant.finiteGaussianThirdCumulant_row_blocks_wick
