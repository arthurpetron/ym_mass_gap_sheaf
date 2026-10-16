/-
# Cubic source-source order-six Cayley covariance

This leaf pays the remaining source-only order-six contraction

  Cov(A3(left), A3(right)).

It first derives the vanishing of every three-row finite Gaussian mean from
the checked Wick recursion and the constructive zero-mean theorem for one
finite rational linear row.  The covariance therefore reduces to its complete
six-row Wick value.  Finite weighted block bilinearity then places the result
on the exact open-cube Cayley trace-source cubic rows.

The mixed source/action cumulants, OWN normalization, supplied OLD centers,
higher remainder and ORIGINAL-law comparison remain separate obligations.
No sign, uniform estimate or physical mass gap is claimed here.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceEvenCovariance

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCubicCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianPositivity
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianIBP
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowWordWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianCayleyCubicPairTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCoefficients
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceEvenCovariance

local infix:50 " ≈ " => Q'.eqv

private theorem mul_congr {left left' right right' : Q'}
    (hleft : left ≈ left') (hright : right ≈ right') :
    left * right ≈ left' * right' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hleft)
    (Q'.mul_eqv_congr_left _ _ _ hright)

private theorem monoMul_nil_right (monomial : List Nat) :
    monoMul monomial [] = monomial := by
  cases monomial <;> rfl

private theorem polyMul_one_right : ∀ polynomial : RatPoly,
    RatPolyCoeffEqv (polyMul polynomial polyOne) polynomial
  | [] => RatPolyCoeffEqv.refl _
  | term :: polynomial => by
      intro weight
      rcases term with ⟨monomial, coefficient⟩
      change
        (coefficient * 1) * weight (monoMul monomial []) +
              ratWeightedSum weight (polyMul polynomial polyOne) ≈
          coefficient * weight monomial +
            ratWeightedSum weight polynomial
      rw [monoMul_nil_right]
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_one_eqv coefficient))
        (polyMul_one_right polynomial weight)

private theorem polyMul_one_left (polynomial : RatPoly) :
    RatPolyCoeffEqv (polyMul polyOne polynomial) polynomial :=
  RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.mul_comm polyOne polynomial)
    (polyMul_one_right polynomial)

private theorem gaussian_one_mul_linear_zero
    (N : Nat) (row : Nat → Q') :
    finiteProductGaussian N
        (polyMul polyOne (finiteLinearRow N row)) ≈ 0 :=
  Q'.eqv_trans _ _ _
    (finiteProductGaussian_coeffEqv N
      (polyMul_one_left (finiteLinearRow N row)))
    (finiteProductGaussian_linearRow_zero N row)

/-- The one-step Wick value of every ordered three-row word is zero. -/
theorem finiteGaussianRowWickStep_three_zero
    (N : Nat) (a b c : Nat → Q') :
    finiteGaussianRowWickStep N a [b, c] ≈ 0 := by
  have firstLinear := gaussian_one_mul_linear_zero N c
  have secondLinear := gaussian_one_mul_linear_zero N b
  unfold finiteGaussianRowWickStep finiteGaussianDerivativeContraction
    finiteGaussianRowWord
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ firstLinear)
      (Q'.mul_eqv_congr_left _ _ _ secondLinear))
    (poly_identity_of_normal_eq
      (.add
        (.mul (.var 0) (.const 0))
        (.mul (.var 1) (.const 0)))
      (.const 0) (by decide) (fun
        | 0 => finiteRowGram N a b
        | _ => finiteRowGram N a c))

/-- Every ordered three-row word has zero finite product-Gaussian mean. -/
theorem finiteProductGaussian_three_row_word_zero
    (N : Nat) (a b c : Nat → Q') :
    finiteProductGaussian N
        (finiteGaussianRowWord N [a, b, c]) ≈ 0 :=
  Q'.eqv_trans _ _ _
    (finiteProductGaussian_row_word_wick N a b [c])
    (finiteGaussianRowWickStep_three_zero N a b c)

/-- Exact six-row Wick value of one cubic/cubic covariance. -/
def finiteGaussianThreeThreeCovarianceWickReduction
    (N : Nat) (a b c d e f : Nat → Q') : Q' :=
  finiteGaussianRowWickStep N a [b, c, d, e, f]

/-- One ordered cubic row word covaried with another reduces to the complete
six-row Wick value because both cubic means vanish constructively. -/
theorem finiteGaussianCovariance_three_three_row_words_wick
    (N : Nat) (a b c d e f : Nat → Q') :
    finiteGaussianCovariance N
        (finiteGaussianRowWord N [a, b, c])
        (finiteGaussianRowWord N [d, e, f]) ≈
      finiteGaussianThreeThreeCovarianceWickReduction N a b c d e f := by
  have productPolynomial : RatPolyCoeffEqv
      (polyMul
        (finiteGaussianRowWord N [a, b, c])
        (finiteGaussianRowWord N [d, e, f]))
      (finiteGaussianRowWord N [a, b, c, d, e, f]) :=
    finiteGaussianRowWord_append_nonempty N a d [b, c] [e, f]
  have productValue := Q'.eqv_trans _ _ _
    (finiteProductGaussian_coeffEqv N productPolynomial)
    (finiteProductGaussian_six_rows_wick N a b c d e f)
  have leftMean := finiteProductGaussian_three_row_word_zero N a b c
  have rightMean := finiteProductGaussian_three_row_word_zero N d e f
  unfold finiteGaussianCovariance
    finiteGaussianThreeThreeCovarianceWickReduction
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' productValue
      (Q'.neg_eqv_congr _ _ (mul_congr leftMean rightMean)))
    (poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.mul (.const 0) (.const 0))))
      (.var 0) (by decide)
      (fun _ => finiteGaussianRowWickStep N a [b, c, d, e, f]))

/-- Explicit weighted double sum of cubic/cubic covariance Wick values. -/
def finiteGaussianWeightedThreeThreeCovarianceWickSum
    (N : Nat)
    (left right : List WeightedCubicRowBlock) : Q' :=
  qListSum (left.map fun leftTerm =>
    qListSum (right.map fun rightTerm =>
      (leftTerm.weight * rightTerm.weight) *
        finiteGaussianThreeThreeCovarianceWickReduction N
          leftTerm.first leftTerm.second leftTerm.third
          rightTerm.first rightTerm.second rightTerm.third))

/-- Covariance of two finite weighted cubic row-block sums is the displayed
finite double six-row Wick sum. -/
theorem finiteGaussianCovariance_weighted_three_three_row_blocks_wick
    (N : Nat)
    (left right : List WeightedCubicRowBlock) :
    finiteGaussianCovariance N
        (weightedTermPolynomial
          (left.map (weightedCubicRowBlockTerm N)))
        (weightedTermPolynomial
          (right.map (weightedCubicRowBlockTerm N))) ≈
      finiteGaussianWeightedThreeThreeCovarianceWickSum N left right := by
  let cubicPolynomial := fun cubic : WeightedCubicRowBlock =>
    polySmul cubic.weight
      (finiteGaussianRowWord N [cubic.first, cubic.second, cubic.third])
  let reduced := fun leftTerm : WeightedCubicRowBlock =>
    fun rightTerm : WeightedCubicRowBlock =>
      (leftTerm.weight * rightTerm.weight) *
        finiteGaussianThreeThreeCovarianceWickReduction N
          leftTerm.first leftTerm.second leftTerm.third
          rightTerm.first rightTerm.second rightTerm.third
  unfold weightedTermPolynomial weightedCubicRowBlockTerm
    finiteGaussianWeightedThreeThreeCovarianceWickSum
  simp only [List.map_map]
  change finiteGaussianCovariance N
      (polySum (left.map cubicPolynomial))
      (polySum (right.map cubicPolynomial)) ≈
    qListSum (left.map fun leftTerm =>
      qListSum (right.map (reduced leftTerm)))
  have expandLeft :
      finiteGaussianCovariance N
          (polySum (left.map cubicPolynomial))
          (polySum (right.map cubicPolynomial)) ≈
        qListSum (left.map fun leftTerm =>
          finiteGaussianCovariance N (cubicPolynomial leftTerm)
            (polySum (right.map cubicPolynomial))) := by
    simpa only [List.map_map, Function.comp_apply] using
      finiteGaussianCovariance_polySum_left N
        (polySum (right.map cubicPolynomial))
        (left.map cubicPolynomial)
  have reduceLeft :
      qListSum (left.map fun leftTerm =>
          finiteGaussianCovariance N (cubicPolynomial leftTerm)
            (polySum (right.map cubicPolynomial))) ≈
        qListSum (left.map fun leftTerm =>
          qListSum (right.map (reduced leftTerm))) := by
    exact finiteGaussianCovariance_qListSum_congr _ _ left
      (fun leftTerm _ => by
        have expandRight :
            finiteGaussianCovariance N (cubicPolynomial leftTerm)
                (polySum (right.map cubicPolynomial)) ≈
              qListSum (right.map fun rightTerm =>
                finiteGaussianCovariance N (cubicPolynomial leftTerm)
                  (cubicPolynomial rightTerm)) := by
          simpa only [List.map_map, Function.comp_apply] using
            finiteGaussianCovariance_polySum_right N
              (cubicPolynomial leftTerm) (right.map cubicPolynomial)
        have reduceRight :
            qListSum (right.map fun rightTerm =>
                finiteGaussianCovariance N (cubicPolynomial leftTerm)
                  (cubicPolynomial rightTerm)) ≈
              qListSum (right.map (reduced leftTerm)) := by
          exact finiteGaussianCovariance_qListSum_congr _ _ right
            (fun rightTerm _ => by
              exact Q'.eqv_trans _ _ _
                (finiteGaussianCovariance_smul N
                  leftTerm.weight rightTerm.weight _ _)
                (Q'.mul_eqv_congr_left _ _ _
                  (finiteGaussianCovariance_three_three_row_words_wick N
                    leftTerm.first leftTerm.second leftTerm.third
                    rightTerm.first rightTerm.second rightTerm.third)))
        exact Q'.eqv_trans _ _ _ expandRight reduceRight)
  exact Q'.eqv_trans _ _ _ expandLeft reduceLeft

/-- Exact finite Wick value of the remaining cubic source-source covariance
for two selected history times. -/
def openCubeBulkCayleyTraceCubicOrderSixCovarianceWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) : Q' :=
  finiteGaussianWeightedThreeThreeCovarianceWickSum
    (bulkSourceNoiseCount timeBonds side)
    (openCubeBulkCayleyTraceA3RowBlocks
      timeBonds side sidePositive stage leftTime)
    (openCubeBulkCayleyTraceA3RowBlocks
      timeBonds side sidePositive stage rightTime)

/-- The literal cubic source covariance `Cov(A3(left),A3(right))` is exactly
the displayed finite weighted six-row Wick sum. -/
theorem finiteGaussianCovariance_openCube_bulk_cayley_trace_cubic_orderSix_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) :
    finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
        (openCubeBulkCayleyTraceA3
          timeBonds side sidePositive stage leftTime)
        (openCubeBulkCayleyTraceA3
          timeBonds side sidePositive stage rightTime) ≈
      openCubeBulkCayleyTraceCubicOrderSixCovarianceWickSum
        timeBonds side sidePositive stage leftTime rightTime := by
  let N := bulkSourceNoiseCount timeBonds side
  let leftBlocks := openCubeBulkCayleyTraceA3RowBlocks
    timeBonds side sidePositive stage leftTime
  let rightBlocks := openCubeBulkCayleyTraceA3RowBlocks
    timeBonds side sidePositive stage rightTime
  have leftCertificate := openCubeBulkCayleyTraceA3_coeffEqv
    timeBonds side sidePositive stage leftTime
  have rightCertificate := openCubeBulkCayleyTraceA3_coeffEqv
    timeBonds side sidePositive stage rightTime
  exact Q'.eqv_trans _ _ _
    (finiteGaussianCovariance_coeffEqv N
      leftCertificate rightCertificate)
    (finiteGaussianCovariance_weighted_three_three_row_blocks_wick
      N leftBlocks rightBlocks)

/-- Sum of all three source-source order-six covariance Wick values. -/
def openCubeBulkCayleyTraceSourceOrderSixCovarianceWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) : Q' :=
  openCubeBulkCayleyTraceEvenOrderSixCovarianceWickSum
      timeBonds side sidePositive stage leftTime rightTime +
    openCubeBulkCayleyTraceCubicOrderSixCovarianceWickSum
      timeBonds side sidePositive stage leftTime rightTime

/-- The complete source-source part of the order-six response is the sum of
the two even covariance Wick families and the cubic-cubic Wick family. -/
theorem finiteGaussianCovariance_openCube_bulk_cayley_trace_source_orderSix_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) :
    (finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
        (openCubeBulkCayleyTraceA4
          timeBonds side sidePositive stage leftTime)
        (openCubeBulkCayleyTraceA2
          timeBonds side sidePositive stage rightTime) +
      finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
        (openCubeBulkCayleyTraceA2
          timeBonds side sidePositive stage leftTime)
        (openCubeBulkCayleyTraceA4
          timeBonds side sidePositive stage rightTime)) +
      finiteGaussianCovariance (bulkSourceNoiseCount timeBonds side)
        (openCubeBulkCayleyTraceA3
          timeBonds side sidePositive stage leftTime)
        (openCubeBulkCayleyTraceA3
          timeBonds side sidePositive stage rightTime) ≈
      openCubeBulkCayleyTraceSourceOrderSixCovarianceWickSum
        timeBonds side sidePositive stage leftTime rightTime := by
  exact Q'.add_eqv_congr'
    (finiteGaussianCovariance_openCube_bulk_cayley_trace_even_orderSix_wick
      timeBonds side sidePositive stage leftTime rightTime)
    (finiteGaussianCovariance_openCube_bulk_cayley_trace_cubic_orderSix_wick
      timeBonds side sidePositive stage leftTime rightTime)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCubicCovariance

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCubicCovariance.finiteProductGaussian_three_row_word_zero
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCubicCovariance.finiteGaussianCovariance_three_three_row_words_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCubicCovariance.finiteGaussianCovariance_weighted_three_three_row_blocks_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCubicCovariance.finiteGaussianCovariance_openCube_bulk_cayley_trace_source_orderSix_wick
