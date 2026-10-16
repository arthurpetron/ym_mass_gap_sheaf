/-
# Connected cubic/quadratic/cubic finite Gaussian row cumulant

The two mixed action terms in the order-six trace-source response have row
degrees `3+2+3`.  This leaf proves the required generic finite-row compiler.
It first derives vanishing of every ordered five-row word from the checked
Wick recursion and the already checked three-row odd mean.  The literal
third cumulant then reduces to

  E[row^8] - E[left cubic * right cubic] * E[middle quadratic].

Both surviving moments are replaced by checked Wick/Gram values.  A literal
first-two-slot symmetry theorem is also included so the same compiler serves
both mixed source orientations.

No open-cube sum, sign, uniform estimate, ORIGINAL-law comparison or physical
mass gap is asserted here.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCubicCovariance

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianThreeTwoThreeCumulant

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
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowWordWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoFourCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianThirdCumulantTrilinear
open YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkNormalizedQuarticCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianCayleyCubicPairTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCubicCovariance

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

private theorem gaussian_three_row_coeffEqv_zero
    (N : Nat) {polynomial : RatPoly}
    (a b c : Nat → Q')
    (certificate : RatPolyCoeffEqv polynomial
      (finiteGaussianRowWord N [a, b, c])) :
    finiteProductGaussian N polynomial ≈ 0 :=
  Q'.eqv_trans _ _ _
    (finiteProductGaussian_coeffEqv N certificate)
    (finiteProductGaussian_three_row_word_zero N a b c)

/-- The one-step Wick value of every ordered five-row word is zero. -/
theorem finiteGaussianRowWickStep_five_zero
    (N : Nat) (a b c d e : Nat → Q') :
    finiteGaussianRowWickStep N a [b, c, d, e] ≈ 0 := by
  let B := finiteLinearRow N b
  let C := finiteLinearRow N c
  let D := finiteLinearRow N d
  let E := finiteLinearRow N e
  have firstPolynomial : RatPolyCoeffEqv
      (polyMul polyOne (finiteGaussianRowWord N [c, d, e]))
      (finiteGaussianRowWord N [c, d, e]) :=
    polyMul_one_left _
  have secondPolynomial : RatPolyCoeffEqv
      (polyMul (polyMul polyOne B)
        (finiteGaussianRowWord N [d, e]))
      (finiteGaussianRowWord N [b, d, e]) :=
    RatPolyCoeffEqv.trans
      ((polyMul_one_left B).mul_right
        (finiteGaussianRowWord N [d, e]))
      (finiteGaussianRowWord_append_nonempty N b d [] [e])
  have thirdPolynomial : RatPolyCoeffEqv
      (polyMul (polyMul (polyMul polyOne B) C) E)
      (finiteGaussianRowWord N [b, c, e]) :=
    RatPolyCoeffEqv.trans
      (((polyMul_one_left B).mul_right C).mul_right E)
      (finiteGaussianRowWord_append_nonempty N b e [c] [])
  have fourthPolynomial : RatPolyCoeffEqv
      (polyMul (polyMul (polyMul polyOne B) C) D)
      (finiteGaussianRowWord N [b, c, d]) :=
    RatPolyCoeffEqv.trans
      (((polyMul_one_left B).mul_right C).mul_right D)
      (finiteGaussianRowWord_append_nonempty N b d [c] [])
  have firstMean := gaussian_three_row_coeffEqv_zero N c d e
    firstPolynomial
  have secondMean := gaussian_three_row_coeffEqv_zero N b d e
    secondPolynomial
  have thirdMean := gaussian_three_row_coeffEqv_zero N b c e
    thirdPolynomial
  have fourthMean := gaussian_three_row_coeffEqv_zero N b c d
    fourthPolynomial
  unfold finiteGaussianRowWickStep finiteGaussianDerivativeContraction
  change
    finiteRowGram N a b *
          finiteProductGaussian N
            (polyMul polyOne (finiteGaussianRowWord N [c, d, e])) +
        (finiteRowGram N a c *
              finiteProductGaussian N
                (polyMul (polyMul polyOne B)
                  (finiteGaussianRowWord N [d, e])) +
          (finiteRowGram N a d *
                finiteProductGaussian N
                  (polyMul (polyMul (polyMul polyOne B) C) E) +
            finiteRowGram N a e *
              finiteProductGaussian N
                (polyMul (polyMul (polyMul polyOne B) C) D))) ≈ 0
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ firstMean)
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _ secondMean)
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left _ _ _ thirdMean)
          (Q'.mul_eqv_congr_left _ _ _ fourthMean))))
    (poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.const 0))
        (.add (.mul (.var 1) (.const 0))
          (.add (.mul (.var 2) (.const 0))
            (.mul (.var 3) (.const 0)))))
      (.const 0) (by decide) (fun
        | 0 => finiteRowGram N a b
        | 1 => finiteRowGram N a c
        | 2 => finiteRowGram N a d
        | _ => finiteRowGram N a e))

/-- Every ordered five-row word has zero finite product-Gaussian mean. -/
theorem finiteProductGaussian_five_row_word_zero
    (N : Nat) (a b c d e : Nat → Q') :
    finiteProductGaussian N
        (finiteGaussianRowWord N [a, b, c, d, e]) ≈ 0 :=
  Q'.eqv_trans _ _ _
    (finiteProductGaussian_row_word_wick N a b [c, d, e])
    (finiteGaussianRowWickStep_five_zero N a b c d e)

private def thirdCumulantValue
    (triple leftRight insertionMean leftInsertion rightMean
      rightInsertion leftMean : Q') : Q' :=
  ((((triple + -(leftRight * insertionMean)) +
        -(leftInsertion * rightMean)) +
      -(rightInsertion * leftMean)) +
    2 * (leftMean * (rightMean * insertionMean)))

private theorem thirdCumulantValue_swap
    {triple triple' leftRight leftRight' insertionMean
      leftInsertion rightMean rightInsertion leftMean : Q'}
    (htriple : triple ≈ triple')
    (hleftRight : leftRight ≈ leftRight') :
    thirdCumulantValue triple leftRight insertionMean
        leftInsertion rightMean rightInsertion leftMean ≈
      thirdCumulantValue triple' leftRight' insertionMean
        rightInsertion leftMean leftInsertion rightMean := by
  unfold thirdCumulantValue
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr' htriple
            (Q'.neg_eqv_congr _ _
              (mul_congr hleftRight (Q'.eqv_refl _))))
          (Q'.eqv_refl _))
        (Q'.eqv_refl _))
      (Q'.eqv_refl _))
    (poly_identity_of_normal_eq
      (.add
        (.add
          (.add
            (.add (.var 0) (.neg (.mul (.var 1) (.var 2))))
            (.neg (.mul (.var 3) (.var 4))))
          (.neg (.mul (.var 5) (.var 6))))
        (.mul (.const 2) (.mul (.var 6) (.mul (.var 4) (.var 2)))))
      (.add
        (.add
          (.add
            (.add (.var 0) (.neg (.mul (.var 1) (.var 2))))
            (.neg (.mul (.var 5) (.var 6))))
          (.neg (.mul (.var 3) (.var 4))))
        (.mul (.const 2) (.mul (.var 4) (.mul (.var 6) (.var 2)))))
      (by decide) (fun
        | 0 => triple'
        | 1 => leftRight'
        | 2 => insertionMean
        | 3 => leftInsertion
        | 4 => rightMean
        | 5 => rightInsertion
        | _ => leftMean))

/-- The literal finite Gaussian third cumulant is symmetric in its first two
polynomial slots. -/
theorem finiteGaussianThirdCumulant_swap_left_middle
    (N : Nat) (left middle insertion : RatPoly) :
    finiteGaussianThirdCumulant N left middle insertion ≈
      finiteGaussianThirdCumulant N middle left insertion := by
  have product : RatPolyCoeffEqv
      (polyMul left middle) (polyMul middle left) :=
    RatPolyCoeffEqv.mul_comm left middle
  have triple : RatPolyCoeffEqv
      (polyMul (polyMul left middle) insertion)
      (polyMul (polyMul middle left) insertion) :=
    product.mul_right insertion
  unfold finiteGaussianThirdCumulant
  change thirdCumulantValue _ _ _ _ _ _ _ ≈
    thirdCumulantValue _ _ _ _ _ _ _
  exact thirdCumulantValue_swap
    (finiteProductGaussian_coeffEqv N triple)
    (finiteProductGaussian_coeffEqv N product)

/-- Literal connected cumulant of ordered row degrees `3+2+3`. -/
def finiteGaussianThreeTwoThreeCumulant
    (N : Nat) (a b c d e f g h : Nat → Q') : Q' :=
  let moment := fun rows =>
    finiteProductGaussian N (finiteGaussianRowWord N rows)
  (((moment [a, b, c, d, e, f, g, h] +
          -(moment [a, b, c, d, e] * moment [f, g, h])) +
        -(moment [a, b, c, f, g, h] * moment [d, e])) +
      -(moment [d, e, f, g, h] * moment [a, b, c])) +
    2 * (moment [a, b, c] *
      (moment [d, e] * moment [f, g, h]))

/-- Complete Wick reduction of the connected `3+2+3` row cumulant. -/
def finiteGaussianThreeTwoThreeWickReduction
    (N : Nat) (a b c d e f g h : Nat → Q') : Q' :=
  finiteGaussianRowWickStep N a [b, c, d, e, f, g, h] -
    finiteGaussianRowWickStep N a [b, c, f, g, h] *
      finiteRowGram N d e

/-- The abstract polynomial third cumulant of cubic, quadratic and cubic row
blocks is the literal ordered `3+2+3` row cumulant. -/
theorem finiteGaussianThirdCumulant_three_two_three_row_blocks
    (N : Nat) (a b c d e f g h : Nat → Q') :
    finiteGaussianThirdCumulant N
        (finiteGaussianRowWord N [a, b, c])
        (finiteGaussianRowWord N [d, e])
        (finiteGaussianRowWord N [f, g, h]) ≈
      finiteGaussianThreeTwoThreeCumulant N a b c d e f g h := by
  let left := finiteGaussianRowWord N [a, b, c]
  let middle := finiteGaussianRowWord N [d, e]
  let insertion := finiteGaussianRowWord N [f, g, h]
  have leftMiddle : RatPolyCoeffEqv
      (polyMul left middle)
      (finiteGaussianRowWord N [a, b, c, d, e]) :=
    finiteGaussianRowWord_append_nonempty N a d [b, c] [e]
  have leftInsertion : RatPolyCoeffEqv
      (polyMul left insertion)
      (finiteGaussianRowWord N [a, b, c, f, g, h]) :=
    finiteGaussianRowWord_append_nonempty N a f [b, c] [g, h]
  have middleInsertion : RatPolyCoeffEqv
      (polyMul middle insertion)
      (finiteGaussianRowWord N [d, e, f, g, h]) :=
    finiteGaussianRowWord_append_nonempty N d f [e] [g, h]
  have triple : RatPolyCoeffEqv
      (polyMul (polyMul left middle) insertion)
      (finiteGaussianRowWord N [a, b, c, d, e, f, g, h]) :=
    RatPolyCoeffEqv.trans (leftMiddle.mul_right insertion)
      (finiteGaussianRowWord_append_nonempty N a f
        [b, c, d, e] [g, h])
  have tripleValue := finiteProductGaussian_coeffEqv N triple
  have leftMiddleValue := finiteProductGaussian_coeffEqv N leftMiddle
  have leftInsertionValue := finiteProductGaussian_coeffEqv N leftInsertion
  have middleInsertionValue := finiteProductGaussian_coeffEqv N middleInsertion
  unfold finiteGaussianThirdCumulant finiteGaussianThreeTwoThreeCumulant
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr' tripleValue
          (Q'.neg_eqv_congr _ _
            (mul_congr leftMiddleValue (Q'.eqv_refl _))))
        (Q'.neg_eqv_congr _ _
          (mul_congr leftInsertionValue (Q'.eqv_refl _))))
      (Q'.neg_eqv_congr _ _
        (mul_congr middleInsertionValue (Q'.eqv_refl _))))
    (Q'.mul_eqv_congr_left 2 _ _
      (mul_congr (Q'.eqv_refl _)
        (mul_congr (Q'.eqv_refl _) (Q'.eqv_refl _))))

/-- Exact reduction of the literal connected `3+2+3` cumulant to degree
eight and degree six Wick steps plus one quadratic Gram. -/
theorem finiteGaussian_three_two_three_cumulant_wick
    (N : Nat) (a b c d e f g h : Nat → Q') :
    finiteGaussianThreeTwoThreeCumulant N a b c d e f g h ≈
      finiteGaussianThreeTwoThreeWickReduction N a b c d e f g h := by
  have eightRows := finiteProductGaussian_eight_rows_wick
    N a b c d e f g h
  have leftMiddleZero := finiteProductGaussian_five_row_word_zero
    N a b c d e
  have leftInsertion := finiteProductGaussian_six_rows_wick
    N a b c f g h
  have middleInsertionZero := finiteProductGaussian_five_row_word_zero
    N d e f g h
  have leftZero := finiteProductGaussian_three_row_word_zero N a b c
  have middleValue := finiteProductGaussian_two_row_word N d e
  have insertionZero := finiteProductGaussian_three_row_word_zero N f g h
  unfold finiteGaussianThreeTwoThreeCumulant
    finiteGaussianThreeTwoThreeWickReduction
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr' eightRows
            (Q'.neg_eqv_congr _ _
              (mul_congr leftMiddleZero insertionZero)))
          (Q'.neg_eqv_congr _ _
            (mul_congr leftInsertion middleValue)))
        (Q'.neg_eqv_congr _ _
          (mul_congr middleInsertionZero leftZero)))
      (Q'.mul_eqv_congr_left 2 _ _
        (mul_congr leftZero (mul_congr middleValue insertionZero))))
    (poly_identity_of_normal_eq
      (.add
        (.add
          (.add
            (.add (.var 0) (.neg (.mul (.const 0) (.const 0))))
            (.neg (.mul (.var 1) (.var 2))))
          (.neg (.mul (.const 0) (.const 0))))
        (.mul (.const 2)
          (.mul (.const 0) (.mul (.var 2) (.const 0)))))
      (.add (.var 0) (.neg (.mul (.var 1) (.var 2))))
      (by decide) (fun
        | 0 => finiteGaussianRowWickStep N a [b, c, d, e, f, g, h]
        | 1 => finiteGaussianRowWickStep N a [b, c, f, g, h]
        | _ => finiteRowGram N d e))

/-- Direct consumer form for one ordered cubic/quadratic/cubic row triple. -/
theorem finiteGaussianThirdCumulant_three_two_three_row_blocks_wick
    (N : Nat) (a b c d e f g h : Nat → Q') :
    finiteGaussianThirdCumulant N
        (finiteGaussianRowWord N [a, b, c])
        (finiteGaussianRowWord N [d, e])
        (finiteGaussianRowWord N [f, g, h]) ≈
      finiteGaussianThreeTwoThreeWickReduction N a b c d e f g h :=
  Q'.eqv_trans _ _ _
    (finiteGaussianThirdCumulant_three_two_three_row_blocks
      N a b c d e f g h)
    (finiteGaussian_three_two_three_cumulant_wick
      N a b c d e f g h)

/-- Explicit weighted triple sum of `3+2+3` Wick reductions. -/
def finiteGaussianWeightedThreeTwoThreeWickSum
    (N : Nat)
    (left : List WeightedCubicRowBlock)
    (middle : List WeightedQuadraticRowBlock)
    (right : List WeightedCubicRowBlock) : Q' :=
  qListSum (left.map fun leftTerm =>
    qListSum (middle.map fun middleTerm =>
      qListSum (right.map fun rightTerm =>
        leftTerm.weight * (middleTerm.weight *
          (rightTerm.weight *
            finiteGaussianThreeTwoThreeWickReduction N
              leftTerm.first leftTerm.second leftTerm.third
              middleTerm.first middleTerm.second
              rightTerm.first rightTerm.second rightTerm.third)))))

private theorem qListSum_congr {Index : Type}
    (left right : Index → Q') : ∀ items : List Index,
    (∀ item, item ∈ items → left item ≈ right item) →
    qListSum (items.map left) ≈ qListSum (items.map right)
  | [], _ => Q'.eqv_refl _
  | item :: items, hypothesis =>
      Q'.add_eqv_congr'
        (hypothesis item List.mem_cons_self)
        (qListSum_congr left right items
          (fun other membership =>
            hypothesis other (List.mem_cons_of_mem item membership)))

/-- Weighted finite cubic/quadratic/cubic row-block sums reduce termwise to
the checked `3+2+3` Wick expression. -/
theorem finiteGaussianThirdCumulant_weighted_three_two_three_row_blocks_wick
    (N : Nat)
    (left : List WeightedCubicRowBlock)
    (middle : List WeightedQuadraticRowBlock)
    (right : List WeightedCubicRowBlock) :
    finiteGaussianThirdCumulant N
        (weightedTermPolynomial
          (left.map (weightedCubicRowBlockTerm N)))
        (weightedTermPolynomial
          (middle.map (weightedQuadraticRowBlockTerm N)))
        (weightedTermPolynomial
          (right.map (weightedCubicRowBlockTerm N))) ≈
      finiteGaussianWeightedThreeTwoThreeWickSum N left middle right := by
  have sumExpansion := finiteGaussianThirdCumulant_weighted_polySum_three N
    (left.map (weightedCubicRowBlockTerm N))
    (middle.map (weightedQuadraticRowBlockTerm N))
    (right.map (weightedCubicRowBlockTerm N))
  exact Q'.eqv_trans _ _ _ sumExpansion (by
    simp only [List.map_map]
    exact qListSum_congr _ _ left (fun leftTerm _ =>
      qListSum_congr _ _ middle (fun middleTerm _ =>
        qListSum_congr _ _ right (fun rightTerm _ =>
          Q'.mul_eqv_congr_left leftTerm.weight _ _
            (Q'.mul_eqv_congr_left middleTerm.weight _ _
              (Q'.mul_eqv_congr_left rightTerm.weight _ _
                (finiteGaussianThirdCumulant_three_two_three_row_blocks_wick
                  N leftTerm.first leftTerm.second leftTerm.third
                  middleTerm.first middleTerm.second
                  rightTerm.first rightTerm.second rightTerm.third)))))))

end YMGap.Continuum.SU2QuaternionFiniteGaussianThreeTwoThreeCumulant

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianThreeTwoThreeCumulant.finiteProductGaussian_five_row_word_zero
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianThreeTwoThreeCumulant.finiteGaussianThirdCumulant_swap_left_middle
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianThreeTwoThreeCumulant.finiteGaussian_three_two_three_cumulant_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianThreeTwoThreeCumulant.finiteGaussianThirdCumulant_weighted_three_two_three_row_blocks_wick
