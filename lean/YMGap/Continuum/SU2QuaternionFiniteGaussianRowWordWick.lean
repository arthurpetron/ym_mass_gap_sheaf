/-
# Arbitrary finite rational-row Wick recursion

This leaf derives one complete Wick recursion step for an arbitrary nonempty
ordered word of the existing finite rational Gaussian rows.  The leading row
is paired successively with every later row; the already-passed rows are kept
as an explicit polynomial prefix, so no permutation enumeration, independence
axiom or assumed moment formula is needed.

Repeated use reduces every even row word, including the degree-eight words
needed by a quartic insertion against two quadratic sources, to computed Gram
contractions.  This module does not yet assemble those source sums or their
OLD-centered connected subtraction, prove a sign or scale-uniform estimate,
compare the ORIGINAL interacting law, or establish a physical mass gap.
Variables outside the finite Gaussian prefix are still evaluated at ONE by
the existing evaluator; no coefficient-preserving tail claim is made.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianFourRowMoment

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianRowWordWick

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianPositivity
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianIBP
open YMGap.Continuum.SU2QuaternionFiniteGaussianDoubleStein
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram
open YMGap.Continuum.SU2QuaternionFiniteGaussianFourRowMoment

local infix:50 " ≈ " => Q'.eqv

/-- Ordered product of finite rational Gaussian rows.  The singleton clause
keeps the last factor literal, avoiding an artificial derivative of `1`. -/
def finiteGaussianRowWord (N : Nat) : List (Nat → Q') → RatPoly
  | [] => polyOne
  | row :: [] => finiteLinearRow N row
  | row :: next :: rows =>
      polyMul (finiteLinearRow N row)
        (finiteGaussianRowWord N (next :: rows))

/-- One derivative-contraction sweep through a nonempty row tail.  `accumulated`
is the literal product of rows already passed by the sweep. -/
def finiteGaussianDerivativeContraction
    (N : Nat) (leading : Nat → Q') (accumulated : RatPoly) :
    List (Nat → Q') → Q'
  | [] => 0
  | row :: [] =>
      finiteRowGram N leading row * finiteProductGaussian N accumulated
  | row :: next :: rows =>
      finiteRowGram N leading row *
          finiteProductGaussian N
            (polyMul accumulated (finiteGaussianRowWord N (next :: rows))) +
        finiteGaussianDerivativeContraction N leading
          (polyMul accumulated (finiteLinearRow N row)) (next :: rows)

/-- Public one-step Wick value for a leading row and its ordered nonempty
tail. -/
def finiteGaussianRowWickStep
    (N : Nat) (leading : Nat → Q') (rows : List (Nat → Q')) : Q' :=
  finiteGaussianDerivativeContraction N leading polyOne rows

/-- Concatenating two nonempty ordered row words agrees coefficientwise with
multiplying their literal polynomials. -/
theorem finiteGaussianRowWord_append_nonempty
    (N : Nat) (leftHead rightHead : Nat → Q') :
    ∀ (leftTail rightTail : List (Nat → Q')),
      RatPolyCoeffEqv
        (polyMul
          (finiteGaussianRowWord N (leftHead :: leftTail))
          (finiteGaussianRowWord N (rightHead :: rightTail)))
        (finiteGaussianRowWord N
          ((leftHead :: leftTail) ++ (rightHead :: rightTail)))
  | [], _ => RatPolyCoeffEqv.refl _
  | next :: rest, rightTail =>
      RatPolyCoeffEqv.trans
        (RatPolyCoeffEqv.mul_assoc
          (finiteLinearRow N leftHead)
          (finiteGaussianRowWord N (next :: rest))
          (finiteGaussianRowWord N (rightHead :: rightTail)))
        ((finiteGaussianRowWord_append_nonempty N next rightHead
          rest rightTail).mul_left (finiteLinearRow N leftHead))

private theorem gaussian_add (N : Nat) (p q : RatPoly) :
    finiteProductGaussian N (polyAdd p q) ≈
      finiteProductGaussian N p + finiteProductGaussian N q := by
  rw [finiteProductGaussian_probe, finiteProductGaussian_probe,
    finiteProductGaussian_probe]
  exact ratWeightedSum_add (finiteGaussianMono N) p q

private theorem swap_first_two (p q r : RatPoly) :
    RatPolyCoeffEqv (polyMul p (polyMul q r))
      (polyMul q (polyMul p r)) :=
  RatPolyCoeffEqv.trans (RatPolyCoeffEqv.symm
      (RatPolyCoeffEqv.mul_assoc p q r))
    (RatPolyCoeffEqv.trans ((RatPolyCoeffEqv.mul_comm p q).mul_right r)
      (RatPolyCoeffEqv.mul_assoc q p r))

private theorem monoMul_right_nil : ∀ monomial : List Nat,
    monoMul monomial [] = monomial
  | [] => rfl
  | _ :: _ => by simp only [monoMul]

private theorem polyMul_one (polynomial : RatPoly) :
    RatPolyCoeffEqv (polyMul polynomial polyOne) polynomial := by
  intro weight
  induction polynomial with
  | nil => exact Q'.eqv_refl 0
  | cons term rest induction =>
      change
        (term.2 * 1) * weight (monoMul term.1 []) +
              ratWeightedSum weight (polyMul rest polyOne) ≈
          term.2 * weight term.1 + ratWeightedSum weight rest
      rw [monoMul_right_nil]
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_one_eqv term.2))
        induction

private theorem one_polyMul (polynomial : RatPoly) :
    RatPolyCoeffEqv (polyMul polyOne polynomial) polynomial :=
  RatPolyCoeffEqv.trans (RatPolyCoeffEqv.mul_comm polyOne polynomial)
    (polyMul_one polynomial)

private theorem derivative_contraction_nonempty (N : Nat)
    (leading : Nat → Q') :
    ∀ (accumulated : RatPoly) (row : Nat → Q') (rows : List (Nat → Q')),
      finiteProductGaussian N
          (polyMul accumulated
            (finiteRowDerivative N leading
              (finiteGaussianRowWord N (row :: rows)))) ≈
        finiteGaussianDerivativeContraction N leading accumulated (row :: rows)
  | accumulated, row, [] => by
      exact Q'.eqv_trans _ _ _
        (finiteProductGaussian_coeffEqv N
          (RatPolyCoeffEqv.mul_comm accumulated
            (finiteRowDerivative N leading (finiteLinearRow N row))))
        (finiteRowDerivative_mixed_contraction N leading row accumulated)
  | accumulated, row, next :: rows => by
      let Row := finiteLinearRow N row
      let Rest := finiteGaussianRowWord N (next :: rows)
      let DRow := finiteRowDerivative N leading Row
      let DRest := finiteRowDerivative N leading Rest
      have hsplit : RatPolyCoeffEqv
          (polyMul accumulated
            (finiteRowDerivative N leading (polyMul Row Rest)))
          (polyAdd
            (polyMul DRow (polyMul accumulated Rest))
            (polyMul (polyMul accumulated Row) DRest)) :=
        RatPolyCoeffEqv.trans
          ((finiteRowDerivative_mul N leading Row Rest).mul_left accumulated)
          (RatPolyCoeffEqv.trans
            (RatPolyCoeffEqv.mul_add_right accumulated
              (polyMul DRow Rest) (polyMul Row DRest))
            (RatPolyCoeffEqv.add
              (swap_first_two accumulated DRow Rest)
              (RatPolyCoeffEqv.symm
                (RatPolyCoeffEqv.mul_assoc accumulated Row DRest))))
      exact Q'.eqv_trans _ _ _
        (finiteProductGaussian_coeffEqv N hsplit)
        (Q'.eqv_trans _ _ _ (gaussian_add N _ _)
          (Q'.add_eqv_congr'
            (finiteRowDerivative_mixed_contraction N leading row
              (polyMul accumulated Rest))
            (derivative_contraction_nonempty N leading
              (polyMul accumulated Row) next rows)))

/-- Arbitrary rational-row Wick/Stein recursion.  For every nonempty tail,
the expectation of the ordered row word equals the finite sweep pairing its
leading row with each later row.  Repeating the theorem strictly lowers the
word degree by two. -/
theorem finiteProductGaussian_row_word_wick
    (N : Nat) (leading row : Nat → Q') (rows : List (Nat → Q')) :
    finiteProductGaussian N
        (finiteGaussianRowWord N (leading :: row :: rows)) ≈
      finiteGaussianRowWickStep N leading (row :: rows) := by
  exact Q'.eqv_trans _ _ _
    (finiteProductGaussian_linearRow_stein N leading
      (finiteGaussianRowWord N (row :: rows)))
    (Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (finiteProductGaussian_coeffEqv N
          (one_polyMul
            (finiteRowDerivative N leading
              (finiteGaussianRowWord N (row :: rows))))))
      (derivative_contraction_nonempty N leading polyOne row rows))

/-- Two-row word base of the recursion. -/
theorem finiteProductGaussian_two_row_word
    (N : Nat) (a b : Nat → Q') :
    finiteProductGaussian N (finiteGaussianRowWord N [a, b]) ≈
      finiteRowGram N a b :=
  finiteProductGaussian_row_pair N a b

/-- Four-row word base, in the right-associated order used by
`finiteGaussianRowWord`. -/
theorem finiteProductGaussian_four_row_word
    (N : Nat) (a b c d : Nat → Q') :
    finiteProductGaussian N (finiteGaussianRowWord N [a, b, c, d]) ≈
      finiteRowGram N a b * finiteRowGram N c d +
        (finiteRowGram N a c * finiteRowGram N b d +
          finiteRowGram N a d * finiteRowGram N b c) := by
  exact Q'.eqv_trans _ _ _
    (finiteProductGaussian_coeffEqv N
      (RatPolyCoeffEqv.symm
        (RatPolyCoeffEqv.mul_assoc
          (finiteLinearRow N a) (finiteLinearRow N b)
          (polyMul (finiteLinearRow N c) (finiteLinearRow N d)))))
    (finiteProductGaussian_four_rows N a b c d)

/-- Six-row specialization.  This is the lower-degree target produced by one
application of the degree-eight recursion. -/
theorem finiteProductGaussian_six_rows_wick
    (N : Nat) (a b c d e f : Nat → Q') :
    finiteProductGaussian N
        (finiteGaussianRowWord N [a, b, c, d, e, f]) ≈
      finiteGaussianRowWickStep N a [b, c, d, e, f] :=
  finiteProductGaussian_row_word_wick N a b [c, d, e, f]

/-- Eight-row specialization needed by one normalized Cayley-quartic
insertion against two quadratic source observables. -/
theorem finiteProductGaussian_eight_rows_wick
    (N : Nat) (a b c d e f g h : Nat → Q') :
    finiteProductGaussian N
        (finiteGaussianRowWord N [a, b, c, d, e, f, g, h]) ≈
      finiteGaussianRowWickStep N a [b, c, d, e, f, g, h] :=
  finiteProductGaussian_row_word_wick N a b [c, d, e, f, g, h]

end YMGap.Continuum.SU2QuaternionFiniteGaussianRowWordWick

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianRowWordWick.finiteProductGaussian_row_word_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianRowWordWick.finiteGaussianRowWord_append_nonempty
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianRowWordWick.finiteProductGaussian_two_row_word
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianRowWordWick.finiteProductGaussian_four_row_word
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianRowWordWick.finiteProductGaussian_six_rows_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianRowWordWick.finiteProductGaussian_eight_rows_wick
