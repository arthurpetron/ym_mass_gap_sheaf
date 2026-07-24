/-
# Finite signed-monomial reconstruction in one Bernstein row

Core B's bounded atom classifier produces finite signed sums of monomials.
To use a coefficientwise Bernstein certificate, all of those monomials must
be elevated to one common unnormalised Bernstein degree.  This module is the
generic exact seam for that operation.

Given integer weights `weight i`, exponents `exponent i`, a term count `N`,
and a common degree `D`, `finiteSignedMonomialBernsteinRow` recursively adds
the scaled Pascal rows

  `weight i * thetaMonoBernCoeff D (exponent i)`.

The main theorem proves that evaluating the resulting single row is exactly

  `sum_{i<N} weight i * w^(exponent i)`

whenever every used exponent is at most `D`.  Signs are unrestricted.  No
positivity claim is made here; downstream Core-B code may separately prove
coefficientwise nonnegativity of the actual reconstructed row.

Axiom gate (AGENTS.md Rules 1 and 8): no classical reasoning, sorry,
native_decide, quotient, or noncomputable declaration.
-/

import YMGap.Continuum.HarmonicThetaPascalEvaluation

namespace YMGap.Continuum.BernsteinSignedMonomialReconstruction

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BernsteinMonomialReconstruction
open YMGap.Continuum.HarmonicThetaPascalBridge
open YMGap.Continuum.HarmonicThetaPascalEvaluation

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Public linear operations on signed rows -/

/-- Pointwise sum of two signed Bernstein coefficient rows. -/
def signedRowAdd (a b : Nat → Int) : Nat → Int :=
  fun j => a j + b j

/-- Pointwise integer scaling of a signed Bernstein coefficient row. -/
def signedRowScale (z : Int) (a : Nat → Int) : Nat → Int :=
  fun j => z * a j

/-- Signed Bernstein evaluation respects pointwise row addition. -/
theorem signedBernsteinEval_add
    (D : Nat) (a b : Nat → Int) (w : Q') :
    signedBernsteinEval D (signedRowAdd a b) w ≈
      signedBernsteinEval D a w + signedBernsteinEval D b w := by
  unfold signedBernsteinEval signedRowAdd
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr
      (fun j => Q'.ofInt (a j + b j) * bernsteinBasis D w j)
      (fun j =>
        Q'.ofInt (a j) * bernsteinBasis D w j +
          Q'.ofInt (b j) * bernsteinBasis D w j)
      (fun j => ?_) (D + 1)) ?_
  · refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (RingNormaliser.ofInt_add (a j) (b j))) ?_
    exact Q'.add_mul_eqv
      (Q'.ofInt (a j)) (Q'.ofInt (b j)) (bernsteinBasis D w j)
  · exact RationalTail.finSum_add
      (fun j => Q'.ofInt (a j) * bernsteinBasis D w j)
      (fun j => Q'.ofInt (b j) * bernsteinBasis D w j)
      (D + 1)

/-- Signed Bernstein evaluation respects integer row scaling. -/
theorem signedBernsteinEval_scale
    (D : Nat) (z : Int) (a : Nat → Int) (w : Q') :
    signedBernsteinEval D (signedRowScale z a) w ≈
      Q'.ofInt z * signedBernsteinEval D a w := by
  unfold signedBernsteinEval signedRowScale
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr
      (fun j => Q'.ofInt (z * a j) * bernsteinBasis D w j)
      (fun j =>
        Q'.ofInt z * (Q'.ofInt (a j) * bernsteinBasis D w j))
      (fun j => ?_) (D + 1)) ?_
  · refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (RingNormaliser.ofInt_mul z (a j))) ?_
    exact Q'.mul_assoc_eqv
      (Q'.ofInt z) (Q'.ofInt (a j)) (bernsteinBasis D w j)
  · exact Q'.eqv_symm
      (const_mul_finSum
        (fun j => Q'.ofInt (a j) * bernsteinBasis D w j)
        (Q'.ofInt z) (D + 1))

/-! ## 2. A finite signed monomial compiler -/

/-- Compile the first `N` signed monomials into one common degree-`D`
Bernstein row.  The recursion is on the term count, so the definition is
directly computable and actual bounded atom lists can instantiate it without
any finite-set or choice machinery. -/
def finiteSignedMonomialBernsteinRow
    (D : Nat) (weight : Nat → Int) (exponent : Nat → Nat) :
    Nat → Nat → Int
  | 0, _ => 0
  | N + 1, j =>
      finiteSignedMonomialBernsteinRow D weight exponent N j +
        weight N * thetaMonoBernCoeff D (exponent N) j

/-- The exact signed monomial sum represented by
`finiteSignedMonomialBernsteinRow`. -/
def finiteSignedMonomialEval
    (weight : Nat → Int) (exponent : Nat → Nat)
    (w : Q') (N : Nat) : Q' :=
  finSum (fun i => Q'.ofInt (weight i) * w ^ (exponent i)) N

/-- Adding one source monomial appends its scaled elevated row. -/
theorem finiteSignedMonomialBernsteinRow_succ
    (D : Nat) (weight : Nat → Int) (exponent : Nat → Nat)
    (N j : Nat) :
    finiteSignedMonomialBernsteinRow D weight exponent (N + 1) j =
      signedRowAdd
        (finiteSignedMonomialBernsteinRow D weight exponent N)
        (signedRowScale (weight N)
          (thetaMonoBernCoeff D (exponent N))) j := by
  rfl

/-- **Exact finite signed reconstruction.**  A finite signed sum of
monomials, with every exponent fitting in `D`, evaluates exactly as the
single common Bernstein row compiled above. -/
theorem finiteSignedMonomialBernsteinRow_eval
    (D N : Nat) (weight : Nat → Int) (exponent : Nat → Nat)
    (w : Q')
    (hexponent : ∀ i, i < N → exponent i ≤ D) :
    signedBernsteinEval D
        (finiteSignedMonomialBernsteinRow D weight exponent N) w ≈
      finiteSignedMonomialEval weight exponent w N := by
  induction N with
  | zero =>
      unfold signedBernsteinEval finiteSignedMonomialEval
      change
        finSum (fun j =>
          (0 : Q') * bernsteinBasis D w j) (D + 1) ≈ 0
      refine Q'.eqv_trans _ _ _
        (finSum_eqv_congr
          (fun j => (0 : Q') * bernsteinBasis D w j)
          (fun _ => (0 : Q'))
          (fun j => Q'.zero_mul_eqv (bernsteinBasis D w j))
          (D + 1)) ?_
      exact Q'.eqv_of_eq (finSum_zero_seq (D + 1))
  | succ N ih =>
      have hprefix : ∀ i, i < N → exponent i ≤ D :=
        fun i hi => hexponent i (by omega)
      have hlast : exponent N ≤ D :=
        hexponent N (by omega)
      refine Q'.eqv_trans _ _ _
        (signedBernsteinEval_add D
          (finiteSignedMonomialBernsteinRow D weight exponent N)
          (signedRowScale (weight N)
            (thetaMonoBernCoeff D (exponent N))) w) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left
          (signedBernsteinEval D
            (finiteSignedMonomialBernsteinRow D weight exponent N) w)
          _ _
          (signedBernsteinEval_scale D (weight N)
            (thetaMonoBernCoeff D (exponent N)) w)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _
          (ih hprefix)) ?_
      refine Q'.add_eqv_congr_left
        (finiteSignedMonomialEval weight exponent w N) _ _
        (Q'.mul_eqv_congr_left (Q'.ofInt (weight N)) _ _
          (thetaMonoBernCoeff_eval D (exponent N) w hlast))

#print axioms signedBernsteinEval_add
#print axioms signedBernsteinEval_scale
#print axioms finiteSignedMonomialBernsteinRow_succ
#print axioms finiteSignedMonomialBernsteinRow_eval

end YMGap.Continuum.BernsteinSignedMonomialReconstruction
