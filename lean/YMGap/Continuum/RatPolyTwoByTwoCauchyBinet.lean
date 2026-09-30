/-
# Finite two-by-two Cauchy--Binet over rational polynomials

The determinant of four sums of rank-one polynomial terms is a sum over
unordered pairs of list positions. Equal-position contributions cancel
exactly. No positivity, distinct-label hypothesis, or division by two is
used. This is coefficientwise algebra, so arbitrary exterior polynomial
coefficients and signed feature coefficients remain in place.
-/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

namespace YMGap.Continuum.RatPolyTwoByTwoCauchyBinet

set_option autoImplicit false

open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

/-- A finite sum of products, retaining list-position multiplicity. -/
def productSum {Index : Type} (f g : Index → RatPoly) : List Index → RatPoly
  | [] => polyZero
  | i :: rest => polyAdd (polyMul (f i) (g i)) (productSum f g rest)

/-- The ordered two-by-two minor on two list positions. -/
def minor {Index : Type} (f g : Index → RatPoly) (i j : Index) : RatPoly :=
  polyAdd (polyMul (f i) (g j)) (polyNeg (polyMul (f j) (g i)))

/-- Each unordered pair of positions appears exactly once. -/
def pairSum {Index : Type} (a b c d : Index → RatPoly) : List Index → RatPoly
  | [] => polyZero
  | i :: rest => polyAdd
      (productSum (minor a b i) (minor c d i) rest)
      (pairSum a b c d rest)

private def cross {Index : Type} (a b c d : Index → RatPoly)
    (i : Index) (rest : List Index) : RatPoly :=
  polyAdd
    (polyAdd
      (polyMul (polyMul (a i) (c i)) (productSum b d rest))
      (polyMul (polyMul (b i) (d i)) (productSum a c rest)))
    (polyNeg (polyAdd
      (polyMul (polyMul (a i) (d i)) (productSum b c rest))
      (polyMul (polyMul (b i) (c i)) (productSum a d rest))))

private def minorExpr (a b c d : PolyExpr) : PolyExpr :=
  .add (.mul a b) (.neg (.mul c d))

private def crossExpr (a b c d bd ac bc ad : PolyExpr) : PolyExpr :=
  .add
    (.add (.mul (.mul a c) bd) (.mul (.mul b d) ac))
    (.neg (.add (.mul (.mul a d) bc) (.mul (.mul b c) ad)))

private theorem productSum_minors {Index : Type} (a b c d : Index → RatPoly)
    (i : Index) (rest : List Index) :
    RatPolyCoeffEqv (productSum (minor a b i) (minor c d i) rest)
      (cross a b c d i rest) := by
  induction rest with
  | nil =>
      have hfirst : RatPolyCoeffEqv
          (polyAdd
            (polyMul (polyMul (a i) (c i)) polyZero)
            (polyMul (polyMul (b i) (d i)) polyZero)) polyZero :=
        (RatPolyCoeffEqv.mul_zero_right _).add (RatPolyCoeffEqv.mul_zero_right _)
      have hsecond : RatPolyCoeffEqv
          (polyAdd
            (polyMul (polyMul (a i) (d i)) polyZero)
            (polyMul (polyMul (b i) (c i)) polyZero)) polyZero :=
        (RatPolyCoeffEqv.mul_zero_right _).add (RatPolyCoeffEqv.mul_zero_right _)
      change RatPolyCoeffEqv polyZero (cross a b c d i [])
      unfold cross
      change RatPolyCoeffEqv polyZero
        (polyAdd
          (polyAdd
            (polyMul (polyMul (a i) (c i)) polyZero)
            (polyMul (polyMul (b i) (d i)) polyZero))
          (polyNeg (polyAdd
            (polyMul (polyMul (a i) (d i)) polyZero)
            (polyMul (polyMul (b i) (c i)) polyZero))))
      exact (hfirst.add (RatPolyCoeffEqv.neg hsecond)).symm
  | cons j tail ih =>
      have hring : RatPolyCoeffEqv
          (polyAdd
            (polyMul (minor a b i j) (minor c d i j))
            (cross a b c d i tail))
          (cross a b c d i (j :: tail)) := by
        let env : Nat → RatPoly := fun
          | 0 => a i | 1 => b i | 2 => c i | 3 => d i
          | 4 => a j | 5 => b j | 6 => c j | 7 => d j
          | 8 => productSum b d tail | 9 => productSum a c tail
          | 10 => productSum b c tail | _ => productSum a d tail
        have h := coeffEvalExpr_eqv_of_normalize_eq
          (.add
            (.mul
              (minorExpr (.var 0) (.var 5) (.var 4) (.var 1))
              (minorExpr (.var 2) (.var 7) (.var 6) (.var 3)))
            (crossExpr (.var 0) (.var 1) (.var 2) (.var 3)
              (.var 8) (.var 9) (.var 10) (.var 11)))
          (crossExpr (.var 0) (.var 1) (.var 2) (.var 3)
            (.add (.mul (.var 5) (.var 7)) (.var 8))
            (.add (.mul (.var 4) (.var 6)) (.var 9))
            (.add (.mul (.var 5) (.var 6)) (.var 10))
            (.add (.mul (.var 4) (.var 7)) (.var 11)))
          (by decide) env
        simpa only [env, coeffEvalExpr, minorExpr, crossExpr, minor,
          cross, productSum] using h
      exact ((RatPolyCoeffEqv.refl _).add ih).trans hring

/-- Coefficientwise two-by-two Cauchy--Binet on list positions. The diagonal
terms are absent identically, with no assumptions on the four families. -/
theorem determinant_eq_pairSum {Index : Type} (a b c d : Index → RatPoly)
    (xs : List Index) :
    RatPolyCoeffEqv
      (polyAdd
        (polyMul (productSum a c xs) (productSum b d xs))
        (polyNeg (polyMul (productSum b c xs) (productSum a d xs))))
      (pairSum a b c d xs) := by
  induction xs with
  | nil =>
      exact RatPolyCoeffEqv.refl polyZero
  | cons i rest ih =>
      have hring : RatPolyCoeffEqv
          (polyAdd
            (polyMul (productSum a c (i :: rest))
              (productSum b d (i :: rest)))
            (polyNeg (polyMul (productSum b c (i :: rest))
              (productSum a d (i :: rest)))))
          (polyAdd (cross a b c d i rest)
            (polyAdd
              (polyMul (productSum a c rest) (productSum b d rest))
              (polyNeg (polyMul (productSum b c rest)
                (productSum a d rest))))) := by
        let env : Nat → RatPoly := fun
          | 0 => a i | 1 => b i | 2 => c i | 3 => d i
          | 4 => productSum a c rest | 5 => productSum b d rest
          | 6 => productSum b c rest | _ => productSum a d rest
        have h := coeffEvalExpr_eqv_of_normalize_eq
          (.add
            (.mul
              (.add (.mul (.var 0) (.var 2)) (.var 4))
              (.add (.mul (.var 1) (.var 3)) (.var 5)))
            (.neg (.mul
              (.add (.mul (.var 1) (.var 2)) (.var 6))
              (.add (.mul (.var 0) (.var 3)) (.var 7)))))
          (.add
            (crossExpr (.var 0) (.var 1) (.var 2) (.var 3)
              (.var 5) (.var 4) (.var 6) (.var 7))
            (.add (.mul (.var 4) (.var 5))
              (.neg (.mul (.var 6) (.var 7)))))
          (by decide) env
        simpa only [env, coeffEvalExpr, crossExpr, cross, productSum] using h
      exact hring.trans (((productSum_minors a b c d i rest).symm).add ih)

#print axioms productSum
#print axioms minor
#print axioms pairSum
#print axioms determinant_eq_pairSum

end YMGap.Continuum.RatPolyTwoByTwoCauchyBinet
