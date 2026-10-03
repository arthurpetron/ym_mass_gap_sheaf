/-
# Finite geometric and difference-of-powers data in u/h monomial rows

The rows are computed by append and actual row multiplication. Their
polynomials are identified coefficientwise with the existing finite sums;
nonnegative input weights give nonnegative output weights. No positivity
conclusion, coefficient equality, or cutoff is supplied as an extra premise.
-/

import YMGap.Constructive.QPolyUHRow

namespace YMGap.Constructive.QPolyUHRowFiniteSums

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Constructive.QPolyPositivePrimitive (polynomialPower)
open YMGap.Constructive.QPolyFiniteGeometric
open YMGap.Constructive.QPolyFinitePowerDifference
open YMGap.Constructive.QPolyUHRow

/-- The computed sum of row powers with exponents below n. -/
def geometricRow (r : Row) : Nat → Row
  | 0 => []
  | n+1 => geometricRow r n ++ power r n

/-- The computed mixed-power row, including the empty case. -/
def differenceRow (p q : Row) : Nat → Row
  | 0 => []
  | m+1 => multiply p (differenceRow p q m) ++ power q m

theorem polynomial_geometricRow (r : Row) (n : Nat) :
    CoeffEqv (polynomial (geometricRow r n))
      (geometricPolynomial (polynomial r) n) := by
  induction n with
  | zero => exact CoeffEqv.refl []
  | succ n ih =>
      exact (polynomial_append (geometricRow r n) (power r n)).trans
        (CoeffEqv.padd ih (polynomial_power r n))

theorem nonnegative_geometricRow (r : Row) (hr : nonnegative r) (n : Nat) :
    nonnegative (geometricRow r n) := by
  induction n with
  | zero => exact True.intro
  | succ n ih => exact nonnegative_append _ _ ih (nonnegative_power r hr n)

theorem polynomial_differenceRow (p q : Row) (m : Nat) :
    CoeffEqv (polynomial (differenceRow p q m))
      (powerDifferenceRow (polynomial p) (polynomial q) m) := by
  induction m with
  | zero => exact CoeffEqv.refl []
  | succ m ih =>
      exact (polynomial_append (multiply p (differenceRow p q m)) (power q m)).trans
        (CoeffEqv.padd
          ((polynomial_multiply p (differenceRow p q m)).trans
            ((CoeffEqv.refl (polynomial p)).pmul ih))
          (polynomial_power q m))

theorem nonnegative_differenceRow (p q : Row)
    (hp : nonnegative p) (hq : nonnegative q) (m : Nat) :
    nonnegative (differenceRow p q m) := by
  induction m with
  | zero => exact True.intro
  | succ m ih =>
      exact nonnegative_append _ _
        (nonnegative_multiply p (differenceRow p q m) hp ih) (nonnegative_power q hq m)

/-- The original polynomial powers respect padded coefficient equality. -/
theorem polynomialPower_congr {p q : Poly} (h : CoeffEqv p q) (n : Nat) :
    CoeffEqv (polynomialPower p n) (polynomialPower q n) := by
  induction n with
  | zero => exact CoeffEqv.refl [1]
  | succ n ih => exact h.pmul ih

theorem geometric_congr {p q : Poly} (h : CoeffEqv p q) (n : Nat) :
    CoeffEqv (geometricPolynomial p n) (geometricPolynomial q n) := by
  induction n with
  | zero => exact CoeffEqv.refl []
  | succ n ih => exact CoeffEqv.padd ih (polynomialPower_congr h n)

theorem powerDifference_congr {p p' q q' : Poly}
    (hp : CoeffEqv p p') (hq : CoeffEqv q q') (m : Nat) :
    CoeffEqv (powerDifferenceRow p q m) (powerDifferenceRow p' q' m) := by
  induction m with
  | zero => exact CoeffEqv.refl []
  | succ m ih => exact CoeffEqv.padd (hp.pmul ih) (polynomialPower_congr hq m)

#print axioms geometricRow
#print axioms differenceRow
#print axioms polynomial_geometricRow
#print axioms nonnegative_geometricRow
#print axioms polynomial_differenceRow
#print axioms nonnegative_differenceRow
#print axioms polynomialPower_congr
#print axioms geometric_congr
#print axioms powerDifference_congr

end YMGap.Constructive.QPolyUHRowFiniteSums
