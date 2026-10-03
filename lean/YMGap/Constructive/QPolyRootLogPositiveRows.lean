/-
Computed NONNEGATIVE u/h rows for the ORIGINAL finite S and F.
The positive primitive is pinned by actual coefficient derivatives and
zero initial values.  Cancellation occurs at polynomials, never at a root
operator. No assumed sign, spectral floor or analytic input is required.
The coefficient-to-original-operator lift is a separate obligation.
-/

import YMGap.Constructive.QPolyUHRowFiniteSums
import YMGap.Constructive.QPolyUHRowPrimitive
import YMGap.Constructive.QPolyComplementCancellation
import YMGap.Constructive.QPolyComplementaryTelescope
import YMGap.Constructive.QPolyRootLogRemainderDerivative

namespace YMGap.Constructive.QPolyRootLogPositiveRows

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Constructive.QPolyPositivePrimitive
open YMGap.Constructive.QPolyFiniteGeometric
open YMGap.Constructive.QPolyFinitePowerDifference
open YMGap.Constructive.QPolyUHRow
open YMGap.Constructive.QPolyUHRowPrimitive
open YMGap.Constructive.QPolyUHRowFiniteSums
open YMGap.Constructive.QPolyComplementCancellation
open YMGap.Constructive.QPolyComplementaryTelescope
open YMGap.Constructive.QPolyRootLogDifference
open YMGap.Constructive.QPolyRootLogInitial
open YMGap.Constructive.QPolyRootLogRemainderDerivative

def uRow : Row := singleton 1 0
def hRow : Row := singleton 0 1

def defectRow (n : Nat) : Row := multiply hRow (geometricRow uRow (n+1))
def complementaryRow (n : Nat) : Row := geometricRow uRow n ++ geometricRow hRow n
def derivativeRow (n m : Nat) : Row :=
  scale (Q'.ofNat (n+1))
    (multiply hRow (multiply (complementaryRow n)
      (differenceRow (defectRow n) (power hRow (n+1)) m)))
def sRow (n m : Nat) : Row := integralRow (derivativeRow n m)
def remainderDerivativeRow (n m : Nat) : Row :=
  scale (Q'.ofNat (n+1))
    (multiply (power uRow n) (sRow n m ++ power hRow ((n+1)*m)))
def fRow (n m : Nat) : Row := integralRow (remainderDerivativeRow n m)

private theorem mul_one_right (p : Poly) : CoeffEqv (pmul p [1]) p :=
  (coeffEqv_pmul_comm p [1]).trans (coeffEqv_pmul_one_left p)

private theorem uRow_pin : CoeffEqv (polynomial uRow) complement :=
  (polynomial_singleton 1 0).trans
    ((mul_one_right _).trans (mul_one_right complement))

private theorem hRow_pin : CoeffEqv (polynomial hRow) coordinate :=
  (polynomial_singleton 0 1).trans
    ((coeffEqv_pmul_one_left _).trans (mul_one_right coordinate))

private theorem power_uRow_pin (n : Nat) :
    CoeffEqv (polynomial (power uRow n)) (polynomialPower complement n) :=
  (polynomial_power uRow n).trans (polynomialPower_congr uRow_pin n)

private theorem power_hRow_pin (n : Nat) :
    CoeffEqv (polynomial (power hRow n)) (polynomialPower coordinate n) :=
  (polynomial_power hRow n).trans (polynomialPower_congr hRow_pin n)

private theorem defectRow_pin (n : Nat) :
    CoeffEqv (polynomial (defectRow n)) (rootDefect n) :=
  (polynomial_multiply _ _).trans
    ((hRow_pin.pmul ((polynomial_geometricRow _ _).trans
      (geometric_congr uRow_pin (n+1)))).trans (root_defect_positive_factor n).symm)

private theorem complementaryRow_pin (n : Nat) :
    CoeffEqv (polynomial (complementaryRow n)) (complementaryPowerPolynomial n) :=
  (polynomial_append _ _).trans
    (CoeffEqv.padd
      ((polynomial_geometricRow _ _).trans (geometric_congr uRow_pin n))
      ((polynomial_geometricRow _ _).trans (geometric_congr hRow_pin n)))

private theorem derivativeRow_pin (n m : Nat) :
    CoeffEqv (polynomial (derivativeRow n m))
      (pscale (Q'.ofNat (n+1))
        (pmul coordinate (pmul (complementaryPowerPolynomial n)
          (powerDifferenceRow (rootDefect n) (polynomialPower coordinate (n+1)) m)))) :=
  (polynomial_scale _ _).trans
    (((polynomial_multiply _ _).trans
      (hRow_pin.pmul ((polynomial_multiply _ _).trans
        ((complementaryRow_pin n).pmul
          ((polynomial_differenceRow _ _ _).trans
            (powerDifference_congr (defectRow_pin n) (power_hRow_pin (n+1)) m)))))).pscale _)

private theorem sub_congr {p p' q q' : Poly}
    (hp : CoeffEqv p p') (hq : CoeffEqv q q') :
    CoeffEqv (psub p q) (psub p' q') := CoeffEqv.padd hp hq.pneg

/-- The actual original S' is the computed positive derivative row. -/
theorem original_derivative_row (n m : Nat) :
    CoeffEqv (pderiv (rootLogDifference n m)) (polynomial (derivativeRow n m)) := by
  let N := Q'.ofNat (n+1)
  let P := complementaryPowerPolynomial n
  let K := powerDifferenceRow (rootDefect n) (polynomialPower coordinate (n+1)) m
  have hfactor : CoeffEqv
      (pscale N (psub (polynomialPower (rootDefect n) m)
        (polynomialPower coordinate ((n+1)*m))))
      (pscale N (pmul complement (pmul coordinate (pmul P K)))) :=
    ((sub_congr (CoeffEqv.refl _)
      (polynomialPower_iterated coordinate (n+1) m).symm).pscale N).trans
      (((powerDifference_telescope (rootDefect n)
        (polynomialPower coordinate (n+1)) m).symm.trans
        (((complementary_power_defect n).pmul (CoeffEqv.refl K)).trans
          ((coeffEqv_pmul_assoc (pmul complement coordinate) P K).trans
            (coeffEqv_pmul_assoc complement coordinate (pmul P K))))).pscale N)
  have hrow : CoeffEqv (pmul complement (polynomial (derivativeRow n m)))
      (pscale N (pmul complement (pmul coordinate (pmul P K)))) :=
    ((CoeffEqv.refl complement).pmul (derivativeRow_pin n m)).trans
      (coeffEqv_pmul_pscale N complement _)
  exact complement_mul_injective
    ((rootLogDifference_cleared_derivative n m).trans (hfactor.trans hrow.symm))

/-- Coefficientwise identification with ORIGINAL S, not a positive surrogate. -/
theorem original_sRow (n m : Nat) :
    CoeffEqv (polynomial (sRow n m)) (rootLogDifference n m) :=
  derivative_initial_unique _ _
    ((integralRow_derivative _).trans (original_derivative_row n m).symm)
    (Q'.eqv_trans _ _ _ (integralRow_zero _) (Q'.eqv_symm (rootLogDifference_zero n m)))

private theorem remainderDerivativeRow_pin (n m : Nat) :
    CoeffEqv (polynomial (remainderDerivativeRow n m))
      (pscale (Q'.ofNat (n+1))
        (pmul (polynomialPower complement n)
          (padd (rootLogDifference n m) (polynomialPower coordinate ((n+1)*m))))) :=
  (polynomial_scale _ _).trans
    (((polynomial_multiply _ _).trans
      ((power_uRow_pin n).pmul ((polynomial_append _ _).trans
        (CoeffEqv.padd (original_sRow n m) (power_hRow_pin _))))).pscale _)

/-- Coefficientwise identification with ORIGINAL F. -/
theorem original_fRow (n m : Nat) :
    CoeffEqv (polynomial (fRow n m)) (rootLogRemainder n m) :=
  derivative_initial_unique _ _
    ((integralRow_derivative _).trans
      ((remainderDerivativeRow_pin n m).trans (rootLogRemainder_derivative n m).symm))
    (Q'.eqv_trans _ _ _ (integralRow_zero _) (Q'.eqv_symm (rootLogRemainder_zero n m)))

private theorem nonnegative_defectRow (n : Nat) : nonnegative (defectRow n) :=
  nonnegative_multiply _ _ (nonnegative_singleton 0 1)
    (nonnegative_geometricRow _ (nonnegative_singleton 1 0) (n+1))

private theorem nonnegative_complementaryRow (n : Nat) : nonnegative (complementaryRow n) :=
  nonnegative_append _ _
    (nonnegative_geometricRow _ (nonnegative_singleton 1 0) n)
    (nonnegative_geometricRow _ (nonnegative_singleton 0 1) n)

theorem nonnegative_derivativeRow (n m : Nat) : nonnegative (derivativeRow n m) :=
  nonnegative_scale _ (Q'.le_of_lt (Q'.ofNat_succ_pos n)) _
    (nonnegative_multiply _ _ (nonnegative_singleton 0 1)
      (nonnegative_multiply _ _ (nonnegative_complementaryRow n)
        (nonnegative_differenceRow _ _ (nonnegative_defectRow n)
          (nonnegative_power _ (nonnegative_singleton 0 1) (n+1)) m)))

theorem nonnegative_sRow (n m : Nat) : nonnegative (sRow n m) :=
  nonnegative_integralRow _ (nonnegative_derivativeRow n m)

theorem nonnegative_fRow (n m : Nat) : nonnegative (fRow n m) :=
  nonnegative_integralRow _
    (nonnegative_scale _ (Q'.le_of_lt (Q'.ofNat_succ_pos n)) _
      (nonnegative_multiply _ _
        (nonnegative_power _ (nonnegative_singleton 1 0) n)
        (nonnegative_append _ _ (nonnegative_sRow n m)
          (nonnegative_power _ (nonnegative_singleton 0 1) ((n+1)*m)))))

#print axioms derivativeRow
#print axioms sRow
#print axioms fRow
#print axioms original_derivative_row
#print axioms original_sRow
#print axioms original_fRow
#print axioms nonnegative_derivativeRow
#print axioms nonnegative_sRow
#print axioms nonnegative_fRow

end YMGap.Constructive.QPolyRootLogPositiveRows
