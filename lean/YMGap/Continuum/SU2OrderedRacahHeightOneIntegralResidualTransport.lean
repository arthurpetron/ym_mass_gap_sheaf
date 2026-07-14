/-
# Transport to the fully integral height-one residual

One final global factor two clears the complementary inner binomials.  This
module transports the quadratic normal forms through the complete exchange
and carrier scalars, producing a residual with only natural and integer
casts and ring operations.
-/

import YMGap.Continuum.SU2OrderedRacahHeightOneQuadraticNormalForm

namespace YMGap.Continuum.SU2OrderedRacahHeightOneIntegralResidualTransport

open YMGap.Constructive
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedRacahHeightOneLegacyCancellation
open YMGap.Continuum.SU2OrderedRacahHeightOnePolynomialPropagation
open YMGap.Continuum.SU2OrderedRacahHeightOneOuterCommonFactor
open YMGap.Continuum.SU2OrderedRacahHeightOneScalarPolynomial
open YMGap.Continuum.SU2OrderedRacahHeightOneReducedExchangePolynomial
open YMGap.Continuum.SU2OrderedRacahHeightOneCarrierScalarPolynomial
open YMGap.Continuum.SU2OrderedRacahHeightOneExactResidualPolynomial
open YMGap.Continuum.SU2OrderedRacahHeightOneScaledResidualPolynomial
open YMGap.Continuum.SU2OrderedRacahHeightOneQuadraticNormalForm

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero]; try ac_rfl))

private theorem mul_eqv_congr {a b c d : Q'}
    (hab : a ≈ b) (hcd : c ≈ d) : a * c ≈ b * d :=
  Q'.eqv_trans _ (b * c) _
    (Q'.mul_eqv_congr_right _ _ _ hab)
    (Q'.mul_eqv_congr_left _ _ _ hcd)

/-- Aligned exchange coordinate-two outer scalar in integral form. -/
def reducedHeightOneOuterTwoIntegralScalar {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i : Nat) : Q' :=
  (Q'.ofNat (i - q.r + 3) * Q'.ofNat (i - q.r + 2)) *
    outerSecondTwoIntegralScalar a q.intermediate q.r (i - 1)

theorem reduced_height_one_outer_two_integral {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i : Nat) (hr : 2 ≤ q.r) :
    reducedHeightOneOuterTwoScalar q i ≈
      reducedHeightOneOuterTwoIntegralScalar q i := by
  unfold reducedHeightOneOuterTwoScalar reducedHeightOneOuterTwoIntegralScalar
  exact Q'.mul_eqv_congr_left _ _ _
    (outer_second_two_integral a q.intermediate q.r (i - 1) hr)

/-- Twice the complete exchange sample at outer coordinate two. -/
def heightOneExchangeTwoIntegralScalar {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l : Nat) : Q' :=
  heightTwoFullPolynomialTwice (b - 1) (c - 1) (q.p - 1) j l *
    reducedHeightOneOuterTwoIntegralScalar q i

/-- Twice each of the other exchange samples needs no further
normalization. -/
def heightOneExchangeFirstOneTwice {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l : Nat) : Q' :=
  Q'.ofNat 2 * reducedHeightOneExchangeFirstOneScalar q i j l

def heightOneExchangeSecondOneTwice {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l : Nat) : Q' :=
  Q'.ofNat 2 * reducedHeightOneExchangeSecondOneScalar q i j l

def heightOneExchangeZeroTwice {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l : Nat) : Q' :=
  Q'.ofNat 2 * reducedHeightOneExchangeZeroScalar q i j l

/-- Fully integral exchange scalar. -/
def heightOneIntegralExchangeScalar {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l : Nat) : Q' :=
  (Q'.ofNat i * Q'.ofNat (b - j)) *
      (Q'.ofNat (c - l) * heightOneExchangeTwoIntegralScalar q i j l +
        Q'.ofNat l * heightOneExchangeFirstOneTwice q i j l) +
    -((Q'.ofNat (a - i) * Q'.ofNat j) *
      (Q'.ofNat (c - l) * heightOneExchangeSecondOneTwice q i j l +
        Q'.ofNat l * heightOneExchangeZeroTwice q i j l))

/-- Twice the exchange scalar is its integral normal form. -/
theorem height_one_exchange_scalar_integral {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l : Nat)
    (hj : 2 ≤ j) (hl : 2 ≤ l) (hr : 2 ≤ q.r) :
    Q'.ofNat 2 * reducedHeightOneExchangeScalar q i j l ≈
      heightOneIntegralExchangeScalar q i j l := by
  let I := reducedHeightOneInnerTwoScalar q j l
  let O := reducedHeightOneOuterTwoScalar q i
  let I2 := heightTwoFullPolynomialTwice
    (b - 1) (c - 1) (q.p - 1) j l
  let O2 := reducedHeightOneOuterTwoIntegralScalar q i
  have hi := height_two_full_polynomial_twice
    (b - 1) (c - 1) (q.p - 1) j l hj hl
  have ho := reduced_height_one_outer_two_integral q i hr
  have hx0 : Q'.ofNat 2 * (I * O) ≈ I2 * O2 := by
    refine Q'.eqv_trans _ ((Q'.ofNat 2 * I) * O) _ (by ring_qeqv) ?_
    exact mul_eqv_congr (by simpa only [I, I2,
      reducedHeightOneInnerTwoScalar] using hi) ho
  have hx0' : Q'.ofNat 2 *
      reducedHeightOneExchangeTwoScalar q i j l ≈ I2 * O2 := by
    simpa only [reducedHeightOneExchangeTwoScalar, I, O] using hx0
  unfold reducedHeightOneExchangeScalar heightOneIntegralExchangeScalar
    heightOneExchangeTwoIntegralScalar heightOneExchangeFirstOneTwice
    heightOneExchangeSecondOneTwice heightOneExchangeZeroTwice
  refine Q'.eqv_trans _
    ((Q'.ofNat i * Q'.ofNat (b - j)) *
        (Q'.ofNat (c - l) *
            (Q'.ofNat 2 * reducedHeightOneExchangeTwoScalar q i j l) +
          Q'.ofNat l *
            (Q'.ofNat 2 * reducedHeightOneExchangeFirstOneScalar q i j l)) +
      -((Q'.ofNat (a - i) * Q'.ofNat j) *
        (Q'.ofNat (c - l) *
            (Q'.ofNat 2 * reducedHeightOneExchangeSecondOneScalar q i j l) +
          Q'.ofNat l *
            (Q'.ofNat 2 * reducedHeightOneExchangeZeroScalar q i j l)))) _
    (by ring_qeqv) ?_
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _ hx0') (Q'.eqv_refl _)))
    (Q'.neg_eqv_congr _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.eqv_refl _))))

/-- Lower outer scalar on the carrier side in integral form. -/
def heightOneCarrierLowerOuterIntegralScalar (a n r i : Nat) : Q' :=
  (Q'.ofNat n * Q'.ofNat (n - 1)) *
    outerSecondTwoIntegralScalar a (n + 2) (r + 1) i

theorem height_one_carrier_lower_outer_integral
    (a n r i : Nat) (hr : 1 ≤ r) :
    heightOneCarrierLowerOuterScalar a n r i ≈
      heightOneCarrierLowerOuterIntegralScalar a n r i := by
  unfold heightOneCarrierLowerOuterScalar
    heightOneCarrierLowerOuterIntegralScalar
  exact Q'.mul_eqv_congr_left _ _ _
    (outer_second_two_integral a (n + 2) (r + 1) i (by omega))

/-- Twice the lower carrier sample in integral form. -/
def heightOneCarrierLowerIntegralScalar {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l : Nat) : Q' :=
  heightTwoFullPolynomialTwice b c (q.p - 1) j l *
    heightOneCarrierLowerOuterIntegralScalar a q.intermediate q.r i

/-- Fully integral, denominator-cleared carrier side. -/
def heightOneIntegralScaledCarrierSideScalar {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l : Nat) : Q' :=
  heightOneScaledLowerCoefficient q *
      heightOneCarrierLowerIntegralScalar q i j l +
    heightOneScaledDiagonalCoefficient q *
      (Q'.ofNat 2 * heightOneCarrierDiagonalScalar q i j l) +
    heightOneScaledUpperCoefficient q *
      (Q'.ofNat 2 * heightOneCarrierUpperScalar q)

theorem height_one_scaled_carrier_scalar_integral {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l : Nat)
    (hj : 2 ≤ j) (hl : 2 ≤ l) (hr : 1 ≤ q.r) :
    Q'.ofNat 2 * heightOneScaledCarrierSideScalar q i j l ≈
      heightOneIntegralScaledCarrierSideScalar q i j l := by
  let I := heightOneCarrierLowerInnerScalar q j l
  let O := heightOneCarrierLowerOuterScalar a q.intermediate q.r i
  let I2 := heightTwoFullPolynomialTwice b c (q.p - 1) j l
  let O2 := heightOneCarrierLowerOuterIntegralScalar
    a q.intermediate q.r i
  have hi := height_two_full_polynomial_twice
    b c (q.p - 1) j l hj hl
  have ho := height_one_carrier_lower_outer_integral
    a q.intermediate q.r i hr
  have hx : Q'.ofNat 2 * (I * O) ≈ I2 * O2 := by
    refine Q'.eqv_trans _ ((Q'.ofNat 2 * I) * O) _ (by ring_qeqv) ?_
    exact mul_eqv_congr (by simpa only [I, I2,
      heightOneCarrierLowerInnerScalar] using hi) ho
  unfold heightOneScaledCarrierSideScalar
    heightOneIntegralScaledCarrierSideScalar
    heightOneCarrierLowerScalar heightOneCarrierLowerIntegralScalar
  refine Q'.eqv_trans _
    (heightOneScaledLowerCoefficient q * (Q'.ofNat 2 * (I * O)) +
      heightOneScaledDiagonalCoefficient q *
        (Q'.ofNat 2 * heightOneCarrierDiagonalScalar q i j l) +
      heightOneScaledUpperCoefficient q *
        (Q'.ofNat 2 * heightOneCarrierUpperScalar q)) _
    (by simp only [I, O]; ring_qeqv) ?_
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ hx) (Q'.eqv_refl _))
    (Q'.eqv_refl _)

/-- Fully integral residual polynomial. -/
def heightOneIntegralResidualPolynomial {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l : Nat) : Q' :=
  (heightOneJacobiScale q * heightOneBulkExchangeScale q) *
      heightOneIntegralExchangeScalar q i j l +
    -(heightOneBulkCarrierScale q i j l *
      heightOneIntegralScaledCarrierSideScalar q i j l)

theorem height_one_scaled_residual_integral {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l : Nat)
    (hj : 2 ≤ j) (hl : 2 ≤ l) (hr : 2 ≤ q.r) :
    Q'.ofNat 2 * heightOneScaledResidualPolynomial q i j l ≈
      heightOneIntegralResidualPolynomial q i j l := by
  have hx := height_one_exchange_scalar_integral q i j l hj hl hr
  have hy := height_one_scaled_carrier_scalar_integral
    q i j l hj hl (by omega)
  unfold heightOneScaledResidualPolynomial heightOneIntegralResidualPolynomial
  refine Q'.eqv_trans _
    ((heightOneJacobiScale q * heightOneBulkExchangeScale q) *
        (Q'.ofNat 2 * reducedHeightOneExchangeScalar q i j l) +
      -(heightOneBulkCarrierScale q i j l *
        (Q'.ofNat 2 * heightOneScaledCarrierSideScalar q i j l))) _
    (by ring_qeqv) ?_
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left _ _ _ hx)
    (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ hy))

end YMGap.Continuum.SU2OrderedRacahHeightOneIntegralResidualTransport

#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneIntegralResidualTransport.height_one_exchange_scalar_integral
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneIntegralResidualTransport.height_one_scaled_carrier_scalar_integral
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneIntegralResidualTransport.height_one_scaled_residual_integral
