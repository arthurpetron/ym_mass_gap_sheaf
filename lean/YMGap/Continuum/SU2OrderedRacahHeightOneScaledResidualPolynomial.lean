/-
# Clearing the Jacobi denominators in the height-one residual

The exact residual contains the lower, diagonal, and upper correction
coefficients.  Their common positive scale is
`8 n (n+1) (n+2)`, where `n` is the middle intermediate label.  After
scaling, all three coefficients are replaced by their exact integer
numerators, leaving a pure finite polynomial certificate.
-/

import YMGap.Continuum.SU2OrderedRacahHeightOneExactResidualPolynomial

namespace YMGap.Continuum.SU2OrderedRacahHeightOneScaledResidualPolynomial

open YMGap.Constructive
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionThreeCarrier
open YMGap.Continuum.SU2OrderedRacahTridiagonalCoefficients
open YMGap.Continuum.SU2OrderedRacahHeightOneReducedExchangePolynomial
open YMGap.Continuum.SU2OrderedRacahHeightOneCarrierScalarPolynomial
open YMGap.Continuum.SU2OrderedRacahHeightOneExactResidualPolynomial

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero]; try ac_rfl))

private theorem ofNat_mul_eqv (a b : Nat) :
    Q'.ofNat a * Q'.ofNat b ≈ Q'.ofNat (a * b) := by
  unfold Q'.eqv
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast]
  push_cast
  simp

/-- Common exact Jacobi denominator scale. -/
def heightOneJacobiScale {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) : Q' :=
  (Q'.ofNat 8 * Q'.ofNat q.intermediate) *
    (Q'.ofNat (q.intermediate + 2) * Q'.ofNat (q.intermediate + 1))

/-- Lower coefficient numerator with the remaining common-scale factor. -/
def heightOneScaledLowerCoefficient {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) : Q' :=
  (Q'.ofNat 8 * Q'.ofNat q.intermediate) *
    Q'.ofNat ((b - q.p + 1) * (c - q.p + 1) *
      (q.intermediate - q.r + 1))

/-- Diagonal difference numerator with the remaining factor `n+1`. -/
def heightOneScaledDiagonalCoefficient {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) : Q' :=
  Q'.ofNat (q.intermediate + 1) *
    Q'.ofInt (omegaCorrectionDiagonalNumerator a b c d q.intermediate)

/-- Upper coefficient numerator with the remaining scale `8(n+2)`. -/
def heightOneScaledUpperCoefficient {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) : Q' :=
  (Q'.ofNat 8 * Q'.ofNat (q.intermediate + 2)) *
    Q'.ofNat (q.r * (a - q.r + 1) *
      (a + q.intermediate - q.r + 1))

/-- The lower coefficient after clearing the common denominator. -/
theorem height_one_scaled_lower_coefficient {a b c d : Nat}
    (qm q : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (hprev : q.p = qm.p + 1) :
    heightOneJacobiScale q *
        omegaCorrectionLowerCoefficient a b c d q.p ≈
      heightOneScaledLowerCoefficient q := by
  let A := Q'.ofNat 8 * Q'.ofNat q.intermediate
  let D := Q'.ofNat (q.intermediate + 2) *
    Q'.ofNat (q.intermediate + 1)
  let L := omegaCorrectionLowerCoefficient a b c d q.p
  let N := Q'.ofNat ((b - q.p + 1) * (c - q.p + 1) *
    (q.intermediate - q.r + 1))
  have hcoeff := omegaCorrectionLowerCoefficient_closed qm q hp hprev
  have hden := ofNat_mul_eqv (q.intermediate + 2) (q.intermediate + 1)
  have hcore : D * L ≈ N :=
    Q'.eqv_trans _
      (Q'.ofNat ((q.intermediate + 2) * (q.intermediate + 1)) * L) _
      (Q'.mul_eqv_congr_right _ _ L hden) (by simpa only [N] using hcoeff)
  unfold heightOneJacobiScale heightOneScaledLowerCoefficient
  refine Q'.eqv_trans _ (A * (D * L)) _ (by simp only [A, D, L]; ring_qeqv) ?_
  exact Q'.mul_eqv_congr_left A _ _ hcore

/-- The upper coefficient after clearing the common denominator. -/
theorem height_one_scaled_upper_coefficient {a b c d : Nat}
    (q qp : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (hnext : qp.p = q.p + 1) :
    heightOneJacobiScale q *
        omegaCorrectionUpperCoefficient a b c d q.p ≈
      heightOneScaledUpperCoefficient q := by
  let A := Q'.ofNat 8 * Q'.ofNat (q.intermediate + 2)
  let D := Q'.ofNat q.intermediate * Q'.ofNat (q.intermediate + 1)
  let U := omegaCorrectionUpperCoefficient a b c d q.p
  let N := Q'.ofNat (q.r * (a - q.r + 1) *
    (a + q.intermediate - q.r + 1))
  have hcoeff := omegaCorrectionUpperCoefficient_closed q qp hp hnext
  have hden := ofNat_mul_eqv q.intermediate (q.intermediate + 1)
  have hcore : D * U ≈ N :=
    Q'.eqv_trans _
      (Q'.ofNat (q.intermediate * (q.intermediate + 1)) * U) _
      (Q'.mul_eqv_congr_right _ _ U hden) (by simpa only [N] using hcoeff)
  unfold heightOneJacobiScale heightOneScaledUpperCoefficient
  refine Q'.eqv_trans _ (A * (D * U)) _ (by simp only [A, D, U]; ring_qeqv) ?_
  exact Q'.mul_eqv_congr_left A _ _ hcore

/-- The diagonal coefficient after clearing the common denominator. -/
theorem height_one_scaled_diagonal_coefficient {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (hn : q.intermediate ≠ 0) :
    heightOneJacobiScale q *
        omegaCorrectionDiagonalCoefficient a b c d q.p ≈
      heightOneScaledDiagonalCoefficient q := by
  let A := Q'.ofNat (q.intermediate + 1)
  let D := Q'.ofNat 8 * Q'.ofNat q.intermediate *
    Q'.ofNat (q.intermediate + 2)
  let C := omegaCorrectionDiagonalCoefficient a b c d q.p
  let N := Q'.ofInt
    (omegaCorrectionDiagonalNumerator a b c d q.intermediate)
  have hcoeff := omegaCorrectionDiagonalCoefficient_closed q hp
  have hmul := ofNat_mul_eqv q.intermediate (q.intermediate + 2)
  have hden0 := ofNat_mul_eqv 8 (q.intermediate * (q.intermediate + 2))
  have hden : D ≈
      Q'.ofNat (omegaCorrectionDiagonalDenominator q.intermediate) := by
    refine Q'.eqv_trans _
      (Q'.ofNat 8 *
        (Q'.ofNat q.intermediate * Q'.ofNat (q.intermediate + 2))) _
      (by simp only [D]; ring_qeqv) ?_
    refine Q'.eqv_trans _
      (Q'.ofNat 8 * Q'.ofNat
        (q.intermediate * (q.intermediate + 2))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _ hmul
    · refine Q'.eqv_trans _
        (Q'.ofNat (8 * (q.intermediate * (q.intermediate + 2)))) _
        hden0 ?_
      unfold omegaCorrectionDiagonalDenominator diagonalDen casimir4
      simp only [hn]
      exact Q'.eqv_refl _
  have hcore : D * C ≈ N :=
    Q'.eqv_trans _
      (Q'.ofNat (omegaCorrectionDiagonalDenominator q.intermediate) * C) _
      (Q'.mul_eqv_congr_right _ _ C hden) (by simpa only [N] using hcoeff)
  unfold heightOneJacobiScale heightOneScaledDiagonalCoefficient
  refine Q'.eqv_trans _ (A * (D * C)) _ (by simp only [A, D, C]; ring_qeqv) ?_
  exact Q'.mul_eqv_congr_left A _ _ hcore

/-- Carrier-side polynomial after all Jacobi denominators are cleared. -/
def heightOneScaledCarrierSideScalar {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l : Nat) : Q' :=
  heightOneScaledLowerCoefficient q * heightOneCarrierLowerScalar q i j l +
    heightOneScaledDiagonalCoefficient q *
      heightOneCarrierDiagonalScalar q i j l +
    heightOneScaledUpperCoefficient q * heightOneCarrierUpperScalar q

/-- The whole carrier-side scalar after common scaling. -/
theorem height_one_scaled_carrier_side {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (hprev : q.p = qm.p + 1) (hnext : qp.p = q.p + 1)
    (i j l : Nat) (hn : q.intermediate ≠ 0) :
    heightOneJacobiScale q * heightOneCarrierSideScalar q i j l ≈
      heightOneScaledCarrierSideScalar q i j l := by
  let S := heightOneJacobiScale q
  let LC := omegaCorrectionLowerCoefficient a b c d q.p
  let DC := omegaCorrectionDiagonalCoefficient a b c d q.p
  let UC := omegaCorrectionUpperCoefficient a b c d q.p
  let L := heightOneCarrierLowerScalar q i j l
  let D := heightOneCarrierDiagonalScalar q i j l
  let U := heightOneCarrierUpperScalar q
  have hl := height_one_scaled_lower_coefficient qm q hp hprev
  have hd := height_one_scaled_diagonal_coefficient q hp hn
  have hu := height_one_scaled_upper_coefficient q qp hp hnext
  unfold heightOneCarrierSideScalar heightOneScaledCarrierSideScalar
  refine Q'.eqv_trans _
    ((S * LC) * L + (S * DC) * D + (S * UC) * U) _ ?_ ?_
  · simp only [S, LC, DC, UC, L, D, U]
    ring_qeqv
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ L hl)
        (Q'.mul_eqv_congr_right _ _ D hd))
      (Q'.mul_eqv_congr_right _ _ U hu)

/-- Pure numerator polynomial left after clearing all rational coefficients. -/
def heightOneScaledResidualPolynomial {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l : Nat) : Q' :=
  (heightOneJacobiScale q * heightOneBulkExchangeScale q) *
      reducedHeightOneExchangeScalar q i j l +
    -(heightOneBulkCarrierScale q i j l *
      heightOneScaledCarrierSideScalar q i j l)

/-- Exact reduction of the residual scalar to the pure numerator
polynomial. -/
theorem height_one_residual_scaled_to_polynomial {a b c d : Nat}
    (qm q qp : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (hprev : q.p = qm.p + 1) (hnext : qp.p = q.p + 1)
    (i j l : Nat) (hn : q.intermediate ≠ 0) :
    heightOneJacobiScale q * heightOneBulkResidualScalar q i j l ≈
      heightOneScaledResidualPolynomial q i j l := by
  let S := heightOneJacobiScale q
  let E := heightOneBulkExchangeScale q
  let X := reducedHeightOneExchangeScalar q i j l
  let C := heightOneBulkCarrierScale q i j l
  let Y := heightOneCarrierSideScalar q i j l
  let Z := heightOneScaledCarrierSideScalar q i j l
  have hy := height_one_scaled_carrier_side qm q qp hp hprev hnext i j l hn
  unfold heightOneBulkResidualScalar heightOneScaledResidualPolynomial
  refine Q'.eqv_trans _ ((S * E) * X + -(C * (S * Y))) _
    (by simp only [S, E, X, C, Y]; ring_qeqv) ?_
  refine Q'.eqv_trans _ ((S * E) * X + -(C * Z)) _
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left C _ _ hy))) ?_
  simp only [S, E, X, C, Z]
  exact Q'.eqv_refl _

end YMGap.Continuum.SU2OrderedRacahHeightOneScaledResidualPolynomial

#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneScaledResidualPolynomial.height_one_scaled_lower_coefficient
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneScaledResidualPolynomial.height_one_scaled_diagonal_coefficient
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneScaledResidualPolynomial.height_one_scaled_upper_coefficient
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneScaledResidualPolynomial.height_one_scaled_carrier_side
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneScaledResidualPolynomial.height_one_residual_scaled_to_polynomial
