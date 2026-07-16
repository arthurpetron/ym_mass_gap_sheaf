/-
# Exact separable Bernstein certificate for the high-branch Base polynomial

The transparent polynomial `tailBaseCleared` is exactly
`178605 * BASE_FULL_NUM` from the authoritative lower-six second-flux
generator.  Its 42 by 23 positive Bernstein table is checked without a
four-variable expansion: two cached one-dimensional Pascal transforms
identify the table with the scaled chart power coefficients.  A second
upper-binomial coefficient check reconstructs the raw variables.

At `8191 ≤ D ≤ n ≤ 2D`, the normalized chart coordinates are

  `x = 8191/D`,  `y = (n-D)/D`.

Both lie in `[0,1]`.  Table positivity therefore makes the chart polynomial
nonnegative.  Exact projective clearing by `D^50` gives a positive constant
times `tailBaseCleared`, and that constant is cancelled constructively.
-/

import YMGap.Continuum.HarmonicLowerSixTailBaseCoefficientCertificate

namespace YMGap.Continuum.HarmonicLowerSixTailBaseCertificate

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.HarmonicLowerSixTailBaseCertificateRows
open YMGap.Continuum.HarmonicLowerSixTailBaseCoefficientCertificate
open YMGap.Continuum.TensorBernsteinSeparableReconstruction

local infix:50 " ≈ " => Q'.eqv

/-! ## Transparent cleared polynomial -/

/-- The dense exact coefficient evaluation of `178605 * BASE_FULL_NUM`.
The diagonal coordinate `a = 50-i-j` is the inverse-scale exponent of the
high-branch projective chart. -/
def tailBaseCleared (D n : Q') : Q' :=
  diagonalPowerEval 41 22 50 tailBaseClearedDiagCoeff D n

theorem tailBaseTableScale_eq :
    tailBaseTableScale = 178605 * tailBaseChartQuotient := by
  decide

private theorem mkPos_mul_ofNat_eqv (numerator : Int) (denominator : Nat)
    (hdenominator : 0 < denominator) :
    Q'.mkPos numerator denominator hdenominator * Q'.ofNat denominator ≈
      Q'.ofInt numerator := by
  show
    (Q'.mkPos numerator denominator hdenominator *
      Q'.ofNat denominator).num * ((Q'.ofInt numerator).den : Int) =
    (Q'.ofInt numerator).num *
      (((Q'.mkPos numerator denominator hdenominator *
        Q'.ofNat denominator).den : Nat) : Int)
  rw [Q'.mul_num_cast, Q'.mul_den_cast, Q'.mkPos_num,
    Q'.mkPos_den]
  change (numerator * Int.ofNat denominator) * 1 =
    numerator * (Int.ofNat denominator * 1)
  exact Int.mul_assoc _ _ _

private theorem chart_y_mul_den_eqv
    (D n : Nat) (hDpos : 0 < D) :
    (Q'.mkPos (Int.ofNat n - Int.ofNat D) D hDpos + 1) * Q'.ofNat D ≈
      Q'.ofNat n := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_mul_eqv
      (Q'.mkPos (Int.ofNat n - Int.ofNat D) D hDpos) 1 (Q'.ofNat D)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _
      (mkPos_mul_ofNat_eqv (Int.ofNat n - Int.ofNat D) D hDpos)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (Q'.ofInt (Int.ofNat n - Int.ofNat D)) _ _
      (Q'.one_mul_eqv (Q'.ofNat D))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (YMGap.Continuum.RingNormaliser.ofInt_add
        (Int.ofNat n - Int.ofNat D) (Int.ofNat D))) ?_
  have hinteger : Int.ofNat n - Int.ofNat D + Int.ofNat D = Int.ofNat n := by
    omega
  rw [hinteger]
  exact Q'.eqv_refl _

private theorem ofNat_nonnegative (value : Nat) :
    (0 : Q') ≤ Q'.ofNat value := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact Int.natCast_nonneg value

private theorem normalized_chart_bounds
    (D n : Nat) (hDpos : 0 < D)
    (hD : 8191 ≤ D) (hDn : D ≤ n) (hn2 : n ≤ 2 * D) :
    let x := Q'.mkPos 8191 D hDpos
    let y := Q'.mkPos (Int.ofNat n - Int.ofNat D) D hDpos
    (0 : Q') ≤ x ∧ (0 : Q') ≤ 1 - x ∧
      (0 : Q') ≤ y ∧ (0 : Q') ≤ 1 - y := by
  dsimp only
  have hx : (0 : Q') ≤ Q'.mkPos 8191 D hDpos := by
    rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]
    decide
  have hxle : Q'.mkPos 8191 D hDpos ≤ (1 : Q') := by
    show (Q'.mkPos 8191 D hDpos).num * ((1 : Q').den : Int) ≤
      (1 : Q').num * ((Q'.mkPos 8191 D hDpos).den : Int)
    rw [Q'.mkPos_num, Q'.mkPos_den]
    have honeNum : (1 : Q').num = 1 := rfl
    have honeDen : (1 : Q').den = 1 := rfl
    rw [honeNum, honeDen]
    simpa only [Int.natCast_one, Int.mul_one, Int.one_mul] using
      (Int.ofNat_le.mpr hD)
  have hy :
      (0 : Q') ≤ Q'.mkPos (Int.ofNat n - Int.ofNat D) D hDpos := by
    rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]
    exact Int.sub_nonneg.mpr (Int.ofNat_le.mpr hDn)
  have hyle :
      Q'.mkPos (Int.ofNat n - Int.ofNat D) D hDpos ≤ (1 : Q') := by
    show (Q'.mkPos (Int.ofNat n - Int.ofNat D) D hDpos).num *
        ((1 : Q').den : Int) ≤
      (1 : Q').num *
        ((Q'.mkPos (Int.ofNat n - Int.ofNat D) D hDpos).den : Int)
    rw [Q'.mkPos_num, Q'.mkPos_den]
    have honeNum : (1 : Q').num = 1 := rfl
    have honeDen : (1 : Q').den = 1 := rfl
    rw [honeNum, honeDen]
    have hcast : Int.ofNat n ≤ Int.ofNat (2 * D) := Int.ofNat_le.mpr hn2
    have htwo : Int.ofNat (2 * D) = 2 * Int.ofNat D := by
      rw [Int.ofNat_eq_natCast, Int.natCast_mul]
      have htwoCast : ((2 : Nat) : Int) = 2 := by decide
      rw [htwoCast, Int.ofNat_eq_natCast]
    rw [htwo] at hcast
    have hsub : Int.ofNat n - Int.ofNat D ≤ Int.ofNat D := by omega
    simpa only [Int.natCast_one, Int.mul_one, Int.one_mul] using hsub
  exact ⟨hx, Q'.sub_nonneg_of_le hxle,
    hy, Q'.sub_nonneg_of_le hyle⟩

private theorem raw_diag_support
    {a j : Nat} (_ha : a < 42) (_hj : j < 23)
    (hnonzero : tailBaseScaledRawDiagCoeff a j ≠ 0) :
    a + j ≤ 50 := by
  unfold tailBaseScaledRawDiagCoeff tailBaseClearedDiagCoeff at hnonzero
  split at hnonzero
  · assumption
  · simp at hnonzero

/-! ## High-branch sign theorem -/

/-- **Exact high-branch Base sign certificate.** -/
theorem tailBaseCleared_nonnegative
    (D n : Nat) (hD : 8191 ≤ D) (hDn : D ≤ n) (hn2 : n ≤ 2 * D) :
    (0 : Q') ≤ tailBaseCleared (Q'.ofNat D) (Q'.ofNat n) := by
  have hDpos : 0 < D := Nat.lt_of_lt_of_le (by decide) hD
  let x := Q'.mkPos 8191 D hDpos
  let y := Q'.mkPos (Int.ofNat n - Int.ofNat D) D hDpos
  let den := Q'.ofNat D
  let target := Q'.ofNat n
  have hbounds := normalized_chart_bounds D n hDpos hD hDn hn2
  have htable :
      (0 : Q') ≤ tensorBernsteinEval 41 22 tailBaseWeightedCoeff x y :=
    tensorBernsteinEval_nonnegative 41 22 tailBaseWeightedCoeff x y
      hbounds.1 hbounds.2.1 hbounds.2.2.1 hbounds.2.2.2
      (fun i hi j hj => tailBase_weighted_nonnegative_at hi hj)
  have hreconstruction :
      tensorBernsteinEval 41 22 tailBaseWeightedCoeff x y ≈
        tensorPowerEval 41 22 tailBaseScaledPowerCoeff x y :=
    tensorBernsteinEval_eqv_powerEval 41 22
      tailBaseScaledPowerCoeff tailBaseWeightedCoeff x y
      (fun i hi j hj => tailBase_weighted_eq_tensorPascal hi hj)
  have hpower :
      (0 : Q') ≤ tensorPowerEval 41 22 tailBaseScaledPowerCoeff x y :=
    Q'.le_trans' _ _ _ htable (Q'.le_of_eqv hreconstruction)
  have hdenNonnegative : (0 : Q') ≤ den := ofNat_nonnegative D
  have hclearedPower :
      (0 : Q') ≤ tensorPowerEval 41 22 tailBaseScaledPowerCoeff x y *
        den ^ 50 :=
    Q'.mul_nonneg _ _ hpower (Q'.pow_nonneg den hdenNonnegative 50)
  have hxden : x * den ≈ Q'.ofNat 8191 := by
    exact mkPos_mul_ofNat_eqv 8191 D hDpos
  have hyden : (y + 1) * den ≈ target := by
    exact chart_y_mul_den_eqv D n hDpos
  have hprojective :
      tensorPowerEval 41 22 tailBaseScaledPowerCoeff x y * den ^ 50 ≈
        diagonalPowerEval 41 22 50 tailBaseScaledRawDiagCoeff den target :=
    tensorPowerEval_mul_den_pow_eqv_diagonal
      41 22 50 8191 tailBaseScaledPowerCoeff tailBaseScaledRawDiagCoeff
      x y den target (by decide) hxden hyden
      (fun a ha b hb => tailBase_rawChart_relation_at ha hb)
      (fun a ha j hj hnonzero => raw_diag_support ha hj hnonzero)
  have hdiagonal :
      (0 : Q') ≤
        diagonalPowerEval 41 22 50 tailBaseScaledRawDiagCoeff den target :=
    Q'.le_trans' _ _ _ hclearedPower (Q'.le_of_eqv hprojective)
  have hscale :
      diagonalPowerEval 41 22 50 tailBaseScaledRawDiagCoeff den target ≈
        Q'.ofInt tailBaseChartQuotient * tailBaseCleared den target := by
    exact diagonalPowerEval_scale 41 22 50 tailBaseChartQuotient
      tailBaseClearedDiagCoeff den target
  have hscaled :
      (0 : Q') ≤ Q'.ofInt tailBaseChartQuotient * tailBaseCleared den target :=
    Q'.le_trans' _ _ _ hdiagonal (Q'.le_of_eqv hscale)
  have hchartPositive : (0 : Q') < Q'.ofInt tailBaseChartQuotient := by
    decide
  have hcancel :
      Q'.ofInt tailBaseChartQuotient * (0 : Q') ≤
        Q'.ofInt tailBaseChartQuotient * tailBaseCleared den target :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (Q'.mul_zero_eqv (Q'.ofInt tailBaseChartQuotient)))
      hscaled
  exact Q'.le_of_mul_le_mul_left hcancel hchartPositive

/-! ## Dependency gates -/

#print axioms tailBaseCleared
#print axioms tailBaseTableScale_eq
#print axioms tailBaseCleared_nonnegative

end YMGap.Continuum.HarmonicLowerSixTailBaseCertificate
