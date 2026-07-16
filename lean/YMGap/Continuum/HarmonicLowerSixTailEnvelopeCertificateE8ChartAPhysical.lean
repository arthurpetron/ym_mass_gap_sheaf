/-
# Physical chart-A consumer for the lower-six E8 envelope certificate

On `64 ≤ n` and `n² ≤ D ≤ 2*n²`, the exact coordinates

  x = 64/n,        r = (D-n²)/n²

belong to the unit square.  The closed E8 chart-A Bernstein table is
therefore nonnegative, and the quadratic projective kernel carries that
sign to the generated raw `(D,n)` polynomial.
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartACoefficientCertificate
import YMGap.Continuum.TensorBernsteinQuadraticProjectiveReconstruction
import YMGap.Constructive.RegularCReal

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartAPhysical

open YMGap.Constructive
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateRows
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartA
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCoefficientKernel
open YMGap.Continuum.TensorBernsteinQuadraticProjectiveReconstruction
open YMGap.Continuum.TensorBernsteinSeparableReconstruction

local infix:50 " ≈ " => Q'.eqv

theorem mkPos_mul_ofNat_eqv (numerator : Int) (denominator : Nat)
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

theorem offset_chart_add_one_mul_den_eqv
    (target denominator : Nat) (hdenominator : 0 < denominator) :
    (Q'.mkPos (Int.ofNat target - Int.ofNat denominator)
        denominator hdenominator + 1) * Q'.ofNat denominator ≈
      Q'.ofNat target := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_mul_eqv
      (Q'.mkPos (Int.ofNat target - Int.ofNat denominator)
        denominator hdenominator) 1 (Q'.ofNat denominator)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _
      (mkPos_mul_ofNat_eqv
        (Int.ofNat target - Int.ofNat denominator)
        denominator hdenominator)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left
      (Q'.ofInt (Int.ofNat target - Int.ofNat denominator)) _ _
      (Q'.one_mul_eqv (Q'.ofNat denominator))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (YMGap.Continuum.RingNormaliser.ofInt_add
        (Int.ofNat target - Int.ofNat denominator)
        (Int.ofNat denominator))) ?_
  have hinteger : Int.ofNat target - Int.ofNat denominator +
      Int.ofNat denominator = Int.ofNat target := by
    omega
  rw [hinteger]
  exact Q'.eqv_refl _

theorem ofNat_mul_eqv (a b : Nat) :
    Q'.ofNat a * Q'.ofNat b ≈ Q'.ofNat (a * b) := by
  have hmul := YMGap.Continuum.RingNormaliser.ofInt_mul
    (Int.ofNat a) (Int.ofNat b)
  have hinteger : Int.ofNat a * Int.ofNat b = Int.ofNat (a * b) := by
    simp only [Int.ofNat_eq_natCast, Int.natCast_mul]
  rw [hinteger] at hmul
  exact hmul

theorem ofNat_nonnegative (value : Nat) :
    (0 : Q') ≤ Q'.ofNat value := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact Int.natCast_nonneg value

theorem normalized_chartA_bounds
    (D n : Nat) (hnpos : 0 < n) (hn : 64 ≤ n)
    (hDlow : n * n ≤ D) (hDhigh : D ≤ 2 * (n * n)) :
    let x := Q'.mkPos 64 n hnpos
    let n2 := n * n
    let hn2pos : 0 < n2 := Nat.mul_pos hnpos hnpos
    let r := Q'.mkPos (Int.ofNat D - Int.ofNat n2) n2 hn2pos
    (0 : Q') ≤ x ∧ (0 : Q') ≤ 1 - x ∧
      (0 : Q') ≤ r ∧ (0 : Q') ≤ 1 - r := by
  dsimp only
  have hx : (0 : Q') ≤ Q'.mkPos 64 n hnpos := by
    rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]
    decide
  have hxle : Q'.mkPos 64 n hnpos ≤ (1 : Q') := by
    show (Q'.mkPos 64 n hnpos).num * ((1 : Q').den : Int) ≤
      (1 : Q').num * ((Q'.mkPos 64 n hnpos).den : Int)
    rw [Q'.mkPos_num, Q'.mkPos_den]
    have honeNum : (1 : Q').num = 1 := rfl
    have honeDen : (1 : Q').den = 1 := rfl
    rw [honeNum, honeDen]
    simpa only [Int.natCast_one, Int.mul_one, Int.one_mul] using
      (Int.ofNat_le.mpr hn)
  have hn2pos : 0 < n * n := Nat.mul_pos hnpos hnpos
  have hr : (0 : Q') ≤
      Q'.mkPos (Int.ofNat D - Int.ofNat (n * n)) (n * n) hn2pos := by
    rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]
    exact Int.sub_nonneg.mpr (Int.ofNat_le.mpr hDlow)
  have hrle :
      Q'.mkPos (Int.ofNat D - Int.ofNat (n * n)) (n * n) hn2pos ≤
        (1 : Q') := by
    show
      (Q'.mkPos (Int.ofNat D - Int.ofNat (n * n))
        (n * n) hn2pos).num * ((1 : Q').den : Int) ≤
      (1 : Q').num *
        ((Q'.mkPos (Int.ofNat D - Int.ofNat (n * n))
          (n * n) hn2pos).den : Int)
    rw [Q'.mkPos_num, Q'.mkPos_den]
    have honeNum : (1 : Q').num = 1 := rfl
    have honeDen : (1 : Q').den = 1 := rfl
    rw [honeNum, honeDen]
    have hcast : Int.ofNat D ≤ Int.ofNat (2 * (n * n)) :=
      Int.ofNat_le.mpr hDhigh
    have htwo : Int.ofNat (2 * (n * n)) =
        2 * Int.ofNat (n * n) := by
      rw [Int.ofNat_eq_natCast, Int.natCast_mul]
      have htwoCast : ((2 : Nat) : Int) = 2 := by decide
      rw [htwoCast, Int.ofNat_eq_natCast]
    rw [htwo] at hcast
    have hsub : Int.ofNat D - Int.ofNat (n * n) ≤
        Int.ofNat (n * n) := by
      omega
    simpa only [Int.natCast_one, Int.mul_one, Int.one_mul] using hsub
  exact ⟨hx, Q'.sub_nonneg_of_le hxle,
    hr, Q'.sub_nonneg_of_le hrle⟩

/-- Raw coefficients scaled by the exact chart quotient checked in the
coefficient certificate. -/
def tailEnvelopeE8ChartAScaledRaw (i j : Nat) : Int :=
  Int.ofNat tailEnvelopeE8ChartAChartQuotient *
    gridCoeff tailEnvelopeE8ClearedRows i j

/-- The exact projectively homogeneous E8 numerator on chart A. -/
def tailEnvelopeE8ChartARawEval (D n : Q') : Q' :=
  quadraticPowerEval 83 44 89 tailEnvelopeE8ChartAScaledRaw D n

/-- **Physical E8 chart-A sign certificate.** -/
theorem tailEnvelopeE8ChartARawEval_nonnegative
    (D n : Nat) (hn : 64 ≤ n)
    (hDlow : n * n ≤ D) (hDhigh : D ≤ 2 * (n * n)) :
    (0 : Q') ≤
      tailEnvelopeE8ChartARawEval (Q'.ofNat D) (Q'.ofNat n) := by
  have hnpos : 0 < n := Nat.lt_of_lt_of_le (by decide) hn
  have hn2pos : 0 < n * n := Nat.mul_pos hnpos hnpos
  let x := Q'.mkPos 64 n hnpos
  let r := Q'.mkPos (Int.ofNat D - Int.ofNat (n * n))
    (n * n) hn2pos
  let den := Q'.ofNat n
  let targetD := Q'.ofNat D
  have hbounds := normalized_chartA_bounds D n hnpos hn hDlow hDhigh
  have htable :
      (0 : Q') ≤ tensorBernsteinEval 83 44
        (weightedGrid 83 44 tailEnvelopeE8ChartABernsteinRows) x r :=
    tensorBernsteinEval_nonnegative 83 44
      (weightedGrid 83 44 tailEnvelopeE8ChartABernsteinRows) x r
      hbounds.1 hbounds.2.1 hbounds.2.2.1 hbounds.2.2.2
      (fun i hi j hj => by
        unfold weightedGrid
        exact Int.mul_nonneg
          (tailEnvelopeE8ChartA_nonnegative_at hi hj)
          (Int.natCast_nonneg _))
  have hreconstruction :
      tensorBernsteinEval 83 44
          (weightedGrid 83 44 tailEnvelopeE8ChartABernsteinRows) x r ≈
        tensorPowerEval 83 44
          (gridCoeff tailEnvelopeE8ChartAScaledPowerRows) x r :=
    tensorBernsteinEval_eqv_powerEval 83 44
      (gridCoeff tailEnvelopeE8ChartAScaledPowerRows)
      (weightedGrid 83 44 tailEnvelopeE8ChartABernsteinRows) x r
      (fun i hi j hj => tailEnvelopeE8ChartA_transform_at hi hj)
  have hpower :
      (0 : Q') ≤ tensorPowerEval 83 44
        (gridCoeff tailEnvelopeE8ChartAScaledPowerRows) x r :=
    Q'.le_trans' _ _ _ htable (Q'.le_of_eqv hreconstruction)
  have hdenNonnegative : (0 : Q') ≤ den := ofNat_nonnegative n
  have hcleared :
      (0 : Q') ≤ tensorPowerEval 83 44
          (gridCoeff tailEnvelopeE8ChartAScaledPowerRows) x r * den ^ 89 :=
    Q'.mul_nonneg _ _ hpower (Q'.pow_nonneg den hdenNonnegative 89)
  have hxden : x * den ≈ Q'.ofNat 64 := by
    exact mkPos_mul_ofNat_eqv 64 n hnpos
  have hnSquare : den * den ≈ Q'.ofNat (n * n) := by
    exact ofNat_mul_eqv n n
  have hrSquare : (r + 1) * Q'.ofNat (n * n) ≈ targetD := by
    exact offset_chart_add_one_mul_den_eqv D (n * n) hn2pos
  have hrden : ((r + 1) * den) * den ≈ targetD := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv (r + 1) den den) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (r + 1) _ _ hnSquare) ?_
    exact hrSquare
  have hprojective :
      tensorPowerEval 83 44
          (gridCoeff tailEnvelopeE8ChartAScaledPowerRows) x r * den ^ 89 ≈
        tailEnvelopeE8ChartARawEval targetD den := by
    unfold tailEnvelopeE8ChartARawEval
    apply tensorPowerEval_mul_den_pow_eqv_quadratic
      83 44 89 64
      (gridCoeff tailEnvelopeE8ChartAScaledPowerRows)
      (gridCoeff tailEnvelopeE8ChartAPreChartRows)
      tailEnvelopeE8ChartAScaledRaw x r den targetD
    · decide
    · exact hxden
    · exact hrden
    · intro u hu b hb
      exact tailEnvelopeE8ChartA_shift_at hu hb
    · intro u hu i hi
      have hraw := tailEnvelopeE8ChartA_raw_at hu hi
      unfold quadraticRawExpected at hraw
      unfold quadraticRawLift tailEnvelopeE8ChartAScaledRaw
      exact hraw
  exact Q'.le_trans' _ _ _ hcleared (Q'.le_of_eqv hprojective)

/-! ## Dependency gates -/

#print axioms mkPos_mul_ofNat_eqv
#print axioms offset_chart_add_one_mul_den_eqv
#print axioms ofNat_mul_eqv
#print axioms ofNat_nonnegative
#print axioms normalized_chartA_bounds
#print axioms tailEnvelopeE8ChartAScaledRaw
#print axioms tailEnvelopeE8ChartARawEval
#print axioms tailEnvelopeE8ChartARawEval_nonnegative

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartAPhysical
