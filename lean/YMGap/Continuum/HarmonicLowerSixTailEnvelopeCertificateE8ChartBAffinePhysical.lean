/-
# Physical affine-table consumer for the lower-six E8 chart B

The chart-B certificate first changes

  r = z + (x/182) * (1-z).

This module proves the physical unit-square bounds and transports table
positivity through the generated, coefficient-checked affine grid.  The
separate semantic theorem identifying that affine grid with the original
`r`-power table remains an explicit next layer.
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartBCoefficientCertificate
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartBAffineReconstruction
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartAPhysical
import YMGap.Constructive.Soundness

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartBAffinePhysical

open YMGap.Constructive
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateRows
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartB
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartBAffineReconstruction
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCoefficientKernel
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartAPhysical
open YMGap.Continuum.TensorBernsteinQuadraticProjectiveReconstruction
open YMGap.Continuum.TensorBernsteinQuadraticAffineChartReconstruction
open YMGap.Continuum.TensorBernsteinSeparableReconstruction

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

theorem ofNat_pos_of_pos (value : Nat) (hvalue : 0 < value) :
    (0 : Q') < Q'.ofNat value := by
  show (0 : Int) * ((Q'.ofNat value).den : Int) <
    (Q'.ofNat value).num * (1 : Int)
  rw [Int.zero_mul, Q'.ofNat_num_cast, Int.mul_one]
  exact Int.ofNat_lt.mpr hvalue

/-- Positive denominator of the physical chart-B coordinate
`z = (2D-n)/(2n²-n)`. -/
def chartBDenominator (n : Nat) : Nat := 2 * (n * n) - n

theorem chartBDenominator_pos {n : Nat} (hnpos : 0 < n) :
    0 < chartBDenominator n := by
  have hone : 1 ≤ n := hnpos
  have hnn : n ≤ n * n := by
    have hmul := Nat.mul_le_mul_left n hone
    simpa only [Nat.mul_one] using hmul
  unfold chartBDenominator
  omega

/-- Exact chart-B coordinates lie in the unit square on the physical
corridor `91 ≤ n`, `n ≤ 2D`, `D ≤ n²`. -/
theorem normalized_chartB_bounds
    (D n : Nat) (hnpos : 0 < n) (hn : 91 ≤ n)
    (_hn2D : n ≤ 2 * D) (hDhigh : D ≤ n * n) :
    let zDen := chartBDenominator n
    let hzDenPos : 0 < zDen := chartBDenominator_pos hnpos
    let x := Q'.mkPos 91 n hnpos
    let z := Q'.mkPos (Int.ofNat (2 * D - n)) zDen hzDenPos
    (0 : Q') ≤ x ∧ (0 : Q') ≤ 1 - x ∧
      (0 : Q') ≤ z ∧ (0 : Q') ≤ 1 - z := by
  dsimp only
  have hx : (0 : Q') ≤ Q'.mkPos 91 n hnpos := by
    rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]
    decide
  have hxle : Q'.mkPos 91 n hnpos ≤ (1 : Q') := by
    show (Q'.mkPos 91 n hnpos).num * ((1 : Q').den : Int) ≤
      (1 : Q').num * ((Q'.mkPos 91 n hnpos).den : Int)
    rw [Q'.mkPos_num, Q'.mkPos_den]
    have honeNum : (1 : Q').num = 1 := rfl
    have honeDen : (1 : Q').den = 1 := rfl
    rw [honeNum, honeDen]
    simpa only [Int.natCast_one, Int.mul_one, Int.one_mul] using
      (Int.ofNat_le.mpr hn)
  have hzDenPos : 0 < chartBDenominator n := chartBDenominator_pos hnpos
  have hz : (0 : Q') ≤
      Q'.mkPos (Int.ofNat (2 * D - n))
        (chartBDenominator n) hzDenPos := by
    rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]
    exact Int.natCast_nonneg _
  have hdouble : 2 * D ≤ 2 * (n * n) := Nat.mul_le_mul_left 2 hDhigh
  have hnumle : 2 * D - n ≤ chartBDenominator n := by
    unfold chartBDenominator
    exact Nat.sub_le_sub_right hdouble n
  have hzle :
      Q'.mkPos (Int.ofNat (2 * D - n))
          (chartBDenominator n) hzDenPos ≤ (1 : Q') := by
    show
      (Q'.mkPos (Int.ofNat (2 * D - n))
        (chartBDenominator n) hzDenPos).num * ((1 : Q').den : Int) ≤
      (1 : Q').num *
        ((Q'.mkPos (Int.ofNat (2 * D - n))
          (chartBDenominator n) hzDenPos).den : Int)
    rw [Q'.mkPos_num, Q'.mkPos_den]
    have honeNum : (1 : Q').num = 1 := rfl
    have honeDen : (1 : Q').den = 1 := rfl
    rw [honeNum, honeDen]
    simpa only [Int.natCast_one, Int.mul_one, Int.one_mul] using
      (Int.ofNat_le.mpr hnumle)
  exact ⟨hx, Q'.sub_nonneg_of_le hxle,
    hz, Q'.sub_nonneg_of_le hzle⟩

/-- The physical coordinates satisfy the exact affine chart relation
`182*r = 182*z + x*(1-z)`, with `r = D/n²`. -/
theorem normalized_chartB_affine_relation
    (D n : Nat) (hnpos : 0 < n) (hn2D : n ≤ 2 * D) :
    Q'.ofNat 182 *
        Q'.mkPos (Int.ofNat D) (n * n) (Nat.mul_pos hnpos hnpos) ≈
      Q'.ofNat 182 *
          Q'.mkPos (Int.ofNat (2 * D - n)) (chartBDenominator n)
            (chartBDenominator_pos hnpos) +
        Q'.mkPos 91 n hnpos *
          ((1 : Q') +
            -Q'.mkPos (Int.ofNat (2 * D - n)) (chartBDenominator n)
              (chartBDenominator_pos hnpos)) := by
  unfold chartBDenominator
  show _ * (_ : Int) = _ * (_ : Int)
  have hnle : n ≤ 2 * (n * n) := by
    have hnn : n ≤ n * n := by
      have hone : 1 ≤ n := hnpos
      have hmul := Nat.mul_le_mul_left n hone
      simpa only [Nat.mul_one] using hmul
    omega
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
    Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den,
    Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
    Int.one_mul]
  have hnumCast : Int.ofNat (2 * D - n) =
      Int.ofNat (2 * D) - Int.ofNat n := Int.ofNat_sub hn2D
  have hdenCast : ((2 * (n * n) - n : Nat) : Int) =
      ((2 * (n * n) : Nat) : Int) - (n : Int) :=
    Int.natCast_sub hnle
  rw [hnumCast, hdenCast]
  have h182 : ((182 : Nat) : Int) = 2 * 91 := by decide
  have htwo : ((2 : Nat) : Int) = 2 := by decide
  have honeNum : (1 : Q').num = 1 := rfl
  have honeDen : ((1 : Q').den : Int) = 1 := rfl
  rw [h182, honeNum, honeDen]
  simp only [Int.ofNat_eq_natCast, Int.natCast_mul, Int.sub_eq_add_neg,
    Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
    Int.one_mul, Int.mul_one]
  rw [htwo]
  simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm,
    Int.reduceMul]
  omega

/-- The coefficient-cleared affine E8 chart-B power polynomial. -/
def tailEnvelopeE8ChartBAffineEval (x z : Q') : Q' :=
  tensorPowerEval 85 44
    (affineChartBClearedCoeff 44 tailEnvelopeE8ChartBPreChartRows) x z

/-- The physical affine grid is nonnegative.  This theorem consumes both the
Bernstein sign table and the generated affine coefficient identities. -/
theorem tailEnvelopeE8ChartBAffineEval_nonnegative
    (D n : Nat) (hn : 91 ≤ n)
    (hn2D : n ≤ 2 * D) (hDhigh : D ≤ n * n) :
    (0 : Q') ≤
      tailEnvelopeE8ChartBAffineEval
        (Q'.mkPos 91 n (Nat.lt_of_lt_of_le (by decide) hn))
        (Q'.mkPos (Int.ofNat (2 * D - n)) (chartBDenominator n)
          (chartBDenominator_pos
            (Nat.lt_of_lt_of_le (by decide) hn))) := by
  have hnpos : 0 < n := Nat.lt_of_lt_of_le (by decide) hn
  let x := Q'.mkPos 91 n hnpos
  let z := Q'.mkPos (Int.ofNat (2 * D - n)) (chartBDenominator n)
    (chartBDenominator_pos hnpos)
  have hbounds := normalized_chartB_bounds D n hnpos hn hn2D hDhigh
  have htable :
      (0 : Q') ≤ tensorBernsteinEval 85 44
        (weightedGrid 85 44 tailEnvelopeE8ChartBBernsteinRows) x z :=
    tensorBernsteinEval_nonnegative 85 44
      (weightedGrid 85 44 tailEnvelopeE8ChartBBernsteinRows) x z
      hbounds.1 hbounds.2.1 hbounds.2.2.1 hbounds.2.2.2
      (fun i hi j hj => by
        unfold weightedGrid
        exact Int.mul_nonneg
          (tailEnvelopeE8ChartB_nonnegative_at hi hj)
          (Int.natCast_nonneg _))
  have hreconstruction :
      tensorBernsteinEval 85 44
          (weightedGrid 85 44 tailEnvelopeE8ChartBBernsteinRows) x z ≈
        tensorPowerEval 85 44
          (gridCoeff tailEnvelopeE8ChartBScaledPowerRows) x z :=
    tensorBernsteinEval_eqv_powerEval 85 44
      (gridCoeff tailEnvelopeE8ChartBScaledPowerRows)
      (weightedGrid 85 44 tailEnvelopeE8ChartBBernsteinRows) x z
      (fun i hi j hj => tailEnvelopeE8ChartB_transform_at hi hj)
  have hpower :
      (0 : Q') ≤ tensorPowerEval 85 44
        (gridCoeff tailEnvelopeE8ChartBScaledPowerRows) x z :=
    Q'.le_trans' _ _ _ htable (Q'.le_of_eqv hreconstruction)
  let scale : Int := Int.ofNat (182 ^ 44)
  have hscaleNonnegative : (0 : Q') ≤ Q'.ofInt scale := by
    dsimp only [scale]
    exact ofNat_nonnegative (182 ^ 44)
  have hscaled :
      (0 : Q') ≤ tensorPowerEval 85 44
          (gridCoeff tailEnvelopeE8ChartBScaledPowerRows) x z *
        Q'.ofInt scale :=
    Q'.mul_nonneg _ _ hpower hscaleNonnegative
  have haffineCoeff :
      tailEnvelopeE8ChartBAffineEval x z ≈
        tensorPowerEval 85 44
          (fun i j => gridCoeff tailEnvelopeE8ChartBScaledPowerRows i j *
            scale) x z := by
    unfold tailEnvelopeE8ChartBAffineEval
    apply tensorPowerEval_congr
    intro i hi j hj
    dsimp only [scale]
    exact Eq.symm (tailEnvelopeE8ChartB_affine_at hi hj)
  have hscaledEval :
      tensorPowerEval 85 44
          (fun i j => gridCoeff tailEnvelopeE8ChartBScaledPowerRows i j *
            scale) x z ≈
        tensorPowerEval 85 44
          (gridCoeff tailEnvelopeE8ChartBScaledPowerRows) x z *
            Q'.ofInt scale :=
    tensorPowerEval_scale_right 85 44
      (gridCoeff tailEnvelopeE8ChartBScaledPowerRows) scale x z
  have haffine := Q'.eqv_trans _ _ _ haffineCoeff hscaledEval
  exact Q'.le_trans' _ _ _ hscaled (Q'.ge_of_eqv haffine)

/-- The original E8 pre-chart power polynomial. -/
def tailEnvelopeE8ChartBPreChartEval (x r : Q') : Q' :=
  tensorPowerEval 85 44
    (gridCoeff tailEnvelopeE8ChartBPreChartRows) x r

/-- Raw E8 coefficients multiplied by the exact chart quotient checked in
the coefficient certificate. -/
def tailEnvelopeE8ChartBScaledRaw (i j : Nat) : Int :=
  Int.ofNat tailEnvelopeE8ChartBChartQuotient *
    gridCoeff tailEnvelopeE8ClearedRows i j

/-- The exact projectively homogeneous E8 numerator on chart B. -/
def tailEnvelopeE8ChartBRawEval (D n : Q') : Q' :=
  quadraticPowerEval 85 44 89 tailEnvelopeE8ChartBScaledRaw D n

/-- Exact physical affine scaling: the cleared affine table equals the
original pre-chart table multiplied by `182^44`. -/
theorem tailEnvelopeE8ChartB_physical_affine_scaling
    (D n : Nat) (hn : 91 ≤ n) (hn2D : n ≤ 2 * D) :
    tailEnvelopeE8ChartBAffineEval
        (Q'.mkPos 91 n (Nat.lt_of_lt_of_le (by decide) hn))
        (Q'.mkPos (Int.ofNat (2 * D - n)) (chartBDenominator n)
          (chartBDenominator_pos
            (Nat.lt_of_lt_of_le (by decide) hn))) ≈
      tailEnvelopeE8ChartBPreChartEval
          (Q'.mkPos 91 n (Nat.lt_of_lt_of_le (by decide) hn))
          (Q'.mkPos (Int.ofNat D) (n * n)
            (Nat.mul_pos
              (Nat.lt_of_lt_of_le (by decide) hn)
              (Nat.lt_of_lt_of_le (by decide) hn))) *
        Q'.ofNat (182 ^ 44) := by
  have hnpos : 0 < n := Nat.lt_of_lt_of_le (by decide) hn
  unfold tailEnvelopeE8ChartBAffineEval tailEnvelopeE8ChartBPreChartEval
  exact tailEnvelopeE8ChartB_affine_reconstruction
    (Q'.mkPos 91 n hnpos)
    (Q'.mkPos (Int.ofNat (2 * D - n)) (chartBDenominator n)
      (chartBDenominator_pos hnpos))
    (Q'.mkPos (Int.ofNat D) (n * n) (Nat.mul_pos hnpos hnpos))
    (normalized_chartB_affine_relation D n hnpos hn2D)

/-- Exact projective clearing of the E8 pre-chart power polynomial. -/
theorem tailEnvelopeE8ChartB_preChart_projective
    (D n : Nat) (hnpos : 0 < n) :
    tailEnvelopeE8ChartBPreChartEval
        (Q'.mkPos 91 n hnpos)
        (Q'.mkPos (Int.ofNat D) (n * n) (Nat.mul_pos hnpos hnpos)) *
      Q'.ofNat n ^ 89 ≈
        tailEnvelopeE8ChartBRawEval (Q'.ofNat D) (Q'.ofNat n) := by
  let x := Q'.mkPos 91 n hnpos
  let r := Q'.mkPos (Int.ofNat D) (n * n) (Nat.mul_pos hnpos hnpos)
  let den := Q'.ofNat n
  let targetD := Q'.ofNat D
  have hxden : x * den ≈ Q'.ofNat 91 := by
    exact mkPos_mul_ofNat_eqv 91 n hnpos
  have hnSquare : den * den ≈ Q'.ofNat (n * n) := by
    exact
      YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartAPhysical.ofNat_mul_eqv
        n n
  have hrSquare : r * Q'.ofNat (n * n) ≈ targetD := by
    exact mkPos_mul_ofNat_eqv (Int.ofNat D) (n * n)
      (Nat.mul_pos hnpos hnpos)
  have hrden : (r * den) * den ≈ targetD := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv r den den) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left r _ _ hnSquare) ?_
    exact hrSquare
  unfold tailEnvelopeE8ChartBPreChartEval tailEnvelopeE8ChartBRawEval
  apply tensorPowerEval_mul_den_pow_eqv_quadratic_direct
    85 44 89 91
    (gridCoeff tailEnvelopeE8ChartBPreChartRows)
    tailEnvelopeE8ChartBScaledRaw x r den targetD
  · decide
  · exact hxden
  · exact hrden
  · intro u hu i hi
    have hraw := tailEnvelopeE8ChartB_raw_at hu hi
    unfold quadraticRawExpected at hraw
    unfold quadraticRawLift tailEnvelopeE8ChartBScaledRaw
    exact hraw

/-- Exact physical scaling from the nonnegative affine polynomial to the
projective raw numerator. -/
theorem tailEnvelopeE8ChartB_affine_projective_scaling
    (D n : Nat) (hn : 91 ≤ n) (hn2D : n ≤ 2 * D) :
    tailEnvelopeE8ChartBAffineEval
        (Q'.mkPos 91 n (Nat.lt_of_lt_of_le (by decide) hn))
        (Q'.mkPos (Int.ofNat (2 * D - n)) (chartBDenominator n)
          (chartBDenominator_pos
            (Nat.lt_of_lt_of_le (by decide) hn))) *
      Q'.ofNat n ^ 89 ≈
        tailEnvelopeE8ChartBRawEval (Q'.ofNat D) (Q'.ofNat n) *
          Q'.ofNat (182 ^ 44) := by
  have hnpos : 0 < n := Nat.lt_of_lt_of_le (by decide) hn
  let x := Q'.mkPos 91 n hnpos
  let z := Q'.mkPos (Int.ofNat (2 * D - n)) (chartBDenominator n)
    (chartBDenominator_pos hnpos)
  let r := Q'.mkPos (Int.ofNat D) (n * n) (Nat.mul_pos hnpos hnpos)
  let pre := tailEnvelopeE8ChartBPreChartEval x r
  let scale := Q'.ofNat (182 ^ 44)
  let denPow := Q'.ofNat n ^ 89
  have haffine : tailEnvelopeE8ChartBAffineEval x z ≈ pre * scale := by
    exact tailEnvelopeE8ChartB_physical_affine_scaling D n hn hn2D
  have hprojective : pre * denPow ≈
      tailEnvelopeE8ChartBRawEval (Q'.ofNat D) (Q'.ofNat n) := by
    exact tailEnvelopeE8ChartB_preChart_projective D n hnpos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ denPow haffine) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv pre scale denPow) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left pre _ _ (Q'.mul_comm_eqv scale denPow)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv pre denPow scale)) ?_
  exact Q'.mul_eqv_congr_right _ _ scale hprojective

/-- The exact scaled raw E8 chart-B numerator is nonnegative throughout the
physical corridor. -/
theorem tailEnvelopeE8ChartBRawEval_scaled_nonnegative
    (D n : Nat) (hn : 91 ≤ n)
    (hn2D : n ≤ 2 * D) (hDhigh : D ≤ n * n) :
    (0 : Q') ≤
      tailEnvelopeE8ChartBRawEval (Q'.ofNat D) (Q'.ofNat n) *
        Q'.ofNat (182 ^ 44) := by
  have haffine :=
    tailEnvelopeE8ChartBAffineEval_nonnegative D n hn hn2D hDhigh
  have hdenNonnegative : (0 : Q') ≤ Q'.ofNat n :=
    ofNat_nonnegative n
  have hcleared :
      (0 : Q') ≤
        tailEnvelopeE8ChartBAffineEval
            (Q'.mkPos 91 n (Nat.lt_of_lt_of_le (by decide) hn))
            (Q'.mkPos (Int.ofNat (2 * D - n)) (chartBDenominator n)
              (chartBDenominator_pos
                (Nat.lt_of_lt_of_le (by decide) hn))) *
          Q'.ofNat n ^ 89 :=
    Q'.mul_nonneg _ _ haffine
      (Q'.pow_nonneg (Q'.ofNat n) hdenNonnegative 89)
  exact Q'.le_trans' _ _ _ hcleared
    (Q'.le_of_eqv
      (tailEnvelopeE8ChartB_affine_projective_scaling D n hn hn2D))

/-- The unscaled projective E8 chart-B numerator is nonnegative; the only
cancelled factor is the explicitly positive exact integer `182^44`. -/
theorem tailEnvelopeE8ChartBRawEval_nonnegative
    (D n : Nat) (hn : 91 ≤ n)
    (hn2D : n ≤ 2 * D) (hDhigh : D ≤ n * n) :
    (0 : Q') ≤
      tailEnvelopeE8ChartBRawEval (Q'.ofNat D) (Q'.ofNat n) := by
  let raw := tailEnvelopeE8ChartBRawEval (Q'.ofNat D) (Q'.ofNat n)
  let scale := Q'.ofNat (182 ^ 44)
  have hscaled : (0 : Q') ≤ raw * scale :=
    tailEnvelopeE8ChartBRawEval_scaled_nonnegative
      D n hn hn2D hDhigh
  have hscaleFirst : (0 : Q') ≤ scale * raw :=
    Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (Q'.mul_comm_eqv raw scale))
  have hscalePos : (0 : Q') < scale := by
    dsimp only [scale]
    exact ofNat_pos_of_pos (182 ^ 44)
      (Nat.pow_pos (by decide : 0 < (182 : Nat)))
  exact Q'.nonneg_of_mul_pos hscalePos hscaleFirst

/-! ## Dependency gates -/

#print axioms chartBDenominator
#print axioms chartBDenominator_pos
#print axioms normalized_chartB_bounds
#print axioms normalized_chartB_affine_relation
#print axioms tailEnvelopeE8ChartBAffineEval
#print axioms tailEnvelopeE8ChartBAffineEval_nonnegative
#print axioms tailEnvelopeE8ChartB_physical_affine_scaling
#print axioms tailEnvelopeE8ChartB_preChart_projective
#print axioms tailEnvelopeE8ChartB_affine_projective_scaling
#print axioms tailEnvelopeE8ChartBRawEval_scaled_nonnegative
#print axioms tailEnvelopeE8ChartBRawEval_nonnegative

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartBAffinePhysical
