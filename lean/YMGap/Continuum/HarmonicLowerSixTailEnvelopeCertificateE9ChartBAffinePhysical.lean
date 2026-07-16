/-
# Physical affine-table consumer for the lower-six E9 chart B

This module reuses the exact chart-B coordinates proved for E8, transports
the E9 Bernstein sign table through its checked affine reconstruction, and
identifies the result with the exact projective raw numerator.
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE9ChartBCoefficientCertificate
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE9ChartBAffineReconstruction
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartBAffinePhysical

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE9ChartBAffinePhysical

open YMGap.Constructive
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateRows
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE9ChartB
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE9ChartBAffineReconstruction
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCoefficientKernel
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartAPhysical
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartBAffinePhysical
open YMGap.Continuum.TensorBernsteinQuadraticProjectiveReconstruction
open YMGap.Continuum.TensorBernsteinQuadraticAffineChartReconstruction
open YMGap.Continuum.TensorBernsteinSeparableReconstruction

local infix:50 " ≈ " => Q'.eqv

/-- The coefficient-cleared affine E9 chart-B power polynomial. -/
def tailEnvelopeE9ChartBAffineEval (x z : Q') : Q' :=
  tensorPowerEval 87 44
    (affineChartBClearedCoeff 44 tailEnvelopeE9ChartBPreChartRows) x z

/-- The physical affine E9 grid is nonnegative. -/
theorem tailEnvelopeE9ChartBAffineEval_nonnegative
    (D n : Nat) (hn : 91 ≤ n)
    (hn2D : n ≤ 2 * D) (hDhigh : D ≤ n * n) :
    (0 : Q') ≤
      tailEnvelopeE9ChartBAffineEval
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
      (0 : Q') ≤ tensorBernsteinEval 87 44
        (weightedGrid 87 44 tailEnvelopeE9ChartBBernsteinRows) x z :=
    tensorBernsteinEval_nonnegative 87 44
      (weightedGrid 87 44 tailEnvelopeE9ChartBBernsteinRows) x z
      hbounds.1 hbounds.2.1 hbounds.2.2.1 hbounds.2.2.2
      (fun i hi j hj => by
        unfold weightedGrid
        exact Int.mul_nonneg
          (tailEnvelopeE9ChartB_nonnegative_at hi hj)
          (Int.natCast_nonneg _))
  have hreconstruction :
      tensorBernsteinEval 87 44
          (weightedGrid 87 44 tailEnvelopeE9ChartBBernsteinRows) x z ≈
        tensorPowerEval 87 44
          (gridCoeff tailEnvelopeE9ChartBScaledPowerRows) x z :=
    tensorBernsteinEval_eqv_powerEval 87 44
      (gridCoeff tailEnvelopeE9ChartBScaledPowerRows)
      (weightedGrid 87 44 tailEnvelopeE9ChartBBernsteinRows) x z
      (fun i hi j hj => tailEnvelopeE9ChartB_transform_at hi hj)
  have hpower :
      (0 : Q') ≤ tensorPowerEval 87 44
        (gridCoeff tailEnvelopeE9ChartBScaledPowerRows) x z :=
    Q'.le_trans' _ _ _ htable (Q'.le_of_eqv hreconstruction)
  let scale : Int := Int.ofNat (182 ^ 44)
  have hscaleNonnegative : (0 : Q') ≤ Q'.ofInt scale := by
    dsimp only [scale]
    exact ofNat_nonnegative (182 ^ 44)
  have hscaled :
      (0 : Q') ≤ tensorPowerEval 87 44
          (gridCoeff tailEnvelopeE9ChartBScaledPowerRows) x z *
        Q'.ofInt scale :=
    Q'.mul_nonneg _ _ hpower hscaleNonnegative
  have haffineCoeff :
      tailEnvelopeE9ChartBAffineEval x z ≈
        tensorPowerEval 87 44
          (fun i j => gridCoeff tailEnvelopeE9ChartBScaledPowerRows i j *
            scale) x z := by
    unfold tailEnvelopeE9ChartBAffineEval
    apply tensorPowerEval_congr
    intro i hi j hj
    dsimp only [scale]
    exact Eq.symm (tailEnvelopeE9ChartB_affine_at hi hj)
  have hscaledEval :
      tensorPowerEval 87 44
          (fun i j => gridCoeff tailEnvelopeE9ChartBScaledPowerRows i j *
            scale) x z ≈
        tensorPowerEval 87 44
          (gridCoeff tailEnvelopeE9ChartBScaledPowerRows) x z *
            Q'.ofInt scale :=
    tensorPowerEval_scale_right 87 44
      (gridCoeff tailEnvelopeE9ChartBScaledPowerRows) scale x z
  have haffine := Q'.eqv_trans _ _ _ haffineCoeff hscaledEval
  exact Q'.le_trans' _ _ _ hscaled (Q'.ge_of_eqv haffine)

/-- The original E9 pre-chart power polynomial. -/
def tailEnvelopeE9ChartBPreChartEval (x r : Q') : Q' :=
  tensorPowerEval 87 44
    (gridCoeff tailEnvelopeE9ChartBPreChartRows) x r

/-- Raw E9 coefficients multiplied by the exact chart quotient checked in
the coefficient certificate. -/
def tailEnvelopeE9ChartBScaledRaw (i j : Nat) : Int :=
  Int.ofNat tailEnvelopeE9ChartBChartQuotient *
    gridCoeff tailEnvelopeE9ClearedRows i j

/-- The exact projectively homogeneous E9 numerator on chart B. -/
def tailEnvelopeE9ChartBRawEval (D n : Q') : Q' :=
  quadraticPowerEval 87 44 89 tailEnvelopeE9ChartBScaledRaw D n

/-- Exact physical affine scaling for E9. -/
theorem tailEnvelopeE9ChartB_physical_affine_scaling
    (D n : Nat) (hn : 91 ≤ n) (hn2D : n ≤ 2 * D) :
    tailEnvelopeE9ChartBAffineEval
        (Q'.mkPos 91 n (Nat.lt_of_lt_of_le (by decide) hn))
        (Q'.mkPos (Int.ofNat (2 * D - n)) (chartBDenominator n)
          (chartBDenominator_pos
            (Nat.lt_of_lt_of_le (by decide) hn))) ≈
      tailEnvelopeE9ChartBPreChartEval
          (Q'.mkPos 91 n (Nat.lt_of_lt_of_le (by decide) hn))
          (Q'.mkPos (Int.ofNat D) (n * n)
            (Nat.mul_pos
              (Nat.lt_of_lt_of_le (by decide) hn)
              (Nat.lt_of_lt_of_le (by decide) hn))) *
        Q'.ofNat (182 ^ 44) := by
  have hnpos : 0 < n := Nat.lt_of_lt_of_le (by decide) hn
  unfold tailEnvelopeE9ChartBAffineEval tailEnvelopeE9ChartBPreChartEval
  exact tailEnvelopeE9ChartB_affine_reconstruction
    (Q'.mkPos 91 n hnpos)
    (Q'.mkPos (Int.ofNat (2 * D - n)) (chartBDenominator n)
      (chartBDenominator_pos hnpos))
    (Q'.mkPos (Int.ofNat D) (n * n) (Nat.mul_pos hnpos hnpos))
    (normalized_chartB_affine_relation D n hnpos hn2D)

/-- Exact projective clearing of the E9 pre-chart power polynomial. -/
theorem tailEnvelopeE9ChartB_preChart_projective
    (D n : Nat) (hnpos : 0 < n) :
    tailEnvelopeE9ChartBPreChartEval
        (Q'.mkPos 91 n hnpos)
        (Q'.mkPos (Int.ofNat D) (n * n) (Nat.mul_pos hnpos hnpos)) *
      Q'.ofNat n ^ 89 ≈
        tailEnvelopeE9ChartBRawEval (Q'.ofNat D) (Q'.ofNat n) := by
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
  unfold tailEnvelopeE9ChartBPreChartEval tailEnvelopeE9ChartBRawEval
  apply tensorPowerEval_mul_den_pow_eqv_quadratic_direct
    87 44 89 91
    (gridCoeff tailEnvelopeE9ChartBPreChartRows)
    tailEnvelopeE9ChartBScaledRaw x r den targetD
  · decide
  · exact hxden
  · exact hrden
  · intro u hu i hi
    have hraw := tailEnvelopeE9ChartB_raw_at hu hi
    unfold quadraticRawExpected at hraw
    unfold quadraticRawLift tailEnvelopeE9ChartBScaledRaw
    exact hraw

/-- Exact physical scaling from the E9 affine polynomial to its projective
raw numerator. -/
theorem tailEnvelopeE9ChartB_affine_projective_scaling
    (D n : Nat) (hn : 91 ≤ n) (hn2D : n ≤ 2 * D) :
    tailEnvelopeE9ChartBAffineEval
        (Q'.mkPos 91 n (Nat.lt_of_lt_of_le (by decide) hn))
        (Q'.mkPos (Int.ofNat (2 * D - n)) (chartBDenominator n)
          (chartBDenominator_pos
            (Nat.lt_of_lt_of_le (by decide) hn))) *
      Q'.ofNat n ^ 89 ≈
        tailEnvelopeE9ChartBRawEval (Q'.ofNat D) (Q'.ofNat n) *
          Q'.ofNat (182 ^ 44) := by
  have hnpos : 0 < n := Nat.lt_of_lt_of_le (by decide) hn
  let x := Q'.mkPos 91 n hnpos
  let z := Q'.mkPos (Int.ofNat (2 * D - n)) (chartBDenominator n)
    (chartBDenominator_pos hnpos)
  let r := Q'.mkPos (Int.ofNat D) (n * n) (Nat.mul_pos hnpos hnpos)
  let pre := tailEnvelopeE9ChartBPreChartEval x r
  let scale := Q'.ofNat (182 ^ 44)
  let denPow := Q'.ofNat n ^ 89
  have haffine : tailEnvelopeE9ChartBAffineEval x z ≈ pre * scale := by
    exact tailEnvelopeE9ChartB_physical_affine_scaling D n hn hn2D
  have hprojective : pre * denPow ≈
      tailEnvelopeE9ChartBRawEval (Q'.ofNat D) (Q'.ofNat n) := by
    exact tailEnvelopeE9ChartB_preChart_projective D n hnpos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ denPow haffine) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv pre scale denPow) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left pre _ _ (Q'.mul_comm_eqv scale denPow)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv pre denPow scale)) ?_
  exact Q'.mul_eqv_congr_right _ _ scale hprojective

/-- The exact scaled raw E9 chart-B numerator is nonnegative throughout the
physical corridor. -/
theorem tailEnvelopeE9ChartBRawEval_scaled_nonnegative
    (D n : Nat) (hn : 91 ≤ n)
    (hn2D : n ≤ 2 * D) (hDhigh : D ≤ n * n) :
    (0 : Q') ≤
      tailEnvelopeE9ChartBRawEval (Q'.ofNat D) (Q'.ofNat n) *
        Q'.ofNat (182 ^ 44) := by
  have haffine :=
    tailEnvelopeE9ChartBAffineEval_nonnegative D n hn hn2D hDhigh
  have hdenNonnegative : (0 : Q') ≤ Q'.ofNat n :=
    ofNat_nonnegative n
  have hcleared :
      (0 : Q') ≤
        tailEnvelopeE9ChartBAffineEval
            (Q'.mkPos 91 n (Nat.lt_of_lt_of_le (by decide) hn))
            (Q'.mkPos (Int.ofNat (2 * D - n)) (chartBDenominator n)
              (chartBDenominator_pos
                (Nat.lt_of_lt_of_le (by decide) hn))) *
          Q'.ofNat n ^ 89 :=
    Q'.mul_nonneg _ _ haffine
      (Q'.pow_nonneg (Q'.ofNat n) hdenNonnegative 89)
  exact Q'.le_trans' _ _ _ hcleared
    (Q'.le_of_eqv
      (tailEnvelopeE9ChartB_affine_projective_scaling D n hn hn2D))

/-- The unscaled projective E9 chart-B numerator is nonnegative. -/
theorem tailEnvelopeE9ChartBRawEval_nonnegative
    (D n : Nat) (hn : 91 ≤ n)
    (hn2D : n ≤ 2 * D) (hDhigh : D ≤ n * n) :
    (0 : Q') ≤
      tailEnvelopeE9ChartBRawEval (Q'.ofNat D) (Q'.ofNat n) := by
  let raw := tailEnvelopeE9ChartBRawEval (Q'.ofNat D) (Q'.ofNat n)
  let scale := Q'.ofNat (182 ^ 44)
  have hscaled : (0 : Q') ≤ raw * scale :=
    tailEnvelopeE9ChartBRawEval_scaled_nonnegative
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

#print axioms tailEnvelopeE9ChartBAffineEval
#print axioms tailEnvelopeE9ChartBAffineEval_nonnegative
#print axioms tailEnvelopeE9ChartB_physical_affine_scaling
#print axioms tailEnvelopeE9ChartB_preChart_projective
#print axioms tailEnvelopeE9ChartB_affine_projective_scaling
#print axioms tailEnvelopeE9ChartBRawEval_scaled_nonnegative
#print axioms tailEnvelopeE9ChartBRawEval_nonnegative

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE9ChartBAffinePhysical
