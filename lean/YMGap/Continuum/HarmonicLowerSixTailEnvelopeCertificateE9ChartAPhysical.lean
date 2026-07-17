/-
# Physical chart-A consumer for the lower-six E9 envelope certificate

On `tailEnvelopeModeChartBase ≤ n` and `n² ≤ D ≤ 2*n²`, this is the ninth-order
counterpart of the E8 chart-A consumer.  The exact nonnegative Bernstein
table is transported through the quadratic projective coordinates to the
generated raw `(D,n)` numerator.
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE9ChartACoefficientCertificate
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartAPhysical

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE9ChartAPhysical

open YMGap.Constructive
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateRows
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE9ChartA
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCoefficientKernel
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartAPhysical
open YMGap.Continuum.TensorBernsteinQuadraticProjectiveReconstruction
open YMGap.Continuum.TensorBernsteinSeparableReconstruction

local infix:50 " ≈ " => Q'.eqv

/-- Raw coefficients scaled by the exact E9 chart-A quotient checked in the
coefficient certificate. -/
def tailEnvelopeE9ChartAScaledRaw (i j : Nat) : Int :=
  Int.ofNat tailEnvelopeE9ChartAChartQuotient *
    gridCoeff tailEnvelopeE9ClearedRows i j

/-- The exact projectively homogeneous E9 numerator on chart A. -/
def tailEnvelopeE9ChartARawEval (D n : Q') : Q' :=
  quadraticPowerEval 87 44 89 tailEnvelopeE9ChartAScaledRaw D n

/-- **Physical E9 chart-A sign certificate.** -/
theorem tailEnvelopeE9ChartARawEval_nonnegative
    (D n : Nat) (hn : tailEnvelopeModeChartBase ≤ n)
    (hDlow : n * n ≤ D) (hDhigh : D ≤ 2 * (n * n)) :
    (0 : Q') ≤
      tailEnvelopeE9ChartARawEval (Q'.ofNat D) (Q'.ofNat n) := by
  have hnpos : 0 < n := Nat.lt_of_lt_of_le (by decide) hn
  have hn2pos : 0 < n * n := Nat.mul_pos hnpos hnpos
  let x := Q'.mkPos tailEnvelopeModeChartBase n hnpos
  let r := Q'.mkPos (Int.ofNat D - Int.ofNat (n * n))
    (n * n) hn2pos
  let den := Q'.ofNat n
  let targetD := Q'.ofNat D
  have hbounds := normalized_chartA_bounds D n hnpos hn hDlow hDhigh
  have htable :
      (0 : Q') ≤ tensorBernsteinEval 87 44
        (weightedGrid 87 44 tailEnvelopeE9ChartABernsteinRows) x r :=
    tensorBernsteinEval_nonnegative 87 44
      (weightedGrid 87 44 tailEnvelopeE9ChartABernsteinRows) x r
      hbounds.1 hbounds.2.1 hbounds.2.2.1 hbounds.2.2.2
      (fun i hi j hj => by
        unfold weightedGrid
        exact Int.mul_nonneg
          (tailEnvelopeE9ChartA_nonnegative_at hi hj)
          (Int.natCast_nonneg _))
  have hreconstruction :
      tensorBernsteinEval 87 44
          (weightedGrid 87 44 tailEnvelopeE9ChartABernsteinRows) x r ≈
        tensorPowerEval 87 44
          (gridCoeff tailEnvelopeE9ChartAScaledPowerRows) x r :=
    tensorBernsteinEval_eqv_powerEval 87 44
      (gridCoeff tailEnvelopeE9ChartAScaledPowerRows)
      (weightedGrid 87 44 tailEnvelopeE9ChartABernsteinRows) x r
      (fun i hi j hj => tailEnvelopeE9ChartA_transform_at hi hj)
  have hpower :
      (0 : Q') ≤ tensorPowerEval 87 44
        (gridCoeff tailEnvelopeE9ChartAScaledPowerRows) x r :=
    Q'.le_trans' _ _ _ htable (Q'.le_of_eqv hreconstruction)
  have hdenNonnegative : (0 : Q') ≤ den := ofNat_nonnegative n
  have hcleared :
      (0 : Q') ≤ tensorPowerEval 87 44
          (gridCoeff tailEnvelopeE9ChartAScaledPowerRows) x r * den ^ 89 :=
    Q'.mul_nonneg _ _ hpower (Q'.pow_nonneg den hdenNonnegative 89)
  have hxden : x * den ≈ Q'.ofNat tailEnvelopeModeChartBase := by
    exact mkPos_mul_ofNat_eqv tailEnvelopeModeChartBase n hnpos
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
      tensorPowerEval 87 44
          (gridCoeff tailEnvelopeE9ChartAScaledPowerRows) x r * den ^ 89 ≈
        tailEnvelopeE9ChartARawEval targetD den := by
    unfold tailEnvelopeE9ChartARawEval
    apply tensorPowerEval_mul_den_pow_eqv_quadratic
      87 44 89 tailEnvelopeModeChartBase
      (gridCoeff tailEnvelopeE9ChartAScaledPowerRows)
      (gridCoeff tailEnvelopeE9ChartAPreChartRows)
      tailEnvelopeE9ChartAScaledRaw x r den targetD
    · decide
    · exact hxden
    · exact hrden
    · intro u hu b hb
      exact tailEnvelopeE9ChartA_shift_at hu hb
    · intro u hu i hi
      have hraw := tailEnvelopeE9ChartA_raw_at hu hi
      unfold quadraticRawExpected at hraw
      unfold quadraticRawLift tailEnvelopeE9ChartAScaledRaw
      exact hraw
  exact Q'.le_trans' _ _ _ hcleared (Q'.le_of_eqv hprojective)

/-! ## Dependency gates -/

#print axioms tailEnvelopeE9ChartAScaledRaw
#print axioms tailEnvelopeE9ChartARawEval
#print axioms tailEnvelopeE9ChartARawEval_nonnegative

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE9ChartAPhysical
