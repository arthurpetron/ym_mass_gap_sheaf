/-
# Exact affine reconstruction for the lower-six E9 chart B

The generated pre-chart table is triangular in the support sense needed by
the generic affine semantic theorem.  The full table is checked in thirteen
shallow row shards so kernel reduction remains within the default recursion
depth.
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE9ChartBAggregateSlice0
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE9ChartBAggregateSlice1
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE9ChartBAggregateSlice2
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE9ChartBAggregateSlice3
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE9ChartBAggregateSlice4
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE9ChartBAggregateSlice5
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE9ChartBAggregateSlice6
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE9ChartBAggregateSlice7
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE9ChartBAggregateSlice8
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE9ChartBAggregateSlice9
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE9ChartBAggregateSlice10
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE9ChartBAggregateSlice11
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE9ChartBAggregateSlice12
import YMGap.Continuum.TensorBernsteinQuadraticAffineChartReconstruction

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE9ChartBAffineReconstruction

open YMGap.Constructive
open YMGap.Continuum.TensorBernsteinSeparableReconstruction
open YMGap.Continuum.TensorBernsteinQuadraticAffineChartReconstruction
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCoefficientKernel
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateRows
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE9ChartB

local infix:50 " ≈ " => Q'.eqv

/-! ## Shard-local triangular support checks -/

theorem tailEnvelopeE9ChartB_triangular_slice0 :
    GridTriangularSupportSlice 0 7 87 44
      (gridCoeff tailEnvelopeE9ChartBPreChartRows0) = true := by
  decide

theorem tailEnvelopeE9ChartB_triangular_slice1 :
    GridTriangularSupportSlice 7 7 87 44
      (gridCoeff tailEnvelopeE9ChartBPreChartRows1) = true := by
  decide

theorem tailEnvelopeE9ChartB_triangular_slice2 :
    GridTriangularSupportSlice 14 7 87 44
      (gridCoeff tailEnvelopeE9ChartBPreChartRows2) = true := by
  decide

theorem tailEnvelopeE9ChartB_triangular_slice3 :
    GridTriangularSupportSlice 21 7 87 44
      (gridCoeff tailEnvelopeE9ChartBPreChartRows3) = true := by
  decide

theorem tailEnvelopeE9ChartB_triangular_slice4 :
    GridTriangularSupportSlice 28 7 87 44
      (gridCoeff tailEnvelopeE9ChartBPreChartRows4) = true := by
  decide

theorem tailEnvelopeE9ChartB_triangular_slice5 :
    GridTriangularSupportSlice 35 7 87 44
      (gridCoeff tailEnvelopeE9ChartBPreChartRows5) = true := by
  decide

theorem tailEnvelopeE9ChartB_triangular_slice6 :
    GridTriangularSupportSlice 42 7 87 44
      (gridCoeff tailEnvelopeE9ChartBPreChartRows6) = true := by
  decide

theorem tailEnvelopeE9ChartB_triangular_slice7 :
    GridTriangularSupportSlice 49 7 87 44
      (gridCoeff tailEnvelopeE9ChartBPreChartRows7) = true := by
  decide

theorem tailEnvelopeE9ChartB_triangular_slice8 :
    GridTriangularSupportSlice 56 7 87 44
      (gridCoeff tailEnvelopeE9ChartBPreChartRows8) = true := by
  decide

theorem tailEnvelopeE9ChartB_triangular_slice9 :
    GridTriangularSupportSlice 63 7 87 44
      (gridCoeff tailEnvelopeE9ChartBPreChartRows9) = true := by
  decide

theorem tailEnvelopeE9ChartB_triangular_slice10 :
    GridTriangularSupportSlice 70 7 87 44
      (gridCoeff tailEnvelopeE9ChartBPreChartRows10) = true := by
  decide

theorem tailEnvelopeE9ChartB_triangular_slice11 :
    GridTriangularSupportSlice 77 7 87 44
      (gridCoeff tailEnvelopeE9ChartBPreChartRows11) = true := by
  decide

theorem tailEnvelopeE9ChartB_triangular_slice12 :
    GridTriangularSupportSlice 84 4 87 44
      (gridCoeff tailEnvelopeE9ChartBPreChartRows12) = true := by
  decide

/-! ## Global support and semantic reconstruction -/

theorem tailEnvelopeE9ChartB_preChart_length :
    tailEnvelopeE9ChartBPreChartRows.length ≤ 88 := by
  decide

theorem tailEnvelopeE9ChartB_triangular_at
    {a i : Nat} (ha : a < 88) (hi : i < 45)
    (hdegree : 87 < a + i) :
    gridCoeff tailEnvelopeE9ChartBPreChartRows a i = 0 := by
  by_cases h0 : a < 7
  · exact gridTriangularSupportSlice_to_global 0 7 87 44
      (gridCoeff tailEnvelopeE9ChartBPreChartRows0)
      (gridCoeff tailEnvelopeE9ChartBPreChartRows)
      tailEnvelopeE9ChartB_triangular_slice0
      tailEnvelopeE9ChartB_preChart_aggregate_slice0
      (by omega) h0 hi hdegree
  · by_cases h1 : a < 14
    · exact gridTriangularSupportSlice_to_global 7 7 87 44
        (gridCoeff tailEnvelopeE9ChartBPreChartRows1)
        (gridCoeff tailEnvelopeE9ChartBPreChartRows)
        tailEnvelopeE9ChartB_triangular_slice1
        tailEnvelopeE9ChartB_preChart_aggregate_slice1
        (by omega) h1 hi hdegree
    · by_cases h2 : a < 21
      · exact gridTriangularSupportSlice_to_global 14 7 87 44
          (gridCoeff tailEnvelopeE9ChartBPreChartRows2)
          (gridCoeff tailEnvelopeE9ChartBPreChartRows)
          tailEnvelopeE9ChartB_triangular_slice2
          tailEnvelopeE9ChartB_preChart_aggregate_slice2
          (by omega) h2 hi hdegree
      · by_cases h3 : a < 28
        · exact gridTriangularSupportSlice_to_global 21 7 87 44
            (gridCoeff tailEnvelopeE9ChartBPreChartRows3)
            (gridCoeff tailEnvelopeE9ChartBPreChartRows)
            tailEnvelopeE9ChartB_triangular_slice3
            tailEnvelopeE9ChartB_preChart_aggregate_slice3
            (by omega) h3 hi hdegree
        · by_cases h4 : a < 35
          · exact gridTriangularSupportSlice_to_global 28 7 87 44
              (gridCoeff tailEnvelopeE9ChartBPreChartRows4)
              (gridCoeff tailEnvelopeE9ChartBPreChartRows)
              tailEnvelopeE9ChartB_triangular_slice4
              tailEnvelopeE9ChartB_preChart_aggregate_slice4
              (by omega) h4 hi hdegree
          · by_cases h5 : a < 42
            · exact gridTriangularSupportSlice_to_global 35 7 87 44
                (gridCoeff tailEnvelopeE9ChartBPreChartRows5)
                (gridCoeff tailEnvelopeE9ChartBPreChartRows)
                tailEnvelopeE9ChartB_triangular_slice5
                tailEnvelopeE9ChartB_preChart_aggregate_slice5
                (by omega) h5 hi hdegree
            · by_cases h6 : a < 49
              · exact gridTriangularSupportSlice_to_global 42 7 87 44
                  (gridCoeff tailEnvelopeE9ChartBPreChartRows6)
                  (gridCoeff tailEnvelopeE9ChartBPreChartRows)
                  tailEnvelopeE9ChartB_triangular_slice6
                  tailEnvelopeE9ChartB_preChart_aggregate_slice6
                  (by omega) h6 hi hdegree
              · by_cases h7 : a < 56
                · exact gridTriangularSupportSlice_to_global 49 7 87 44
                    (gridCoeff tailEnvelopeE9ChartBPreChartRows7)
                    (gridCoeff tailEnvelopeE9ChartBPreChartRows)
                    tailEnvelopeE9ChartB_triangular_slice7
                    tailEnvelopeE9ChartB_preChart_aggregate_slice7
                    (by omega) h7 hi hdegree
                · by_cases h8 : a < 63
                  · exact gridTriangularSupportSlice_to_global 56 7 87 44
                      (gridCoeff tailEnvelopeE9ChartBPreChartRows8)
                      (gridCoeff tailEnvelopeE9ChartBPreChartRows)
                      tailEnvelopeE9ChartB_triangular_slice8
                      tailEnvelopeE9ChartB_preChart_aggregate_slice8
                      (by omega) h8 hi hdegree
                  · by_cases h9 : a < 70
                    · exact gridTriangularSupportSlice_to_global 63 7 87 44
                        (gridCoeff tailEnvelopeE9ChartBPreChartRows9)
                        (gridCoeff tailEnvelopeE9ChartBPreChartRows)
                        tailEnvelopeE9ChartB_triangular_slice9
                        tailEnvelopeE9ChartB_preChart_aggregate_slice9
                        (by omega) h9 hi hdegree
                    · by_cases h10 : a < 77
                      · exact gridTriangularSupportSlice_to_global 70 7 87 44
                          (gridCoeff tailEnvelopeE9ChartBPreChartRows10)
                          (gridCoeff tailEnvelopeE9ChartBPreChartRows)
                          tailEnvelopeE9ChartB_triangular_slice10
                          tailEnvelopeE9ChartB_preChart_aggregate_slice10
                          (by omega) h10 hi hdegree
                      · by_cases h11 : a < 84
                        · exact gridTriangularSupportSlice_to_global 77 7 87 44
                            (gridCoeff tailEnvelopeE9ChartBPreChartRows11)
                            (gridCoeff tailEnvelopeE9ChartBPreChartRows)
                            tailEnvelopeE9ChartB_triangular_slice11
                            tailEnvelopeE9ChartB_preChart_aggregate_slice11
                            (by omega) h11 hi hdegree
                        · exact gridTriangularSupportSlice_to_global 84 4 87 44
                            (gridCoeff tailEnvelopeE9ChartBPreChartRows12)
                            (gridCoeff tailEnvelopeE9ChartBPreChartRows)
                            tailEnvelopeE9ChartB_triangular_slice12
                            tailEnvelopeE9ChartB_preChart_aggregate_slice12
                            (by omega) ha hi hdegree

/-- Exact E9 chart-B affine reconstruction at the certificate's original
degrees. -/
theorem tailEnvelopeE9ChartB_affine_reconstruction
    (x z r : Q')
    (hr : Q'.ofNat 182 * r ≈
      Q'.ofNat 182 * z + x * ((1 : Q') + -z)) :
    tensorPowerEval 87 44
        (affineChartBClearedCoeff 44 tailEnvelopeE9ChartBPreChartRows) x z ≈
      tensorPowerEval 87 44
          (gridCoeff tailEnvelopeE9ChartBPreChartRows) x r *
        Q'.ofNat (182 ^ 44) := by
  exact tensorPowerEval_affineChartBClearedCoeff_triangular
    87 44 tailEnvelopeE9ChartBPreChartRows x z r
    tailEnvelopeE9ChartB_preChart_length
    (fun a ha i hi hdegree =>
      tailEnvelopeE9ChartB_triangular_at ha hi hdegree)
    hr

/-! ## Dependency gates -/

#print axioms tailEnvelopeE9ChartB_triangular_slice0
#print axioms tailEnvelopeE9ChartB_triangular_slice12
#print axioms tailEnvelopeE9ChartB_triangular_at
#print axioms tailEnvelopeE9ChartB_affine_reconstruction

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE9ChartBAffineReconstruction
