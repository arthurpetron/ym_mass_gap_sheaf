/-
# Exact affine reconstruction for the lower-six E8 chart B

The generated pre-chart table is triangular in the support sense needed by
the generic affine semantic theorem.  The full table is deliberately checked
in thirteen shallow row shards so kernel reduction remains within the default
recursion depth.
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartBAggregateSlice0
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartBAggregateSlice1
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartBAggregateSlice2
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartBAggregateSlice3
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartBAggregateSlice4
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartBAggregateSlice5
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartBAggregateSlice6
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartBAggregateSlice7
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartBAggregateSlice8
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartBAggregateSlice9
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartBAggregateSlice10
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartBAggregateSlice11
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartBAggregateSlice12
import YMGap.Continuum.TensorBernsteinQuadraticAffineChartReconstruction

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartBAffineReconstruction

open YMGap.Constructive
open YMGap.Continuum.TensorBernsteinSeparableReconstruction
open YMGap.Continuum.TensorBernsteinQuadraticAffineChartReconstruction
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCoefficientKernel
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateRows
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartB

local infix:50 " ≈ " => Q'.eqv

/-! ## Shard-local triangular support checks -/

theorem tailEnvelopeE8ChartB_triangular_slice0 :
    GridTriangularSupportSlice 0 7 85 44
      (gridCoeff tailEnvelopeE8ChartBPreChartRows0) = true := by
  decide

theorem tailEnvelopeE8ChartB_triangular_slice1 :
    GridTriangularSupportSlice 7 7 85 44
      (gridCoeff tailEnvelopeE8ChartBPreChartRows1) = true := by
  decide

theorem tailEnvelopeE8ChartB_triangular_slice2 :
    GridTriangularSupportSlice 14 7 85 44
      (gridCoeff tailEnvelopeE8ChartBPreChartRows2) = true := by
  decide

theorem tailEnvelopeE8ChartB_triangular_slice3 :
    GridTriangularSupportSlice 21 7 85 44
      (gridCoeff tailEnvelopeE8ChartBPreChartRows3) = true := by
  decide

theorem tailEnvelopeE8ChartB_triangular_slice4 :
    GridTriangularSupportSlice 28 7 85 44
      (gridCoeff tailEnvelopeE8ChartBPreChartRows4) = true := by
  decide

theorem tailEnvelopeE8ChartB_triangular_slice5 :
    GridTriangularSupportSlice 35 7 85 44
      (gridCoeff tailEnvelopeE8ChartBPreChartRows5) = true := by
  decide

theorem tailEnvelopeE8ChartB_triangular_slice6 :
    GridTriangularSupportSlice 42 7 85 44
      (gridCoeff tailEnvelopeE8ChartBPreChartRows6) = true := by
  decide

theorem tailEnvelopeE8ChartB_triangular_slice7 :
    GridTriangularSupportSlice 49 7 85 44
      (gridCoeff tailEnvelopeE8ChartBPreChartRows7) = true := by
  decide

theorem tailEnvelopeE8ChartB_triangular_slice8 :
    GridTriangularSupportSlice 56 7 85 44
      (gridCoeff tailEnvelopeE8ChartBPreChartRows8) = true := by
  decide

theorem tailEnvelopeE8ChartB_triangular_slice9 :
    GridTriangularSupportSlice 63 7 85 44
      (gridCoeff tailEnvelopeE8ChartBPreChartRows9) = true := by
  decide

theorem tailEnvelopeE8ChartB_triangular_slice10 :
    GridTriangularSupportSlice 70 7 85 44
      (gridCoeff tailEnvelopeE8ChartBPreChartRows10) = true := by
  decide

theorem tailEnvelopeE8ChartB_triangular_slice11 :
    GridTriangularSupportSlice 77 7 85 44
      (gridCoeff tailEnvelopeE8ChartBPreChartRows11) = true := by
  decide

theorem tailEnvelopeE8ChartB_triangular_slice12 :
    GridTriangularSupportSlice 84 2 85 44
      (gridCoeff tailEnvelopeE8ChartBPreChartRows12) = true := by
  decide

/-! ## Global support and semantic reconstruction -/

theorem tailEnvelopeE8ChartB_preChart_length :
    tailEnvelopeE8ChartBPreChartRows.length ≤ 86 := by
  decide

theorem tailEnvelopeE8ChartB_triangular_at
    {a i : Nat} (ha : a < 86) (hi : i < 45)
    (hdegree : 85 < a + i) :
    gridCoeff tailEnvelopeE8ChartBPreChartRows a i = 0 := by
  by_cases h0 : a < 7
  · exact gridTriangularSupportSlice_to_global 0 7 85 44
      (gridCoeff tailEnvelopeE8ChartBPreChartRows0)
      (gridCoeff tailEnvelopeE8ChartBPreChartRows)
      tailEnvelopeE8ChartB_triangular_slice0
      tailEnvelopeE8ChartB_preChart_aggregate_slice0
      (by omega) h0 hi hdegree
  · by_cases h1 : a < 14
    · exact gridTriangularSupportSlice_to_global 7 7 85 44
        (gridCoeff tailEnvelopeE8ChartBPreChartRows1)
        (gridCoeff tailEnvelopeE8ChartBPreChartRows)
        tailEnvelopeE8ChartB_triangular_slice1
        tailEnvelopeE8ChartB_preChart_aggregate_slice1
        (by omega) h1 hi hdegree
    · by_cases h2 : a < 21
      · exact gridTriangularSupportSlice_to_global 14 7 85 44
          (gridCoeff tailEnvelopeE8ChartBPreChartRows2)
          (gridCoeff tailEnvelopeE8ChartBPreChartRows)
          tailEnvelopeE8ChartB_triangular_slice2
          tailEnvelopeE8ChartB_preChart_aggregate_slice2
          (by omega) h2 hi hdegree
      · by_cases h3 : a < 28
        · exact gridTriangularSupportSlice_to_global 21 7 85 44
            (gridCoeff tailEnvelopeE8ChartBPreChartRows3)
            (gridCoeff tailEnvelopeE8ChartBPreChartRows)
            tailEnvelopeE8ChartB_triangular_slice3
            tailEnvelopeE8ChartB_preChart_aggregate_slice3
            (by omega) h3 hi hdegree
        · by_cases h4 : a < 35
          · exact gridTriangularSupportSlice_to_global 28 7 85 44
              (gridCoeff tailEnvelopeE8ChartBPreChartRows4)
              (gridCoeff tailEnvelopeE8ChartBPreChartRows)
              tailEnvelopeE8ChartB_triangular_slice4
              tailEnvelopeE8ChartB_preChart_aggregate_slice4
              (by omega) h4 hi hdegree
          · by_cases h5 : a < 42
            · exact gridTriangularSupportSlice_to_global 35 7 85 44
                (gridCoeff tailEnvelopeE8ChartBPreChartRows5)
                (gridCoeff tailEnvelopeE8ChartBPreChartRows)
                tailEnvelopeE8ChartB_triangular_slice5
                tailEnvelopeE8ChartB_preChart_aggregate_slice5
                (by omega) h5 hi hdegree
            · by_cases h6 : a < 49
              · exact gridTriangularSupportSlice_to_global 42 7 85 44
                  (gridCoeff tailEnvelopeE8ChartBPreChartRows6)
                  (gridCoeff tailEnvelopeE8ChartBPreChartRows)
                  tailEnvelopeE8ChartB_triangular_slice6
                  tailEnvelopeE8ChartB_preChart_aggregate_slice6
                  (by omega) h6 hi hdegree
              · by_cases h7 : a < 56
                · exact gridTriangularSupportSlice_to_global 49 7 85 44
                    (gridCoeff tailEnvelopeE8ChartBPreChartRows7)
                    (gridCoeff tailEnvelopeE8ChartBPreChartRows)
                    tailEnvelopeE8ChartB_triangular_slice7
                    tailEnvelopeE8ChartB_preChart_aggregate_slice7
                    (by omega) h7 hi hdegree
                · by_cases h8 : a < 63
                  · exact gridTriangularSupportSlice_to_global 56 7 85 44
                      (gridCoeff tailEnvelopeE8ChartBPreChartRows8)
                      (gridCoeff tailEnvelopeE8ChartBPreChartRows)
                      tailEnvelopeE8ChartB_triangular_slice8
                      tailEnvelopeE8ChartB_preChart_aggregate_slice8
                      (by omega) h8 hi hdegree
                  · by_cases h9 : a < 70
                    · exact gridTriangularSupportSlice_to_global 63 7 85 44
                        (gridCoeff tailEnvelopeE8ChartBPreChartRows9)
                        (gridCoeff tailEnvelopeE8ChartBPreChartRows)
                        tailEnvelopeE8ChartB_triangular_slice9
                        tailEnvelopeE8ChartB_preChart_aggregate_slice9
                        (by omega) h9 hi hdegree
                    · by_cases h10 : a < 77
                      · exact gridTriangularSupportSlice_to_global 70 7 85 44
                          (gridCoeff tailEnvelopeE8ChartBPreChartRows10)
                          (gridCoeff tailEnvelopeE8ChartBPreChartRows)
                          tailEnvelopeE8ChartB_triangular_slice10
                          tailEnvelopeE8ChartB_preChart_aggregate_slice10
                          (by omega) h10 hi hdegree
                      · by_cases h11 : a < 84
                        · exact gridTriangularSupportSlice_to_global 77 7 85 44
                            (gridCoeff tailEnvelopeE8ChartBPreChartRows11)
                            (gridCoeff tailEnvelopeE8ChartBPreChartRows)
                            tailEnvelopeE8ChartB_triangular_slice11
                            tailEnvelopeE8ChartB_preChart_aggregate_slice11
                            (by omega) h11 hi hdegree
                        · exact gridTriangularSupportSlice_to_global 84 2 85 44
                            (gridCoeff tailEnvelopeE8ChartBPreChartRows12)
                            (gridCoeff tailEnvelopeE8ChartBPreChartRows)
                            tailEnvelopeE8ChartB_triangular_slice12
                            tailEnvelopeE8ChartB_preChart_aggregate_slice12
                            (by omega) ha hi hdegree

/-- Exact E8 chart-B affine reconstruction at the certificate's original
degrees. -/
theorem tailEnvelopeE8ChartB_affine_reconstruction
    (x z r : Q')
    (hr : Q'.ofNat 28 * r ≈
      Q'.ofNat 28 * z + x * ((1 : Q') + -z)) :
    tensorPowerEval 85 44
        (affineChartBClearedCoeff 44 tailEnvelopeE8ChartBPreChartRows) x z ≈
      tensorPowerEval 85 44
          (gridCoeff tailEnvelopeE8ChartBPreChartRows) x r *
        Q'.ofNat (28 ^ 44) := by
  exact tensorPowerEval_affineChartBClearedCoeff_triangular
    85 44 tailEnvelopeE8ChartBPreChartRows x z r
    tailEnvelopeE8ChartB_preChart_length
    (fun a ha i hi hdegree =>
      tailEnvelopeE8ChartB_triangular_at ha hi hdegree)
    hr

/-! ## Dependency gates -/

#print axioms tailEnvelopeE8ChartB_triangular_slice0
#print axioms tailEnvelopeE8ChartB_triangular_slice12
#print axioms tailEnvelopeE8ChartB_triangular_at
#print axioms tailEnvelopeE8ChartB_affine_reconstruction

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartBAffineReconstruction
