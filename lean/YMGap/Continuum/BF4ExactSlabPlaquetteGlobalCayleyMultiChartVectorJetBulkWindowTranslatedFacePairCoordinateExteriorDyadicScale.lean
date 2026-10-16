/-
# Linear dyadic scale for the coordinate exterior covariance cutoff

The explicit coordinate carrier has support at most `5*s + 3*L + 5`.
Combining that geometric fact with the exact covariance-amplitude factorization
and the quartic shell count turns the executable exterior cutoff into a
support-free denominator precision plus a displayed exponent linear in `s`
and `L`.

This remains a finite fixed-spacing estimate.  It does not identify a
continuum Hamiltonian or prove the Clay mass-gap statement.
-/

import YMGap.Continuum.BF4ExactSlabCovarianceAmplitudeDyadicScale
import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorTail
import YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetGeometricConvolution

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorDyadicScale

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabCovarianceAmplitudeDyadicScale
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePair
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorTail
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinatePath
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairGuardedResponse
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairPathCarrier
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DyadicGeometricCutoff
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.PolynomialGeometricDecay
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetGeometricConvolution
open YMGap.Continuum.Z4LinfGeometricSum

/-- The coordinate decay rate is nonnegative. -/
theorem exteriorCoordinateRate_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1) :
    (0 : Q') ≤ entropyRate 625 (adjustedCoreRate w hd) :=
  Q'.mul_nonneg _ _ (ClusterCount.ofNat_nonneg _)
    (adjustedCoreRate_nonnegative (Q'.le_of_lt hw0) hd)

/-- Geometry-independent singleton base for the fixed eight-link translated
face pair. -/
def fixedCoordinateInsertionAmplitudeBase
    {w : Q'} (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (c b : Q') : Q' :=
  ((c * b + c * b) * probePrefactor w hd 12) *
    Q'.recipPos (1 + -entropyRate 625 (adjustedCoreRate w hd))
      (HKPos.one_sub_pos hs)

/-- Geometry-independent covariance base for the translated local pair. -/
def fixedCoordinateCovarianceAmplitudeBase
    {w : Q'} (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) : Q' :=
  let cap := originalBulkVectorQuadraticJetLocalCap +
    originalBulkVectorQuadraticJetLocalCap
  fixedCoordinateInsertionAmplitudeBase hd hs (cap * cap) (prefixCap w) *
      inverseFaceFloor w hd +
    (cap *
        (fixedCoordinateInsertionAmplitudeBase hd hs cap (prefixCap w) *
          inverseFaceFloor w hd) +
      cap *
        (fixedCoordinateInsertionAmplitudeBase hd hs cap (prefixCap w) *
          inverseFaceFloor w hd))

/-- Fully geometry-independent shell base. -/
def fixedCoordinateCovarianceShellBase
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) : Q' :=
  let rate := entropyRate 625 (adjustedCoreRate w hd)
  let shellRate := entropyRate 16 (rate ^ blockLength rate 4)
  fixedCoordinateCovarianceAmplitudeBase hd hs *
    Q'.recipPos (1 + -shellRate)
      (HKPos.one_sub_pos
        (block_rate_lt_one (exteriorCoordinateRate_nonnegative hw0 hd) hs))

/-- Support-free shell base for the concrete coordinate carrier and translated
pair cap. -/
def coordinateCovarianceShellBase
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (s n leftOffset rightOffset L target : Nat)
    (hroom : originalBulkVectorQuadraticJetExtent s n L ≤ target)
    (leftFace rightFace : Z4Plaq) : Q' :=
  let placement := zeroPlacement s n L target hroom
  let rate := entropyRate 625 (adjustedCoreRate w hd)
  let shellRate := entropyRate 16 (rate ^ blockLength rate 4)
  covarianceShellBase
    (left := translatedOriginalBulkVectorQuadraticJetFacePairLinks
      placement n leftOffset rightOffset leftFace rightFace)
    w hd hs
    (translatedOriginalBulkVectorQuadraticJetFacePairCap
      n leftOffset rightOffset leftFace rightFace)
    shellRate
    (block_rate_lt_one (exteriorCoordinateRate_nonnegative hw0 hd) hs)

/-- The apparently geometry-indexed shell base is exactly the fixed local
coefficient: both translated faces contribute four links and the same local
cap. -/
theorem coordinateCovarianceShellBase_eq_fixed
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (s n leftOffset rightOffset L target : Nat)
    (hroom : originalBulkVectorQuadraticJetExtent s n L ≤ target)
    (leftFace rightFace : Z4Plaq) :
    coordinateCovarianceShellBase hw0 hd hs s n leftOffset rightOffset L
        target hroom leftFace rightFace =
      fixedCoordinateCovarianceShellBase hw0 hd hs := by
  unfold coordinateCovarianceShellBase fixedCoordinateCovarianceShellBase
    fixedCoordinateCovarianceAmplitudeBase
    fixedCoordinateInsertionAmplitudeBase covarianceShellBase
    covarianceAmplitudeBase insertionAmplitudeBase
    translatedOriginalBulkVectorQuadraticJetFacePairCap
    translatedOriginalBulkVectorQuadraticJetFacePairLinks
  simp only [List.length_append, edgesOf, List.length_cons, List.length_nil,
    originalBulkVectorQuadraticJetFaceCap_eq_localCap]

/-- The concrete coordinate exterior cutoff has only linear carrier-size cost
outside its support-free denominator precision. -/
theorem coordinateExteriorCovarianceBlockCutoff_le_linearScale
    {w epsilon : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (s n leftOffset rightOffset L target : Nat)
    (hroom : originalBulkVectorQuadraticJetExtent s n L ≤ target)
    (leftFace rightFace : Z4Plaq)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hrightFace : rightFace ∈ bulkSourceFaces s)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L)
    (hepsilon : (0 : Q') < epsilon) :
    coordinateExteriorCovarianceBlockCutoff hw0 hd hs s n leftOffset
        rightOffset L target hroom leftFace rightFace epsilon ≤
      blockLength
          (entropyRate 16
            ((entropyRate 625 (adjustedCoreRate w hd)) ^
              blockLength (entropyRate 625 (adjustedCoreRate w hd)) 4)) 0 *
        (denominatorBitPrecision
            (HKConv.divPos epsilon
              (1 + coordinateCovarianceShellBase hw0 hd hs s n leftOffset
                rightOffset L target hroom leftFace rightFace)) +
          (15 * (5 * s + 3 * L + 5) +
            4 * blockLength (entropyRate 625 (adjustedCoreRate w hd)) 4 + 26)) := by
  let placement := zeroPlacement s n L target hroom
  let carrier :=
    translatedOriginalBulkVectorQuadraticJetFacePairCoordinateCarrier
      placement n leftOffset rightOffset leftFace rightFace
  let cap := translatedOriginalBulkVectorQuadraticJetFacePairCap
    n leftOffset rightOffset leftFace rightFace
  let rate := entropyRate 625 (adjustedCoreRate w hd)
  have hrate : (0 : Q') ≤ rate := exteriorCoordinateRate_nonnegative hw0 hd
  have hcap : (0 : Q') ≤ cap := by
    exact (translatedOriginalBulkVectorQuadraticJetFacePair_left_interval
      placement s n leftOffset rightOffset L leftFace rightFace rfl
      hleftFace hrightFace hleftOffset hrightOffset).nonnegative
  have hsupport : carrier.animal.support.length ≤ 5 * s + 3 * L + 5 :=
    translatedOriginalBulkVectorQuadraticJetFacePairCoordinateCarrier_support_length_le
      placement s n leftOffset rightOffset L leftFace rightFace
      hleftFace hrightFace hleftOffset hrightOffset
  have hcutoff := dyadicBlockCutoff_le_supportUpperBound carrier hw0 hd hs
    hrate hs hcap hepsilon (5 * s + 3 * L + 5) hsupport
  simpa only [coordinateExteriorCovarianceBlockCutoff, coordinateCovarianceShellBase,
    placement, carrier, cap, rate] using hcutoff

/-- Final coordinate form: the denominator precision is independent of all
carrier geometry, while the remaining exponent is explicitly linear in `s`
and `L`. -/
theorem coordinateExteriorCovarianceBlockCutoff_le_fixedLinearScale
    {w epsilon : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (s n leftOffset rightOffset L target : Nat)
    (hroom : originalBulkVectorQuadraticJetExtent s n L ≤ target)
    (leftFace rightFace : Z4Plaq)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hrightFace : rightFace ∈ bulkSourceFaces s)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L)
    (hepsilon : (0 : Q') < epsilon) :
    coordinateExteriorCovarianceBlockCutoff hw0 hd hs s n leftOffset
        rightOffset L target hroom leftFace rightFace epsilon ≤
      blockLength
          (entropyRate 16
            ((entropyRate 625 (adjustedCoreRate w hd)) ^
              blockLength (entropyRate 625 (adjustedCoreRate w hd)) 4)) 0 *
        (denominatorBitPrecision
            (HKConv.divPos epsilon
              (1 + fixedCoordinateCovarianceShellBase hw0 hd hs)) +
          (15 * (5 * s + 3 * L + 5) +
            4 * blockLength (entropyRate 625 (adjustedCoreRate w hd)) 4 + 26)) := by
  simpa only [coordinateCovarianceShellBase_eq_fixed] using
    coordinateExteriorCovarianceBlockCutoff_le_linearScale hw0 hd hs s n
      leftOffset rightOffset L target hroom leftFace rightFace hleftFace
      hrightFace hleftOffset hrightOffset hepsilon

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorDyadicScale

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorDyadicScale.exteriorCoordinateRate_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorDyadicScale.fixedCoordinateCovarianceShellBase
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorDyadicScale.coordinateCovarianceShellBase
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorDyadicScale.coordinateCovarianceShellBase_eq_fixed
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorDyadicScale.coordinateExteriorCovarianceBlockCutoff_le_linearScale
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorDyadicScale.coordinateExteriorCovarianceBlockCutoff_le_fixedLinearScale
