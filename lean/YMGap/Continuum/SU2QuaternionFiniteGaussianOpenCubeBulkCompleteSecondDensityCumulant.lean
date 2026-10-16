/-
# Complete finite second-density connected insertion

The second coefficient of the finite FREE density is

  V3^2/2 - V4_spatial - V4_kinetic + J2.

The four component insertions are already checked on the SAME rooted-comb /
Heron history carrier.  This leaf supplies the missing literal signed
assembly.  Spatial fourth-action terms range over every internal face on
every history slice; kinetic fourth-action terms range over every forward
temporal bond and comb-gauge edge; Cayley-Haar terms range over every history
slice and comb-gauge edge; and the TOTAL cubic half-square retains every
ordered cross-face and cross-time pair.

This is still only the connected third cumulant of two finite FREE source
quadratics with the complete reference second-density coefficient.  OWN
normalization, supplied OLD-center mean-residual products, the ORIGINAL
gauge-reduced law, higher remainders, a uniform signed estimate and the
continuum/Clay conclusions remain outside this theorem.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialCubicPairCumulant
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkKineticHeatActionCumulant
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyHaarCumulant

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCompleteSecondDensityCumulant

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoFourCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianThirdCumulantTrilinear
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianInternalOpenCubeIncidence
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialHeatActionCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkKineticHeatActionCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyHaarCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialCubicPairCumulant

local infix:50 " ≈ " => Q'.eqv

/-- Canonical complete spatial fourth-action list: every internal spatial
face on every history slice, including both terminal slices. -/
def completeOpenCubeSpatialHeatActionFourthInsertions
    (timeBonds width : Nat) :
    List OpenCubeSpatialHeatActionFourthInsertion :=
  (List.range (timeBonds + 1)).flatMap fun time =>
    (internalOpenCubeFaces width).map fun face =>
      { weight := 1
        time := time
        face := face }

/-- Complete finite spatial fourth-action polynomial. -/
def completeOpenCubeSpatialHeatActionFourthPolynomial
    (timeBonds width stage : Nat) : RatPoly :=
  openCubeSpatialHeatActionFourthInsertionPolynomial
    timeBonds width stage
    (completeOpenCubeSpatialHeatActionFourthInsertions timeBonds width)

/-- Complete finite kinetic fourth-action polynomial. -/
def completeOpenCubeKineticFourthActionPolynomial
    (timeBonds width stage : Nat) : RatPoly :=
  openCubeKineticFourthActionInsertionPolynomial
    timeBonds width stage
    (completeOpenCubeKineticFourthActionInsertions timeBonds width)

/-- Complete finite product-Cayley-chart Haar `J2` polynomial. -/
def completeOpenCubeCayleyHaarJ2Polynomial
    (timeBonds width stage : Nat) : RatPoly :=
  openCubeCayleyHaarJ2InsertionPolynomial
    timeBonds width stage
    (completeOpenCubeCayleyHaarJ2Insertions timeBonds width)

/-- Literal complete second coefficient of the finite FREE density.  The two
fourth-action families enter with the density sign `-V4`; `J2` already
contains its local negative Cayley-Jacobian coefficient. -/
def completeOpenCubeSecondDensityPolynomial
    (timeBonds width stage : Nat) : RatPoly :=
  polyAdd
    (completeOpenCubeSpatialCubicPairPolynomial timeBonds width stage)
    (polyAdd
      (polySmul (-1)
        (completeOpenCubeSpatialHeatActionFourthPolynomial
          timeBonds width stage))
      (polyAdd
        (polySmul (-1)
          (completeOpenCubeKineticFourthActionPolynomial
            timeBonds width stage))
        (completeOpenCubeCayleyHaarJ2Polynomial
          timeBonds width stage)))

/-- Exact assembled connected value of the complete finite FREE
second-density coefficient. -/
def openCubeBulkCompleteSecondDensityWickSum
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime : Nat) : Q' :=
  openCubeBulkCompleteSpatialCubicPairWickSum
      timeBonds s hs stage leftTime rightTime +
    ((-1) *
      openCubeBulkPlaquetteSpatialHeatActionFourthFamilyWickSum
        timeBonds s hs stage leftTime rightTime
        (completeOpenCubeSpatialHeatActionFourthInsertions
          timeBonds (bulkSourceWidth s)) +
      ((-1) *
        openCubeBulkKineticFourthActionFamilyWickSum
          timeBonds s hs stage leftTime rightTime
          (completeOpenCubeKineticFourthActionInsertions
            timeBonds (bulkSourceWidth s)) +
        openCubeBulkCayleyHaarJ2FamilyTriangleSum
          timeBonds s hs stage leftTime rightTime
          (completeOpenCubeCayleyHaarJ2Insertions
            timeBonds (bulkSourceWidth s))))

/-- Exact common-carrier signed assembly of `V3^2/2-V4+J2` against the two
OLD-centered finite bulk-source quadratics.  Center cancellation here does
not supply the separate OWN/OLD mean-residual terms of the full response. -/
theorem finiteGaussianThirdCumulant_openCube_bulk_old_centered_completeSecondDensity_wick
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime : Nat)
    (leftOldCenter rightOldCenter : Q') :
    finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds s)
        (finiteGaussianCenteredPolynomial leftOldCenter
          (bulkSourceHeronRadialSquare timeBonds s hs stage leftTime))
        (finiteGaussianCenteredPolynomial rightOldCenter
          (bulkSourceHeronRadialSquare timeBonds s hs stage rightTime))
        (completeOpenCubeSecondDensityPolynomial
          timeBonds (bulkSourceWidth s) stage) ≈
      openCubeBulkCompleteSecondDensityWickSum
        timeBonds s hs stage leftTime rightTime := by
  let N := bulkSourceNoiseCount timeBonds s
  let left := finiteGaussianCenteredPolynomial leftOldCenter
    (bulkSourceHeronRadialSquare timeBonds s hs stage leftTime)
  let right := finiteGaussianCenteredPolynomial rightOldCenter
    (bulkSourceHeronRadialSquare timeBonds s hs stage rightTime)
  let cubic := completeOpenCubeSpatialCubicPairPolynomial
    timeBonds (bulkSourceWidth s) stage
  let spatial := completeOpenCubeSpatialHeatActionFourthPolynomial
    timeBonds (bulkSourceWidth s) stage
  let kinetic := completeOpenCubeKineticFourthActionPolynomial
    timeBonds (bulkSourceWidth s) stage
  let haar := completeOpenCubeCayleyHaarJ2Polynomial
    timeBonds (bulkSourceWidth s) stage
  let spatialInsertions := completeOpenCubeSpatialHeatActionFourthInsertions
    timeBonds (bulkSourceWidth s)
  let kineticInsertions := completeOpenCubeKineticFourthActionInsertions
    timeBonds (bulkSourceWidth s)
  let haarInsertions := completeOpenCubeCayleyHaarJ2Insertions
    timeBonds (bulkSourceWidth s)
  have hcubic : finiteGaussianThirdCumulant N left right cubic ≈
      openCubeBulkCompleteSpatialCubicPairWickSum
        timeBonds s hs stage leftTime rightTime :=
    finiteGaussianThirdCumulant_openCube_bulk_old_centered_completeSpatialCubicPair_wick
      timeBonds s hs stage leftTime rightTime leftOldCenter rightOldCenter
  have hspatialBase : finiteGaussianThirdCumulant N left right spatial ≈
      openCubeBulkPlaquetteSpatialHeatActionFourthFamilyWickSum
        timeBonds s hs stage leftTime rightTime spatialInsertions := by
    exact finiteGaussianThirdCumulant_openCube_bulk_old_centered_spatialHeatActionFourth_family_wick
      timeBonds s hs stage leftTime rightTime leftOldCenter rightOldCenter
      spatialInsertions
  have hspatial : finiteGaussianThirdCumulant N left right
        (polySmul (-1) spatial) ≈
      (-1) * openCubeBulkPlaquetteSpatialHeatActionFourthFamilyWickSum
        timeBonds s hs stage leftTime rightTime spatialInsertions :=
    Q'.eqv_trans _ _ _
      (finiteGaussianThirdCumulant_smul_right N (-1) left right spatial)
      (Q'.mul_eqv_congr_left (-1) _ _ hspatialBase)
  have hkineticBase : finiteGaussianThirdCumulant N left right kinetic ≈
      openCubeBulkKineticFourthActionFamilyWickSum
        timeBonds s hs stage leftTime rightTime kineticInsertions := by
    exact finiteGaussianThirdCumulant_openCube_bulk_old_centered_completeKineticFourthAction_wick
      timeBonds s hs stage leftTime rightTime leftOldCenter rightOldCenter
  have hkinetic : finiteGaussianThirdCumulant N left right
        (polySmul (-1) kinetic) ≈
      (-1) * openCubeBulkKineticFourthActionFamilyWickSum
        timeBonds s hs stage leftTime rightTime kineticInsertions :=
    Q'.eqv_trans _ _ _
      (finiteGaussianThirdCumulant_smul_right N (-1) left right kinetic)
      (Q'.mul_eqv_congr_left (-1) _ _ hkineticBase)
  have hhaar : finiteGaussianThirdCumulant N left right haar ≈
      openCubeBulkCayleyHaarJ2FamilyTriangleSum
        timeBonds s hs stage leftTime rightTime haarInsertions := by
    exact finiteGaussianThirdCumulant_openCube_bulk_old_centered_completeCayleyHaarJ2_triangle
      timeBonds s hs stage leftTime rightTime leftOldCenter rightOldCenter
  have hsplitCubic := finiteGaussianThirdCumulant_add_right
    N left right cubic
      (polyAdd (polySmul (-1) spatial)
        (polyAdd (polySmul (-1) kinetic) haar))
  have hsplitSpatial := finiteGaussianThirdCumulant_add_right
    N left right (polySmul (-1) spatial)
      (polyAdd (polySmul (-1) kinetic) haar)
  have hsplitKinetic := finiteGaussianThirdCumulant_add_right
    N left right (polySmul (-1) kinetic) haar
  unfold completeOpenCubeSecondDensityPolynomial
    openCubeBulkCompleteSecondDensityWickSum
  exact Q'.eqv_trans _ _ _ hsplitCubic
    (Q'.add_eqv_congr' hcubic
      (Q'.eqv_trans _ _ _ hsplitSpatial
        (Q'.add_eqv_congr' hspatial
          (Q'.eqv_trans _ _ _ hsplitKinetic
            (Q'.add_eqv_congr' hkinetic hhaar)))))

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCompleteSecondDensityCumulant

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCompleteSecondDensityCumulant.finiteGaussianThirdCumulant_openCube_bulk_old_centered_completeSecondDensity_wick
