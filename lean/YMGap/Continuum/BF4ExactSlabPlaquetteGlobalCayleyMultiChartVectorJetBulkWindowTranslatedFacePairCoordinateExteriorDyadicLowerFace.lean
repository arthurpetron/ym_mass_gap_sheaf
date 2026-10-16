/-
# Concrete lower-face dyadic schedule

This module instantiates the cofinal coordinate exterior comparison with the
explicit listed lower bulk-source face at every scheduled side.  The two
placed observables may still have distinct time offsets.  No abstract
face-membership trajectory remains in the resulting convergence theorem.

The theorem is still a fixed-nome comparison between two finite-law
presentations.  It does not construct their common thermodynamic or continuum
limit.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorDyadicCofinal

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorDyadicLowerFace

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorDyadicCofinal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.PolynomialGeometricDecay
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource

/-- The explicit lower listed source face at a dyadic scheduled side. -/
def dyadicScheduledLowerFace
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (L stage : Nat) : Z4Plaq :=
  bulkSourceLowerFace (dyadicScheduleSide hw0 hd hs L stage)

theorem dyadicScheduleSide_positive
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (L stage : Nat) :
    0 < dyadicScheduleSide hw0 hd hs L stage := by
  unfold dyadicScheduleSide
  omega

/-- The scheduled lower face is a literal member of every scheduled source
window. -/
theorem dyadicScheduledLowerFace_mem
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (L stage : Nat) :
    dyadicScheduledLowerFace hw0 hd hs L stage ∈
      bulkSourceFaces (dyadicScheduleSide hw0 hd hs L stage) := by
  exact bulkSourceLowerFace_mem _
    (dyadicScheduleSide_positive hw0 hd hs L stage)

/-- Canonical-full minus original-source covariance for the two time-shifted
copies of the scheduled lower face. -/
def dyadicScheduledLowerFaceDifference
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (L leftOffset rightOffset stage : Nat) : CReal :=
  dyadicScheduledDifference hw0 hw1 hd hs L leftOffset rightOffset
    (dyadicScheduledLowerFace hw0 hd hs L)
    (dyadicScheduledLowerFace hw0 hd hs L) stage

/-- The concrete lower-face covariance comparison has the dyadic stage
bound. -/
theorem dyadicScheduledLowerFaceDifference_small
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (L leftOffset rightOffset stage : Nat)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L) :
    leEv
      (CReal.abs (dyadicScheduledLowerFaceDifference hw0 hw1 hd hs L
        leftOffset rightOffset stage))
      (ofQ' (dyadicTolerance stage)) := by
  exact dyadicScheduledDifference_small hw0 hw1 hsmall hd hs L leftOffset
    rightOffset stage hleftOffset hrightOffset
    (dyadicScheduledLowerFace hw0 hd hs L)
    (dyadicScheduledLowerFace hw0 hd hs L)
    (dyadicScheduledLowerFace_mem hw0 hd hs L stage)
    (dyadicScheduledLowerFace_mem hw0 hd hs L stage)

/-- The actual concrete lower-face covariance presentation difference
converges to zero along the explicit cofinal schedule. -/
theorem dyadicScheduledLowerFaceDifference_converges_zero
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (L leftOffset rightOffset : Nat)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L) :
    CReal.ConvergesTo
      (fun stage => dyadicScheduledLowerFaceDifference hw0 hw1 hd hs L
        leftOffset rightOffset stage)
      CReal.czero := by
  exact dyadicScheduledDifference_converges_zero hw0 hw1 hsmall hd hs L
    leftOffset rightOffset hleftOffset hrightOffset
    (dyadicScheduledLowerFace hw0 hd hs L)
    (dyadicScheduledLowerFace hw0 hd hs L)
    (fun stage => dyadicScheduledLowerFace_mem hw0 hd hs L stage)
    (fun stage => dyadicScheduledLowerFace_mem hw0 hd hs L stage)

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorDyadicLowerFace

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorDyadicLowerFace.dyadicScheduledLowerFace_mem
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorDyadicLowerFace.dyadicScheduledLowerFaceDifference_small
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorDyadicLowerFace.dyadicScheduledLowerFaceDifference_converges_zero
