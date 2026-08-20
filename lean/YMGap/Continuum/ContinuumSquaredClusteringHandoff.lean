/-
M4s -- package the projective/Wilson decay theorem as a faithful constructive
continuum clustering interface.

The projective-to-Wilson handoff proves a squared bound in the completed-real
quotient.  This module records exactly that notion of geometric clustering,
including a ratio strictly below one.  When the already-separated
reconstruction spectral channel is supplied, its positive time-zero weight
also makes the clustering witness nontrivial.

No continuum correlator, spectral channel, or Wilson identification is
constructed here.
-/

import YMGap.Continuum.ProjectiveWilsonConnectedDecayHandoff

namespace YMGap.Continuum.ContinuumSquaredClusteringHandoff

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.MeasureLinkedOSReconstruction
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorContinuumRealization
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.ProjectiveOSCorrelationHandoff
open YMGap.Continuum.ProjectiveWilsonConnectedDecayHandoff
open YMGap.Continuum.WilsonIteratedNormDecayHandoff
open YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff

/-- A constructive-real connected correlator has squared geometric clustering
with a nonnegative amplitude and a rational ratio strictly below one. -/
structure RCSquaredGeometricClustering (corr : Nat -> RC) : Type 1 where
  amplitude : RC
  ratio : Q'
  amplitude_nonneg : RCnonneg amplitude
  ratio_nonneg : (0 : Q') <= ratio
  ratio_lt_one : ratio < (1 : Q')
  decay : forall n : Nat,
    RCle
      (RCmul (corr n) (corr n))
      (RCmul (RCscale (ratio ^ n) amplitude) amplitude)

/-- The clustering channel is nontrivial when its time-zero value dominates a
strictly positive rational floor. -/
structure NontrivialRCSquaredGeometricClustering
    (corr : Nat -> RC) : Type 1 extends RCSquaredGeometricClustering corr where
  zeroFloor : Q'
  zeroFloor_pos : (0 : Q') < zeroFloor
  zeroFloor_le : RCle
    (Quotient.mk crealSetoid (CReal.ofQ' zeroFloor))
    (corr 0)

namespace ProjectiveWilsonOSMatrixCoefficientPin

/-- The projective continuum gap correlator satisfies the constructive-real
squared clustering contract. -/
def continuumSquaredGeometricClustering
    {P : PhysicalSeparator}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {L : MeasureLinkedOSGNSData H}
    {A : PhysicalSpacing}
    {sampling : PhysicalSeparationSampling A}
    {B : ProjectiveOSCorrelationHandoff P H L sampling}
    {W : WilsonSelectedOSGNSData H}
    (C : ProjectiveWilsonOSMatrixCoefficientPin B W)
    (G : WilsonIteratedBoundedMassGap W) :
    RCSquaredGeometricClustering C.continuumGapCorrRC where
  amplitude := W.wilson.toGNSData.gnsComplete.hilbert.cinner
    C.gapState C.gapState
  ratio := W.selectedSpectralData.gap.sep *
    W.selectedSpectralData.gap.sep
  amplitude_nonneg := W.wilson.toGNSData.cinner_self_nonneg C.gapState
  ratio_nonneg := Q'.mul_nonneg _ _
    W.selectedSpectralData.gap.sep_nonneg
    W.selectedSpectralData.gap.sep_nonneg
  ratio_lt_one := by
    have hstep :
        W.selectedSpectralData.gap.sep *
            W.selectedSpectralData.gap.sep <=
          W.selectedSpectralData.gap.sep * (1 : Q') :=
      Q'.mul_le_mul_of_nonneg_left _ _ _
        (Q'.le_of_lt W.selectedSpectralData.gap.sep_lt_one)
        W.selectedSpectralData.gap.sep_nonneg
    exact Q'.lt_of_le_of_lt
      (Q'.le_trans' _ _ _ hstep
        (Q'.le_of_eqv
          (Q'.mul_one_eqv W.selectedSpectralData.gap.sep)))
      W.selectedSpectralData.gap.sep_lt_one
  decay := C.continuumGapCorrelationSqDecay G

/-- The positive reconstructed time-zero channel upgrades the same clustering
witness to a nonvacuous one. -/
def continuumNontrivialSquaredGeometricClustering
    {P : PhysicalSeparator}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {L : MeasureLinkedOSGNSData H}
    {A : PhysicalSpacing}
    {sampling : PhysicalSeparationSampling A}
    {B : ProjectiveOSCorrelationHandoff P H L sampling}
    {W : WilsonSelectedOSGNSData H}
    (C : ProjectiveWilsonOSMatrixCoefficientPin B W)
    (G : WilsonIteratedBoundedMassGap W)
    (S : ProjectiveOSCorrelationHandoff.ReconstructionSpectralChannelHandoff
      B L.reconstruction) :
    NontrivialRCSquaredGeometricClustering C.continuumGapCorrRC where
  toRCSquaredGeometricClustering :=
    ContinuumSquaredClusteringHandoff.ProjectiveWilsonOSMatrixCoefficientPin.continuumSquaredGeometricClustering
      C G
  zeroFloor := SpectralGap.corr L.reconstruction.spec 0
  zeroFloor_pos := S.spectralCorrZero_pos
  zeroFloor_le := by
    have heq : C.continuumGapCorrRC 0 =
        (Quotient.mk crealSetoid
          (CReal.ofQ' (SpectralGap.corr L.reconstruction.spec 0)) : RC) := by
      apply Quotient.sound
      exact S.spectralCorr_eq 0
    rw [heq]
    exact RCle_refl _

end ProjectiveWilsonOSMatrixCoefficientPin

end YMGap.Continuum.ContinuumSquaredClusteringHandoff

#print axioms YMGap.Continuum.ContinuumSquaredClusteringHandoff.ProjectiveWilsonOSMatrixCoefficientPin.continuumSquaredGeometricClustering
#print axioms YMGap.Continuum.ContinuumSquaredClusteringHandoff.ProjectiveWilsonOSMatrixCoefficientPin.continuumNontrivialSquaredGeometricClustering
