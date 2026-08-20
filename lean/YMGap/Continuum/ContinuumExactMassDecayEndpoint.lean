/-
M4z -- one theorem-facing endpoint for nontrivial continuum clustering at the
exact physical mass.

The scaling-window theorem gives an unsquared exponential bound on the actual
selected continuum correlator.  The earlier projective/Wilson chain separately
gives nontrivial squared clustering.  This module packages both facts with the
positive exact mass and its quotient identity, preventing the exponential
bound from being mistaken for a vacuous statement about a zero channel.

The constructor below consumes a corrected target and its explicit scaling
window.  Neither input is constructed here.
-/

import YMGap.Continuum.ContinuumExactMassScalingWindow

namespace YMGap.Continuum.ContinuumExactMassDecayEndpoint

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ContinuumCorrectedExactMassTarget
open YMGap.Continuum.ContinuumCorrectedExactMassTarget.ContinuumCorrectedExactMassTarget
open YMGap.Continuum.ContinuumExactMassScalingWindow
open YMGap.Continuum.ContinuumExactMassScalingWindow.ExactMassUniformDecayScalingWindow
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.ContinuumSquaredClusteringHandoff
open YMGap.Continuum.ProjectiveWilsonConnectedDecayHandoff
open YMGap.Continuum.RCStrictPositivity
open YMGap.Continuum.UniformCorrelationDecay

/-- A nonzero continuum channel with exponential decay at a positive mass that
is identified in the completed-real quotient with the selected exact physical
mass.  The squared-clustering component records nontriviality independently of
the unsquared bound. -/
structure NontrivialExactMassContinuumClustering
    (corr : Nat -> CReal) : Type 2 where
  rawMass : CReal
  rawMass_pos : CRealPosWitness rawMass
  exactMass : PositiveRC
  rawMass_eq_exactMass :
    Quotient.mk crealSetoid rawMass = exactMass.value
  amplitude : CReal
  amplitude_nonneg : CReal.leEv CReal.czero amplitude
  expData : CReal.ExpNegCData
    (CReal.mul rawMass (CReal.ofQ' (Q'.ofNat 1)))
  exactDecay : forall t : Nat,
    CReal.leEv (CReal.abs (corr (t + 1)))
      (CReal.mul amplitude
        (physEnvelope rawMass (Q'.ofNat 1) expData (t + 1)))
  nontrivialSquared : NontrivialRCSquaredGeometricClustering
    (fun t => Quotient.mk crealSetoid (corr t))

/-- Build the nontrivial exact-mass continuum clustering endpoint from the
corrected same-object target and its explicit scaling-window residual. -/
def ofScalingWindow
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumCorrectedExactMassTarget mu)
    (W : ExactMassUniformDecayScalingWindow T) :
    NontrivialExactMassContinuumClustering
      (fun t => T.exact.projective.continuumCorr
        T.exact.projective.gapObservable t) where
  rawMass := T.uniform.uniformDecay.m
  rawMass_pos := T.uniform.uniformDecay.m_pos
  exactMass := T.positiveMassRC
  rawMass_eq_exactMass := T.uniformMassRC_eq_positiveMassRC
  amplitude := T.uniform.uniformDecay.A
  amplitude_nonneg := T.uniform.uniformDecay.A_nonneg
  expData := T.uniform.uniformDecay.expData (Q'.ofNat 1)
  exactDecay := W.continuumExactMassDecay
  nontrivialSquared := by
    simpa [ProjectiveWilsonOSMatrixCoefficientPin.continuumGapCorrRC] using
      T.nontrivialClustering

end YMGap.Continuum.ContinuumExactMassDecayEndpoint

#print axioms YMGap.Continuum.ContinuumExactMassDecayEndpoint.ofScalingWindow
