/-
M4t -- combine the exact physical mass and nontrivial continuum clustering on
one selected projective/Wilson object.

The preceding reductions deliberately keep rate reconstruction, bounded
Wilson dynamics, projective correlation semantics, and spectral nontriviality
separate.  This endpoint packages their same-object composition.  Its mass is
the positive exact logarithmic rate of the very separator whose square is the
clustering ratio.

This is a conditional continuum endpoint.  It does not construct its
projective measure, Wilson dynamics, or correlation pin, and it is not a
Wightman/Clay closure theorem.
-/

import YMGap.Continuum.ContinuumSquaredClusteringHandoff
import YMGap.Continuum.RCStrictPositivity

namespace YMGap.Continuum.ContinuumMassClusteringEndpoint

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.ContinuumSquaredClusteringHandoff
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.MeasureLinkedOSReconstruction
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorContinuumRealization
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.ProjectiveOSCorrelationHandoff
open YMGap.Continuum.ProjectiveWilsonConnectedDecayHandoff
open YMGap.Continuum.RCStrictPositivity
open YMGap.Continuum.TuranPositivity
open YMGap.Continuum.WilsonIteratedNormDecayHandoff
open YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff

/-- One same-object continuum endpoint carrying a positive exact logarithmic
mass and a nonzero projective connected correlator with geometric decay. -/
structure ContinuumMassClusteringEndpoint
    {P : PhysicalSeparator}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {A : PhysicalSpacing}
    {sampling : PhysicalSeparationSampling A}
    (W : WilsonSelectedOSGNSData H)
    (B : ProjectiveOSCorrelationHandoff P H W.measureLinked sampling) : Type 2 where
  iteratedGap : WilsonIteratedBoundedMassGap W
  correlationPin : ProjectiveWilsonOSMatrixCoefficientPin B W
  spectralChannel :
    ProjectiveOSCorrelationHandoff.ReconstructionSpectralChannelHandoff
      B W.reconstruction

namespace ContinuumMassClusteringEndpoint

/-- The cutoff-removed physical mass attached to the selected Wilson
separator. -/
def massRate
    {P : PhysicalSeparator}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {A : PhysicalSpacing}
    {sampling : PhysicalSeparationSampling A}
    {W : WilsonSelectedOSGNSData H}
    {B : ProjectiveOSCorrelationHandoff P H W.measureLinked sampling}
    (E : ContinuumMassClusteringEndpoint W B) : CReal :=
  E.iteratedGap.boundedGap.rate

/-- The exact physical mass has a constructive positive rational margin. -/
theorem massRate_posEv
    {P : PhysicalSeparator}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {A : PhysicalSpacing}
    {sampling : PhysicalSeparationSampling A}
    {W : WilsonSelectedOSGNSData H}
    {B : ProjectiveOSCorrelationHandoff P H W.measureLinked sampling}
    (E : ContinuumMassClusteringEndpoint W B) : PosEv E.massRate :=
  E.iteratedGap.rate_posEv

/-- The same exact mass in the representation-invariant completed-real
currency used by the Wilson Hilbert-space and clustering layers. -/
def massRC
    {P : PhysicalSeparator}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {A : PhysicalSpacing}
    {sampling : PhysicalSeparationSampling A}
    {W : WilsonSelectedOSGNSData H}
    {B : ProjectiveOSCorrelationHandoff P H W.measureLinked sampling}
    (E : ContinuumMassClusteringEndpoint W B) : RC :=
  Quotient.mk crealSetoid E.massRate

/-- Representation-invariant strict positivity of the exact physical mass. -/
theorem massRC_isPositive
    {P : PhysicalSeparator}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {A : PhysicalSpacing}
    {sampling : PhysicalSeparationSampling A}
    {W : WilsonSelectedOSGNSData H}
    {B : ProjectiveOSCorrelationHandoff P H W.measureLinked sampling}
    (E : ContinuumMassClusteringEndpoint W B) : RCIsPositive E.massRC :=
  (rcIsPositive_mk_iff_posEv E.massRate).2 E.massRate_posEv

/-- Package the representation-invariant positive mass as Type-level data. -/
def positiveMassRC
    {P : PhysicalSeparator}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {A : PhysicalSpacing}
    {sampling : PhysicalSeparationSampling A}
    {W : WilsonSelectedOSGNSData H}
    {B : ProjectiveOSCorrelationHandoff P H W.measureLinked sampling}
    (E : ContinuumMassClusteringEndpoint W B) : PositiveRC where
  value := E.massRC
  isPositive := E.massRC_isPositive

/-- A canonical raw `CReal` representative of the same physical mass, chosen
as the reconstruction's computed exact logarithm.  Unlike an arbitrary
cutoff-limit representative, this canonical logarithm already carries the
repository's one-slack `CReal.IsPositive` witness. -/
def canonicalPositiveMass
    {P : PhysicalSeparator}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {A : PhysicalSpacing}
    {sampling : PhysicalSeparationSampling A}
    {W : WilsonSelectedOSGNSData H}
    {B : ProjectiveOSCorrelationHandoff P H W.measureLinked sampling}
    (E : ContinuumMassClusteringEndpoint W B) :
    Σ' mass : CReal, CReal.IsPositive mass :=
  ⟨OSExactLogGap.exactLogGap W.reconstruction
      E.iteratedGap.boundedGap.exactRate.exactGap.positiveGapBound,
    E.iteratedGap.boundedGap.exactRate.exactGap.reconstructedRate_isPositive⟩

/-- The mass is the reconstruction's exact logarithm of the same separator
used by the selected Wilson transfer. -/
theorem massRate_equiv_selectedSeparatorExactLog
    {P : PhysicalSeparator}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {A : PhysicalSpacing}
    {sampling : PhysicalSeparationSampling A}
    {W : WilsonSelectedOSGNSData H}
    {B : ProjectiveOSCorrelationHandoff P H W.measureLinked sampling}
    (E : ContinuumMassClusteringEndpoint W B) :
    CReal.Equiv E.massRate
      (OSExactLogGap.exactLogGap W.reconstruction
        E.iteratedGap.boundedGap.exactRate.exactGap.positiveGapBound) :=
  E.iteratedGap.boundedGap.rate_equiv_selectedSeparatorExactLog

/-- In the completed-real quotient, the physical mass is literally the
reconstruction's exact logarithm of the selected separator. -/
theorem massRC_eq_selectedSeparatorExactLogRC
    {P : PhysicalSeparator}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {A : PhysicalSpacing}
    {sampling : PhysicalSeparationSampling A}
    {W : WilsonSelectedOSGNSData H}
    {B : ProjectiveOSCorrelationHandoff P H W.measureLinked sampling}
    (E : ContinuumMassClusteringEndpoint W B) :
    E.massRC =
      Quotient.mk crealSetoid
        (OSExactLogGap.exactLogGap W.reconstruction
          E.iteratedGap.boundedGap.exactRate.exactGap.positiveGapBound) :=
  Quotient.sound E.massRate_equiv_selectedSeparatorExactLog

/-- The quotient of the canonical positive representative is exactly the
endpoint's cutoff-removed physical mass. -/
theorem massRC_eq_canonicalPositiveMassRC
    {P : PhysicalSeparator}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {A : PhysicalSpacing}
    {sampling : PhysicalSeparationSampling A}
    {W : WilsonSelectedOSGNSData H}
    {B : ProjectiveOSCorrelationHandoff P H W.measureLinked sampling}
    (E : ContinuumMassClusteringEndpoint W B) :
    E.massRC = Quotient.mk crealSetoid E.canonicalPositiveMass.1 :=
  E.massRC_eq_selectedSeparatorExactLogRC

/-- The selected physical continuum gap channel is nonzero and geometrically
clustered in the constructive-real squared sense. -/
def nontrivialClustering
    {P : PhysicalSeparator}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {A : PhysicalSpacing}
    {sampling : PhysicalSeparationSampling A}
    {W : WilsonSelectedOSGNSData H}
    {B : ProjectiveOSCorrelationHandoff P H W.measureLinked sampling}
    (E : ContinuumMassClusteringEndpoint W B) :
    NontrivialRCSquaredGeometricClustering
      E.correlationPin.continuumGapCorrRC :=
  ContinuumSquaredClusteringHandoff.ProjectiveWilsonOSMatrixCoefficientPin.continuumNontrivialSquaredGeometricClustering
    E.correlationPin E.iteratedGap E.spectralChannel

/-- The clustering ratio is definitionally the square of the same selected
separator whose exact logarithm is the physical mass. -/
theorem clusteringRatio_eq_selectedSeparatorSq
    {P : PhysicalSeparator}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {A : PhysicalSpacing}
    {sampling : PhysicalSeparationSampling A}
    {W : WilsonSelectedOSGNSData H}
    {B : ProjectiveOSCorrelationHandoff P H W.measureLinked sampling}
    (E : ContinuumMassClusteringEndpoint W B) :
    E.nontrivialClustering.ratio =
      W.selectedSpectralData.gap.sep * W.selectedSpectralData.gap.sep :=
  rfl

end ContinuumMassClusteringEndpoint

end YMGap.Continuum.ContinuumMassClusteringEndpoint

#print axioms YMGap.Continuum.ContinuumMassClusteringEndpoint.ContinuumMassClusteringEndpoint.massRate_posEv
#print axioms YMGap.Continuum.ContinuumMassClusteringEndpoint.ContinuumMassClusteringEndpoint.massRC_isPositive
#print axioms YMGap.Continuum.ContinuumMassClusteringEndpoint.ContinuumMassClusteringEndpoint.positiveMassRC
#print axioms YMGap.Continuum.ContinuumMassClusteringEndpoint.ContinuumMassClusteringEndpoint.canonicalPositiveMass
#print axioms YMGap.Continuum.ContinuumMassClusteringEndpoint.ContinuumMassClusteringEndpoint.massRate_equiv_selectedSeparatorExactLog
#print axioms YMGap.Continuum.ContinuumMassClusteringEndpoint.ContinuumMassClusteringEndpoint.massRC_eq_selectedSeparatorExactLogRC
#print axioms YMGap.Continuum.ContinuumMassClusteringEndpoint.ContinuumMassClusteringEndpoint.massRC_eq_canonicalPositiveMassRC
#print axioms YMGap.Continuum.ContinuumMassClusteringEndpoint.ContinuumMassClusteringEndpoint.nontrivialClustering
#print axioms YMGap.Continuum.ContinuumMassClusteringEndpoint.ContinuumMassClusteringEndpoint.clusteringRatio_eq_selectedSeparatorSq
