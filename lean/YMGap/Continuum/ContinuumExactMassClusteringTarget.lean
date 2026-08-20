/-
M4v -- bundle the selected-channel exact-mass/clustering endpoint as an honest
continuum target.

This target existentially packages the objects that were parameters of
`ContinuumMassClusteringEndpoint`: one continuum measure, its full
`ContinuumYMExistence` datum, a physical separator and sampling, a selected
same-measure Wilson dynamics, and the projective correlation handoff.

An inhabitant yields both currencies without conflating them:

* a canonical positive exact physical mass `-log(separator)` together with
  nontrivial squared clustering of the selected continuum channel; and
* the legacy dimensionless margin-valued `ContinuumYMWithGap` projection.

The structure is not inhabited here.  In particular it does not construct the
continuum Yang--Mills existence datum, Wilson dynamics, or projective/Wilson
pins, and it does not supply the additional uniform-in-coupling and corrected
same-action target data needed for Clay closure.
-/

import YMGap.Continuum.ContinuumMassClusteringEndpoint
import YMGap.Continuum.OSCanonicalMarginGap

namespace YMGap.Continuum.ContinuumExactMassClusteringTarget

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.ContinuumMassClusteringEndpoint
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.ContinuumSquaredClusteringHandoff
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.MeasureLinkedOSReconstruction
open YMGap.Continuum.OSCanonicalMarginGap
open YMGap.Continuum.OSExactLogGap
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorContinuumRealization
open YMGap.Continuum.ProjectiveOSCorrelationHandoff
open YMGap.Continuum.RCStrictPositivity
open YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff

/-- One bundled continuum theory with a same-object exact physical mass and a
nontrivial selected clustering channel.  Every analytic object is explicit
data; this declaration supplies no inhabitant. -/
structure ContinuumExactMassClusteringTarget
    {M : Nat -> Type} (mu : ContinuumMeasure M) : Type 3 where
  existence : ContinuumYMExistence mu
  separator : PhysicalSeparator
  physicalSpacing :
    YMGap.Continuum.PhysicalSeparatorLogRate.PhysicalSpacing
  sampling : PhysicalSeparationSampling physicalSpacing
  wilson : WilsonSelectedOSGNSData existence
  projective : ProjectiveOSCorrelationHandoff separator existence
    wilson.measureLinked sampling
  endpoint : ContinuumMassClusteringEndpoint wilson projective

namespace ContinuumExactMassClusteringTarget

/-- The canonical positive raw representative of the exact physical mass. -/
def canonicalPositiveMass
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumExactMassClusteringTarget mu) :
    Σ' mass : CReal, CReal.IsPositive mass :=
  T.endpoint.canonicalPositiveMass

/-- The representation-invariant positive exact mass in the completed-real
currency shared by the Wilson Hilbert and clustering layers. -/
def positiveMassRC
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumExactMassClusteringTarget mu) : PositiveRC :=
  T.endpoint.positiveMassRC

/-- The selected continuum channel is nonzero and squared-geometrically
clustered. -/
def nontrivialClustering
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumExactMassClusteringTarget mu) :
    NontrivialRCSquaredGeometricClustering
      T.endpoint.correlationPin.continuumGapCorrRC :=
  T.endpoint.nontrivialClustering

/-- The quotient exact mass is the quotient of the canonical positive
`-log(separator)` representative. -/
theorem massRC_eq_canonicalPositiveMassRC
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumExactMassClusteringTarget mu) :
    T.positiveMassRC.value =
      Quotient.mk crealSetoid T.canonicalPositiveMass.1 :=
  T.endpoint.massRC_eq_canonicalPositiveMassRC

/-- Project to the legacy continuum endpoint in its correct, distinct
dimensionless margin currency `1 - separator`. -/
def toContinuumYMWithCanonicalMarginGap
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumExactMassClusteringTarget mu) : ContinuumYMWithGap mu :=
  OSCanonicalMarginGap.continuumYMWithCanonicalMarginGap
    T.existence T.wilson.reconstruction

/-- The legacy projection's mass is the canonical transfer margin, not the
exact logarithmic physical mass. -/
theorem legacyMass_eq_canonicalMargin
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumExactMassClusteringTarget mu) :
    T.toContinuumYMWithCanonicalMarginGap.mass =
      canonicalMarginGap T.wilson.reconstruction :=
  rfl

end ContinuumExactMassClusteringTarget

end YMGap.Continuum.ContinuumExactMassClusteringTarget

#print axioms YMGap.Continuum.ContinuumExactMassClusteringTarget.ContinuumExactMassClusteringTarget.canonicalPositiveMass
#print axioms YMGap.Continuum.ContinuumExactMassClusteringTarget.ContinuumExactMassClusteringTarget.positiveMassRC
#print axioms YMGap.Continuum.ContinuumExactMassClusteringTarget.ContinuumExactMassClusteringTarget.nontrivialClustering
#print axioms YMGap.Continuum.ContinuumExactMassClusteringTarget.ContinuumExactMassClusteringTarget.massRC_eq_canonicalPositiveMassRC
#print axioms YMGap.Continuum.ContinuumExactMassClusteringTarget.ContinuumExactMassClusteringTarget.toContinuumYMWithCanonicalMarginGap
#print axioms YMGap.Continuum.ContinuumExactMassClusteringTarget.ContinuumExactMassClusteringTarget.legacyMass_eq_canonicalMargin
