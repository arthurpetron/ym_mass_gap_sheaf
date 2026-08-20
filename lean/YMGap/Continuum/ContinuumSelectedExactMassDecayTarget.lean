/-
M4aa -- the selected-theory endpoint after exact-mass scaling transport.

This is the single target consumed by downstream selected-continuum statements:
one corrected same-object target plus its scaling window.  It exposes the full
continuum-existence datum already carried by that target, its reconstruction,
and the nontrivial exact-mass clustering endpoint.

It is deliberately uninhabited.  Moreover, it is a target for one selected
continuum measure; it does not quantify over or pin every compact simple gauge
group, so it is not named or advertised as the final Clay target.
-/

import YMGap.Continuum.ContinuumExactMassDecayEndpoint

namespace YMGap.Continuum.ContinuumSelectedExactMassDecayTarget

open YMGap.Constructive
open YMGap.Continuum.ContinuumCorrectedExactMassTarget
open YMGap.Continuum.ContinuumCorrectedExactMassTarget.ContinuumCorrectedExactMassTarget
open YMGap.Continuum.ContinuumExactMassDecayEndpoint
open YMGap.Continuum.ContinuumExactMassScalingWindow
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.MeasureLinkedOSReconstruction
open YMGap.Continuum.OSReconstruction
open YMGap.Continuum.RCStrictPositivity
open YMGap.Continuum.UniformCorrelationDecay

/-- One selected continuum YM target with full same-object exact-mass decay
data.  No inhabitant is supplied. -/
structure ContinuumSelectedExactMassDecayTarget
    {M : Nat -> Type} (mu : ContinuumMeasure M) : Type 3 where
  corrected : ContinuumCorrectedExactMassTarget mu
  scaling : ExactMassUniformDecayScalingWindow corrected

namespace ContinuumSelectedExactMassDecayTarget

/-- The explicit continuum-existence datum carried by the selected target. -/
def existence
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumSelectedExactMassDecayTarget mu) :
    ContinuumYMExistence mu :=
  T.corrected.exact.existence

/-- The OS reconstruction selected by the same Wilson/projective stack. -/
def reconstruction
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumSelectedExactMassDecayTarget mu) :
    OSReconstruction mu :=
  T.corrected.exact.wilson.reconstruction

/-- The positive quotient-valued exact physical mass. -/
def positiveExactMass
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumSelectedExactMassDecayTarget mu) : PositiveRC :=
  T.corrected.positiveMassRC

/-- The same selected channel has nontrivial continuum exponential clustering
at the quotient-pinned exact physical mass. -/
def nontrivialExactMassClustering
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumSelectedExactMassDecayTarget mu) :
    NontrivialExactMassContinuumClustering
      (fun t => T.corrected.exact.projective.continuumCorr
        T.corrected.exact.projective.gapObservable t) :=
  ofScalingWindow T.corrected T.scaling

/-- Full O(4) restoration is projected from the same selected continuum
existence datum. -/
def fullO4Restoration
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumSelectedExactMassDecayTarget mu) :
    IsO4Restoration mu :=
  T.corrected.fullO4Restoration

/-- Gauge-generation content from the same selected existence datum. -/
def gaugeContent
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumSelectedExactMassDecayTarget mu) :
    IsGaugeGenerated mu :=
  T.existence.gauge_content

/-- UV asymptotic-freedom content from the same selected existence datum. -/
def uvAsymptoticFreedom
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumSelectedExactMassDecayTarget mu) :
    IsUVAsymptoticallyFree mu :=
  T.existence.uv_asymptotic_freedom

/-- Interacting/non-Gaussian content from the same selected existence datum. -/
def interacting
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumSelectedExactMassDecayTarget mu) :
    IsNontrivial mu :=
  T.existence.nontrivial

/-- The selected target still projects to the repository's uniform-decay
mass-gap package; the exact quotient pin is retained by
`nontrivialExactMassClustering`. -/
def uniformMassGap
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumSelectedExactMassDecayTarget mu) : MassGap :=
  T.corrected.uniformMassGap

end ContinuumSelectedExactMassDecayTarget

end YMGap.Continuum.ContinuumSelectedExactMassDecayTarget

#print axioms YMGap.Continuum.ContinuumSelectedExactMassDecayTarget.ContinuumSelectedExactMassDecayTarget.existence
#print axioms YMGap.Continuum.ContinuumSelectedExactMassDecayTarget.ContinuumSelectedExactMassDecayTarget.reconstruction
#print axioms YMGap.Continuum.ContinuumSelectedExactMassDecayTarget.ContinuumSelectedExactMassDecayTarget.positiveExactMass
#print axioms YMGap.Continuum.ContinuumSelectedExactMassDecayTarget.ContinuumSelectedExactMassDecayTarget.nontrivialExactMassClustering
#print axioms YMGap.Continuum.ContinuumSelectedExactMassDecayTarget.ContinuumSelectedExactMassDecayTarget.fullO4Restoration
#print axioms YMGap.Continuum.ContinuumSelectedExactMassDecayTarget.ContinuumSelectedExactMassDecayTarget.gaugeContent
#print axioms YMGap.Continuum.ContinuumSelectedExactMassDecayTarget.ContinuumSelectedExactMassDecayTarget.uvAsymptoticFreedom
#print axioms YMGap.Continuum.ContinuumSelectedExactMassDecayTarget.ContinuumSelectedExactMassDecayTarget.interacting
#print axioms YMGap.Continuum.ContinuumSelectedExactMassDecayTarget.ContinuumSelectedExactMassDecayTarget.uniformMassGap
