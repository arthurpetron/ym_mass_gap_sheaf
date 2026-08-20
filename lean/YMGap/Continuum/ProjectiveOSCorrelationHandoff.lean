/-
M4e -- derive the physical continuum correlator and its OS-functional
identification from one projective-thread handoff.

`ProjectiveOSFunctionalIdentification` already states that every fixed OS
observable has a continuum expectation obtained from the selected measures
`mu.pick j`.  The physical-separator endpoint previously asked independently
for a stage correlator, a projective identification, a continuum limit, and an
OS gap-correlation identification.  Those separate fields obscure the one
analytic compatibility statement that is actually needed: the physically
sampled separator correlator must be the finite-stage expectation of a fixed
OS observable.

`ProjectiveOSCorrelationHandoff` records exactly that compatibility.  From it
and the existing measure-linked OS convergence, this module constructs
`ContinuumCorrelationSemantics` and `OSGapCorrelationIdentification`.

No expectation semantics, convergence theorem, continuum measure, or OS
axiom is manufactured here.  An inhabitant of the handoff remains open
analytic data.
-/

import YMGap.Constructive.TrigAddCReal
import YMGap.Continuum.PhysicalSeparatorContinuumRealization

namespace YMGap.Continuum.ProjectiveOSCorrelationHandoff

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.MeasureLinkedOSReconstruction
open YMGap.Continuum.OSReconstruction
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorContinuumRealization
open YMGap.Continuum.PhysicalSeparatorLogRate

/-- One same-object bridge from physically sampled separator correlators to
the fixed stage OS functional carried by `MeasureLinkedOSGNSData`.

The field `sampledCorr_eq_stageExpectation` is the load-bearing analytic
statement.  Its right-hand observable does not depend on the cutoff `j`, so
the already-supplied projective-functional convergence applies directly.
`gapFunctional_eq` singles out the nonzero channel later matched to the
reconstruction's spectral correlator. -/
structure ProjectiveOSCorrelationHandoff
    (P : PhysicalSeparator)
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (H : ContinuumYMExistence mu)
    (D : MeasureLinkedOSGNSData H)
    {A : PhysicalSeparatorLogRate.PhysicalSpacing}
    (sampling : PhysicalSeparationSampling A) : Type 2 where
  /-- Fixed evaluation of separator correlators on stage measures. -/
  stageCorrelators : StageCorrelationSemantics P M
  /-- The separator correlators are evaluated on the selected projective
  thread, not on an unrelated family. -/
  projectiveIdentification :
    ProjectiveCorrIdentification P mu stageCorrelators
  /-- Fixed connected-two-point insertion semantics in the OS algebra. -/
  osConnectedTwoPoint : OSConnectedTwoPointSemantics H
  /-- The fixed OS observable representing each separator observable at each
  integer physical separation. -/
  continuumInsertion : P.corrIface.Obs -> Nat -> H.os_axioms.A.carrier
  /-- The physically sampled separator correlator is the stage expectation of
  the corresponding cutoff-independent OS observable. -/
  sampledCorr_eq_stageExpectation :
    forall (j : Nat) (O : P.corrIface.Obs) (t : Nat),
      CReal.Equiv
        (CReal.ofQ'
          (stageCorrelators.corrFromStage j (mu.pick j) O
            (sampling.latticeSteps j t)))
        (D.stageFunctional.expectationFromStage j (mu.pick j)
          (continuumInsertion O t))
  /-- The separator observable used for the gap channel. -/
  gapObservable : P.corrIface.Obs
  /-- The gap observable is gauge-invariant and local. -/
  gapObservable_local : P.corrIface.GaugeInvariantLocal gapObservable
  /-- The OS connected gap insertion and the chosen continuum insertion have
  the same Schwinger-functional value. -/
  gapFunctional_eq : forall t : Nat,
    CReal.Equiv
      (CReal.ofQ' (H.os_axioms.E.E
        (osConnectedTwoPoint.connectedInsertion
          osConnectedTwoPoint.gapInsertion t)))
      (CReal.ofQ' (H.os_axioms.E.E (continuumInsertion gapObservable t)))

namespace ProjectiveOSCorrelationHandoff

/-- The continuum correlator is canonically the OS Schwinger functional on
the fixed insertion selected by the handoff. -/
def continuumCorr
    {P : PhysicalSeparator}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : MeasureLinkedOSGNSData H}
    {A : PhysicalSeparatorLogRate.PhysicalSpacing}
    {sampling : PhysicalSeparationSampling A}
    (B : ProjectiveOSCorrelationHandoff P H D sampling)
    (O : P.corrIface.Obs) (t : Nat) : CReal :=
  CReal.ofQ' (H.os_axioms.E.E (B.continuumInsertion O t))

/-- The existing projective OS-functional convergence, transported across
the sampled-correlation identification, constructs the physical continuum
correlator limit. -/
def continuumCorrelators
    {P : PhysicalSeparator}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : MeasureLinkedOSGNSData H}
    {A : PhysicalSeparatorLogRate.PhysicalSpacing}
    {sampling : PhysicalSeparationSampling A}
    (B : ProjectiveOSCorrelationHandoff P H D sampling) :
    ContinuumCorrelationSemantics P mu B.stageCorrelators A sampling where
  continuumCorr := B.continuumCorr
  rescaledStageConverges := fun O t =>
    YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
      (fun j => CReal.Equiv.symm
        (B.sampledCorr_eq_stageExpectation j O t))
      (D.projectiveFunctional.stageExpectationConverges
        (B.continuumInsertion O t))

/-- The remaining spectral-channel assertion after the projective correlator
limit and its OS-functional interpretation have been derived.  This is kept
separate because identifying the OS correlator with the reconstruction's
spectral model requires the GNS/spectral theorem, not merely projective
measure convergence. -/
structure ReconstructionSpectralChannelHandoff
    {P : PhysicalSeparator}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : MeasureLinkedOSGNSData H}
    {A : PhysicalSeparatorLogRate.PhysicalSpacing}
    {sampling : PhysicalSeparationSampling A}
    (B : ProjectiveOSCorrelationHandoff P H D sampling)
    (rec : OSReconstruction mu) : Type 1 where
  spectralCorr_eq : forall t : Nat,
    CReal.Equiv
      (B.continuumCorrelators.continuumCorr B.gapObservable t)
      (CReal.ofQ' (SpectralGap.corr rec.spec t))
  spectralCorrZero_pos : (0 : Q') < SpectralGap.corr rec.spec 0

/-- Build the standard reconstruction-correlation identification with the
same gap observable already fixed by the projective/OS handoff. -/
def reconstructionCorrelators
    {P : PhysicalSeparator}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : MeasureLinkedOSGNSData H}
    {A : PhysicalSeparatorLogRate.PhysicalSpacing}
    {sampling : PhysicalSeparationSampling A}
    (B : ProjectiveOSCorrelationHandoff P H D sampling)
    (rec : OSReconstruction mu)
    (S : ReconstructionSpectralChannelHandoff B rec) :
    ReconstructionCorrIdentification P rec B.continuumCorrelators where
  gapObservable := B.gapObservable
  gapObservable_local := B.gapObservable_local
  spectralCorr_eq := S.spectralCorr_eq
  spectralCorrZero_pos := S.spectralCorrZero_pos

/-- The OS connected gap two-point function is definitionally the continuum
correlator selected above, up to the explicit functional-value compatibility
stored in the handoff. -/
def osGapCorrelation
    {P : PhysicalSeparator}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : MeasureLinkedOSGNSData H}
    {A : PhysicalSeparatorLogRate.PhysicalSpacing}
    {sampling : PhysicalSeparationSampling A}
    (B : ProjectiveOSCorrelationHandoff P H D sampling)
    (rec : OSReconstruction mu)
    (S : ReconstructionSpectralChannelHandoff B rec) :
    OSGapCorrelationIdentification P H B.osConnectedTwoPoint
      B.continuumCorrelators (B.reconstructionCorrelators rec S) where
  gapCorr_eq := B.gapFunctional_eq

end ProjectiveOSCorrelationHandoff

end YMGap.Continuum.ProjectiveOSCorrelationHandoff

#print axioms YMGap.Continuum.ProjectiveOSCorrelationHandoff.ProjectiveOSCorrelationHandoff.continuumCorr
#print axioms YMGap.Continuum.ProjectiveOSCorrelationHandoff.ProjectiveOSCorrelationHandoff.continuumCorrelators
#print axioms YMGap.Continuum.ProjectiveOSCorrelationHandoff.ProjectiveOSCorrelationHandoff.reconstructionCorrelators
#print axioms YMGap.Continuum.ProjectiveOSCorrelationHandoff.ProjectiveOSCorrelationHandoff.osGapCorrelation
