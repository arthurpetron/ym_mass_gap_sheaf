/-
M4r -- compose the projective continuum correlator with the selected Wilson
transfer and inherit geometric decay.

`ProjectiveOSCorrelationHandoff` already constructs the physical continuum
correlator as the limit of the sampled finite-stage expectations.  The Wilson
bounded-transfer branch separately proves geometric decay of matrix
coefficients.  This module isolates the remaining same-object equality between
the selected projective gap correlator and the Wilson transfer
autocorrelation, then composes the two checked reductions.

No projective measure, continuum Yang--Mills theory, Wilson transfer,
vacuum-orthogonality proof, or correlator equality is constructed here.
-/

import YMGap.Continuum.ProjectiveOSCorrelationHandoff
import YMGap.Continuum.WilsonOSConnectedDecayHandoff

namespace YMGap.Continuum.ProjectiveWilsonConnectedDecayHandoff

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.BoundedTransferCalculus
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.MeasureLinkedOSReconstruction
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorContinuumRealization
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.ProjectiveOSCorrelationHandoff
open YMGap.Continuum.WilsonIteratedNormDecayHandoff
open YMGap.Continuum.WilsonMatrixCoefficientDecayHandoff
open YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff
open YMGap.Continuum.WilsonOSConnectedDecayHandoff

/-- The physical continuum gap correlator constructed from the selected
projective thread is the autocorrelation of its embedded connected OS gap
state under the selected Wilson transfer. -/
structure ProjectiveWilsonOSMatrixCoefficientPin
    {P : PhysicalSeparator}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {L : MeasureLinkedOSGNSData H}
    {A : PhysicalSpacing}
    {sampling : PhysicalSeparationSampling A}
    (B : ProjectiveOSCorrelationHandoff P H L sampling)
    (W : WilsonSelectedOSGNSData H) : Type 2 where
  gapState_vacPerp : W.selectedSpectralData.vacPerp
    (embedV W.wilson.toGNSData B.osConnectedTwoPoint.gapInsertion)
  continuumGapCorr_eq : forall n : Nat,
    (Quotient.mk crealSetoid
        (B.continuumCorr B.gapObservable n) : RC) =
      W.wilson.toGNSData.gnsComplete.hilbert.cinner
        (Tpow W.timeTranslation.op n
          (embedV W.wilson.toGNSData
            B.osConnectedTwoPoint.gapInsertion))
        (embedV W.wilson.toGNSData B.osConnectedTwoPoint.gapInsertion)

namespace ProjectiveWilsonOSMatrixCoefficientPin

/-- The completed Wilson GNS state selected by the projective gap
observable's connected OS insertion. -/
def gapState
    {P : PhysicalSeparator}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {L : MeasureLinkedOSGNSData H}
    {A : PhysicalSpacing}
    {sampling : PhysicalSeparationSampling A}
    {B : ProjectiveOSCorrelationHandoff P H L sampling}
    {W : WilsonSelectedOSGNSData H}
    (_C : ProjectiveWilsonOSMatrixCoefficientPin B W) :
    W.wilson.toGNSData.gnsComplete.hilbert.carrier :=
  embedV W.wilson.toGNSData B.osConnectedTwoPoint.gapInsertion

/-- The projectively constructed continuum gap correlator, embedded in the
completed-GNS constructive-real quotient. -/
def continuumGapCorrRC
    {P : PhysicalSeparator}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {L : MeasureLinkedOSGNSData H}
    {A : PhysicalSpacing}
    {sampling : PhysicalSeparationSampling A}
    {B : ProjectiveOSCorrelationHandoff P H L sampling}
    {W : WilsonSelectedOSGNSData H}
    (_C : ProjectiveWilsonOSMatrixCoefficientPin B W)
    (n : Nat) : RC :=
  Quotient.mk crealSetoid (B.continuumCorr B.gapObservable n)

/-- The projective functional compatibility converts the continuum/Wilson pin
into the direct connected-OS/Wilson pin used by the OS decay theorem. -/
def toWilsonOSConnectedMatrixCoefficientPin
    {P : PhysicalSeparator}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {L : MeasureLinkedOSGNSData H}
    {A : PhysicalSpacing}
    {sampling : PhysicalSeparationSampling A}
    {B : ProjectiveOSCorrelationHandoff P H L sampling}
    {W : WilsonSelectedOSGNSData H}
    (C : ProjectiveWilsonOSMatrixCoefficientPin B W) :
    WilsonOSConnectedMatrixCoefficientPin W where
  osConnected := B.osConnectedTwoPoint
  gapState_vacPerp := C.gapState_vacPerp
  osConnectedCorr_eq := fun n => by
    calc
      (Quotient.mk crealSetoid
          (CReal.ofQ' (H.os_axioms.E.E
            (B.osConnectedTwoPoint.connectedInsertion
              B.osConnectedTwoPoint.gapInsertion n))) : RC) =
          Quotient.mk crealSetoid
            (B.continuumCorr B.gapObservable n) := by
              apply Quotient.sound
              exact B.gapFunctional_eq n
      _ = W.wilson.toGNSData.gnsComplete.hilbert.cinner
          (Tpow W.timeTranslation.op n C.gapState) C.gapState :=
        C.continuumGapCorr_eq n

/-- The physical continuum gap correlator obtained from projective cutoff
removal inherits squared geometric decay from the selected Wilson transfer. -/
theorem continuumGapCorrelationSqDecay
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
    (n : Nat) :
    RCle
      (RCmul (C.continuumGapCorrRC n) (C.continuumGapCorrRC n))
      (RCmul
        (RCscale
          ((W.selectedSpectralData.gap.sep *
              W.selectedSpectralData.gap.sep) ^ n)
          (W.wilson.toGNSData.gnsComplete.hilbert.cinner
            C.gapState C.gapState))
        (W.wilson.toGNSData.gnsComplete.hilbert.cinner
          C.gapState C.gapState)) := by
  unfold continuumGapCorrRC gapState
  rw [C.continuumGapCorr_eq n]
  exact WilsonMatrixCoefficientDecayHandoff.WilsonIteratedBoundedMassGap.autocorrelationSqDecay
    G n C.gapState_vacPerp

end ProjectiveWilsonOSMatrixCoefficientPin

end YMGap.Continuum.ProjectiveWilsonConnectedDecayHandoff

#print axioms YMGap.Continuum.ProjectiveWilsonConnectedDecayHandoff.ProjectiveWilsonOSMatrixCoefficientPin.toWilsonOSConnectedMatrixCoefficientPin
#print axioms YMGap.Continuum.ProjectiveWilsonConnectedDecayHandoff.ProjectiveWilsonOSMatrixCoefficientPin.continuumGapCorrelationSqDecay
