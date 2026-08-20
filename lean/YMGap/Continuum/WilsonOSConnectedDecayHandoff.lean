/-
M4q -- identify a connected OS insertion with the selected Wilson transfer
matrix coefficient and inherit its geometric decay.

The bounded-transfer argument already gives decay of every matrix coefficient
whose propagated vector lies in the selected vacuum complement.  To apply it
to the OS Schwinger functional one must still prove that the chosen connected
insertion is represented by exactly that vector and transfer.  This module
names that one same-object equality and proves the resulting squared
connected-correlation bound.

No OS connected insertion, vacuum-orthogonality proof, or equality with the
Wilson matrix coefficient is constructed here.
-/

import YMGap.Continuum.WilsonMatrixCoefficientDecayHandoff

namespace YMGap.Continuum.WilsonOSConnectedDecayHandoff

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.BoundedTransferCalculus
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.PhysicalSeparatorContinuumRealization
open YMGap.Continuum.WilsonIteratedNormDecayHandoff
open YMGap.Continuum.WilsonMatrixCoefficientDecayHandoff
open YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff

/-- The connected OS gap insertion is the autocorrelation of its embedded
Wilson GNS vector under the already-selected time translation. -/
structure WilsonOSConnectedMatrixCoefficientPin
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H) : Type 2 where
  osConnected : OSConnectedTwoPointSemantics H
  gapState_vacPerp : D.selectedSpectralData.vacPerp
    (embedV D.wilson.toGNSData osConnected.gapInsertion)
  osConnectedCorr_eq : forall n : Nat,
    (Quotient.mk crealSetoid
        (CReal.ofQ' (H.os_axioms.E.E
          (osConnected.connectedInsertion osConnected.gapInsertion n))) : RC) =
      D.wilson.toGNSData.gnsComplete.hilbert.cinner
        (Tpow D.timeTranslation.op n
          (embedV D.wilson.toGNSData osConnected.gapInsertion))
        (embedV D.wilson.toGNSData osConnected.gapInsertion)

namespace WilsonOSConnectedMatrixCoefficientPin

/-- The completed GNS vector selected by the connected gap insertion. -/
def gapState
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (B : WilsonOSConnectedMatrixCoefficientPin D) :
    D.wilson.toGNSData.gnsComplete.hilbert.carrier :=
  embedV D.wilson.toGNSData B.osConnected.gapInsertion

/-- The OS connected gap correlation, embedded in the `RC` quotient used by
the completed Wilson GNS inner product. -/
def connectedCorrRC
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (B : WilsonOSConnectedMatrixCoefficientPin D)
    (n : Nat) : RC :=
  Quotient.mk crealSetoid
    (CReal.ofQ' (H.os_axioms.E.E
      (B.osConnected.connectedInsertion B.osConnected.gapInsertion n)))

/-- The connected OS two-point function inherits the selected transfer's
geometric squared-correlation decay. -/
theorem connectedCorrelationSqDecay
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (B : WilsonOSConnectedMatrixCoefficientPin D)
    (G : WilsonIteratedBoundedMassGap D)
    (n : Nat) :
    RCle
      (RCmul (B.connectedCorrRC n) (B.connectedCorrRC n))
      (RCmul
        (RCscale
          ((D.selectedSpectralData.gap.sep *
              D.selectedSpectralData.gap.sep) ^ n)
          (D.wilson.toGNSData.gnsComplete.hilbert.cinner
            B.gapState B.gapState))
        (D.wilson.toGNSData.gnsComplete.hilbert.cinner
          B.gapState B.gapState)) := by
  unfold connectedCorrRC gapState
  rw [B.osConnectedCorr_eq n]
  exact WilsonMatrixCoefficientDecayHandoff.WilsonIteratedBoundedMassGap.autocorrelationSqDecay
    G n B.gapState_vacPerp

end WilsonOSConnectedMatrixCoefficientPin

end YMGap.Continuum.WilsonOSConnectedDecayHandoff

#print axioms YMGap.Continuum.WilsonOSConnectedDecayHandoff.WilsonOSConnectedMatrixCoefficientPin.connectedCorrelationSqDecay
