/-
# Wilson GNS handoff for the raw moving-cube continuum channel

The projective/OS compiler identifies the literal raw moving-cube continuum
limit with one connected insertion in the selected OS functional.  This file
isolates the next same-object statement: that connected insertion is the
autorrelation of its embedded vector under the selected Wilson transfer on
the completed GNS carrier.

The projective handoff is parameterized by `W.measureLinked`, so the measure
thread, OS functional, Wilson expectation, completed carrier, and transfer
cannot drift apart.  The resulting equality identifies the exact raw
continuum correlation with the Wilson matrix coefficient.  If an all-vector
bounded mass-gap datum is separately supplied, the raw channel inherits its
squared decay.

No projective/OS handoff, Wilson GNS datum, matrix-coefficient pin, or
all-vector operator gap is inhabited here.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeProjectiveOSCorrelationHandoff
import YMGap.Continuum.WilsonOSConnectedDecayHandoff

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeWilsonGNSHandoff

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BoundedTransferCalculus
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeProjectiveOSCorrelationHandoff
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel
open YMGap.Continuum.WilsonIteratedNormDecayHandoff
open YMGap.Continuum.WilsonMatrixCoefficientDecayHandoff
open YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff
open YMGap.Continuum.WilsonOSConnectedDecayHandoff

/-! ## 1. Pin the exact raw OS channel to one Wilson matrix coefficient -/

/-- The connected insertion selected by the exact raw/projective handoff is
represented by its embedded Wilson GNS vector and the selected time
translation.

The projective handoff consumes `W.measureLinked` definitionally.  This is the
critical same-measure constraint that prevents a Wilson matrix coefficient
from an unrelated reconstruction from satisfying the interface. -/
structure RawMovingCubeWilsonMatrixCoefficientPin
    (family : DynamicVacuumSectorCompletedFamily 0)
    (raw : MovingCubeRawScheduledRepresentativeVariation family)
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (H : ContinuumYMExistence mu)
    (W : WilsonSelectedOSGNSData H)
    (B : RawMovingCubeProjectiveOSCorrelationHandoff
      family raw H W.measureLinked) : Type 2 where
  /-- The embedded connected insertion lies in the selected vacuum
  complement. -/
  gapState_vacPerp : W.selectedSpectralData.vacPerp
    (embedV W.wilson.toGNSData B.osConnected.gapInsertion)
  /-- The connected OS functional is the autocorrelation under the selected
  Wilson transfer of that exact embedded state. -/
  osConnectedCorr_eq : forall time : Nat,
    (Quotient.mk crealSetoid
        (CReal.ofQ' (H.os_axioms.E.E
          (B.osConnected.connectedInsertion
            B.osConnected.gapInsertion time))) : RC) =
      W.wilson.toGNSData.gnsComplete.hilbert.cinner
        (Tpow W.timeTranslation.op time
          (embedV W.wilson.toGNSData B.osConnected.gapInsertion))
        (embedV W.wilson.toGNSData B.osConnected.gapInsertion)

namespace RawMovingCubeWilsonMatrixCoefficientPin

/-- The exact completed Wilson GNS state selected by the raw moving-cube
observable through the projective/OS handoff. -/
def gapState
    {family : DynamicVacuumSectorCompletedFamily 0}
    {raw : MovingCubeRawScheduledRepresentativeVariation family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    {B : RawMovingCubeProjectiveOSCorrelationHandoff
      family raw H W.measureLinked}
    (_C : RawMovingCubeWilsonMatrixCoefficientPin family raw H W B) :
    W.wilson.toGNSData.gnsComplete.hilbert.carrier :=
  embedV W.wilson.toGNSData B.osConnected.gapInsertion

/-- Compatibility projection to the generic connected-OS/Wilson pin. -/
def toWilsonOSConnectedMatrixCoefficientPin
    {family : DynamicVacuumSectorCompletedFamily 0}
    {raw : MovingCubeRawScheduledRepresentativeVariation family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    {B : RawMovingCubeProjectiveOSCorrelationHandoff
      family raw H W.measureLinked}
    (C : RawMovingCubeWilsonMatrixCoefficientPin family raw H W B) :
    WilsonOSConnectedMatrixCoefficientPin W where
  osConnected := B.osConnected
  gapState_vacPerp := C.gapState_vacPerp
  osConnectedCorr_eq := C.osConnectedCorr_eq

/-! ## 2. The observable-connected projective/OS/GNS equality -/

/-- The literal raw continuum correlation is the autocorrelation of its exact
embedded state under the selected Wilson transfer. -/
theorem rawContinuumConnectedAutocorrelation_eq_matrixCoefficient
    {family : DynamicVacuumSectorCompletedFamily 0}
    {raw : MovingCubeRawScheduledRepresentativeVariation family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    {B : RawMovingCubeProjectiveOSCorrelationHandoff
      family raw H W.measureLinked}
    (C : RawMovingCubeWilsonMatrixCoefficientPin family raw H W B)
    (time : Nat) :
    (rawMovingCubeContinuumLimitOfVariation family raw).continuumConnectedAutocorrelation
        time =
      W.wilson.toGNSData.gnsComplete.hilbert.cinner
        (Tpow W.timeTranslation.op time C.gapState) C.gapState := by
  rw [B.rawContinuumConnectedAutocorrelation_eq_osConnected time]
  exact C.osConnectedCorr_eq time

/-! ## 3. A supplied all-vector gap implies this channel's decay -/

/-- Once the selected Wilson transfer has a uniform iterated bound on the
whole vacuum complement, the definitionally connected raw continuum channel
inherits its squared geometric decay.  This theorem consumes such a gap; it
does not derive it from the one channel. -/
theorem rawContinuumConnectedAutocorrelationSqDecay
    {family : DynamicVacuumSectorCompletedFamily 0}
    {raw : MovingCubeRawScheduledRepresentativeVariation family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    {B : RawMovingCubeProjectiveOSCorrelationHandoff
      family raw H W.measureLinked}
    (C : RawMovingCubeWilsonMatrixCoefficientPin family raw H W B)
    (G : WilsonIteratedBoundedMassGap W)
    (time : Nat) :
    RCle
      (RCmul
        ((rawMovingCubeContinuumLimitOfVariation family raw).continuumConnectedAutocorrelation
          time)
        ((rawMovingCubeContinuumLimitOfVariation family raw).continuumConnectedAutocorrelation
          time))
      (RCmul
        (RCscale
          ((W.selectedSpectralData.gap.sep *
              W.selectedSpectralData.gap.sep) ^ time)
          (W.wilson.toGNSData.gnsComplete.hilbert.cinner
            C.gapState C.gapState))
        (W.wilson.toGNSData.gnsComplete.hilbert.cinner
          C.gapState C.gapState)) := by
  rw [C.rawContinuumConnectedAutocorrelation_eq_matrixCoefficient time]
  exact WilsonIteratedBoundedMassGap.autocorrelationSqDecay
    G time C.gapState_vacPerp

end RawMovingCubeWilsonMatrixCoefficientPin

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeWilsonGNSHandoff

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeWilsonGNSHandoff.RawMovingCubeWilsonMatrixCoefficientPin.toWilsonOSConnectedMatrixCoefficientPin
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeWilsonGNSHandoff.RawMovingCubeWilsonMatrixCoefficientPin.rawContinuumConnectedAutocorrelation_eq_matrixCoefficient
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeWilsonGNSHandoff.RawMovingCubeWilsonMatrixCoefficientPin.rawContinuumConnectedAutocorrelationSqDecay
