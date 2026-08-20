/-
M4n -- the minimal same-object bounded-transfer mass-gap endpoint.

`WilsonLinkedOSGNSData` contains a canonical linear form gap because that is
the natural output of the Schur route.  The final bounded statement, however,
only consumes the selected operator-norm contraction and the positive exact
logarithmic rate.  A proof that supplies the norm gap directly should not also
be forced to supply an unused linear form-gap derivation.

This module therefore factors the same-measure Wilson/OS datum before the
linear form-gap field, states the direct operator-norm pin, and combines it
with the reconstruction-side positive exact rate.  The stronger linked
endpoint projects to this minimal one.  No inhabitant of the continuum data or
operator-norm pin is constructed here.
-/

import YMGap.Continuum.WilsonBoundedMassGapHandoff

namespace YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.MeasureLinkedOSReconstruction
open YMGap.Continuum.PhysicalSeparatorContinuumRealization
open YMGap.Continuum.TuranPositivity
open YMGap.Continuum.WilsonBoundedMassGapHandoff
open YMGap.Continuum.WilsonLinkedOSReconstruction

/-- The same-measure Wilson/OS datum before any linear or quadratic gap
inequality is imposed. -/
structure WilsonSelectedOSGNSData
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (H : ContinuumYMExistence mu) : Type 2 where
  measureLinked : MeasureLinkedOSGNSData H
  wilson : WilsonGNS.WilsonGNSData H.os_axioms.A
  expectationPinned : wilson.E = H.os_axioms.E.E
  timeTranslation :
    WilsonGNSTransferUnderdetermination.WilsonTimeTranslationPin wilson

namespace WilsonSelectedOSGNSData

/-- Forget the canonical linear form-gap field of the stronger linked datum. -/
def ofLinked
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonLinkedOSGNSData H) : WilsonSelectedOSGNSData H where
  measureLinked := D.measureLinked
  wilson := D.wilson
  expectationPinned := D.expectationPinned
  timeTranslation := D.timeTranslation

/-- The abstract reconstruction selected by the same projective OS bundle. -/
def reconstruction
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H) : OSReconstruction.OSReconstruction mu :=
  D.measureLinked.reconstruction

/-- The concrete Wilson transfer with exactly the OS4 model and separator of
the selected reconstruction. -/
def selectedSpectralData
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H) :
    SpectralGapData D.wilson.toGNSData.gnsComplete :=
  selectedSpectralGapData D.measureLinked D.timeTranslation

/-- The concrete and reconstruction separators agree definitionally. -/
theorem selectedSep_eq_reconstructionGapBound
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H) :
    D.selectedSpectralData.gap.sep = D.reconstruction.gapBound :=
  rfl

end WilsonSelectedOSGNSData

/-- The direct bounded transfer-operator gap on the selected vacuum
complement.  This is the smallest operator statement consumed by the final
bounded mass-gap endpoint. -/
structure WilsonOperatorNormGapPin
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H) : Type 2 where
  normGap : forall
      {x : D.wilson.toGNSData.gnsComplete.hilbert.carrier},
    D.selectedSpectralData.vacPerp x ->
      RCle
        (D.wilson.toGNSData.gnsComplete.hilbert.cinner
          (D.timeTranslation.op.T x) (D.timeTranslation.op.T x))
        (RCscale
          (D.selectedSpectralData.gap.sep * D.selectedSpectralData.gap.sep)
          (D.wilson.toGNSData.gnsComplete.hilbert.cinner x x))

/-- The minimal same-object endpoint: a positive exact logarithmic rate and a
bounded operator-norm gap sharing definitionally the selected OS separator. -/
structure WilsonMinimalBoundedMassGap
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H) : Type 2 where
  exactRate : PositiveExactLogGapWitness D.reconstruction
  operatorGap : WilsonOperatorNormGapPin D

namespace WilsonOperatorNormGapPin

/-- Project the norm conclusion of the stronger linked endpoint onto the
minimal same-measure datum. -/
def ofLinkedBoundedMassGap
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonLinkedOSGNSData H)
    (G : WilsonBoundedMassGap D) :
    WilsonOperatorNormGapPin (WilsonSelectedOSGNSData.ofLinked D) where
  normGap := fun hx => G.operatorNormGap hx

end WilsonOperatorNormGapPin

namespace WilsonMinimalBoundedMassGap

/-- Every stronger linked bounded endpoint projects to the minimal endpoint. -/
def ofLinkedBoundedMassGap
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonLinkedOSGNSData H)
    (G : WilsonBoundedMassGap D) :
    WilsonMinimalBoundedMassGap (WilsonSelectedOSGNSData.ofLinked D) where
  exactRate := G.exactRate.reconstructionGap
  operatorGap := WilsonOperatorNormGapPin.ofLinkedBoundedMassGap D G

/-- The exact logarithmic rate of the minimal endpoint. -/
def rate
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (G : WilsonMinimalBoundedMassGap D) : CReal :=
  G.exactRate.rate

/-- Constructive eventual positivity of the exact rate. -/
theorem rate_posEv
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (G : WilsonMinimalBoundedMassGap D) : PosEv G.rate :=
  G.exactRate.rate_posEv

/-- The rate is the exact logarithm of the separator appearing in the direct
operator-norm gap, via the definitionally shared reconstruction. -/
theorem rate_equiv_selectedSeparatorExactLog
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (G : WilsonMinimalBoundedMassGap D) :
    CReal.Equiv G.rate
      (OSExactLogGap.exactLogGap D.reconstruction
        G.exactRate.exactGap.positiveGapBound) :=
  G.exactRate.exactGap.rate_equiv

end WilsonMinimalBoundedMassGap

end YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff

#print axioms YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff.WilsonSelectedOSGNSData.ofLinked
#print axioms YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff.WilsonSelectedOSGNSData.selectedSep_eq_reconstructionGapBound
#print axioms YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff.WilsonOperatorNormGapPin.ofLinkedBoundedMassGap
#print axioms YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff.WilsonMinimalBoundedMassGap.ofLinkedBoundedMassGap
#print axioms YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff.WilsonMinimalBoundedMassGap.rate_posEv
#print axioms YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff.WilsonMinimalBoundedMassGap.rate_equiv_selectedSeparatorExactLog
