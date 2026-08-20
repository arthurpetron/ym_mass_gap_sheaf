/-
M4i -- attach the exact cutoff-removed logarithmic rate to the same concrete
Wilson GNS spectral datum used by the operator-form gap.

`PositiveExactLogGapWitness` is stated for the legacy abstract
`OSReconstruction`.  `WilsonLinkedOSGNSData` separately selects a concrete
completed Wilson GNS, its time translation, and a spectral datum whose model
and separator are definitionally those of that reconstruction.  This module
packages the two facts without asserting that the legacy placeholder space is
the concrete carrier.

The resulting endpoint proves that one positive exact rate is computed from
the separator governing the concrete Wilson operator-form bound.  It does not
construct the continuum data that inhabit the handoff, and it does not build
the unbounded Hamiltonian or its functional calculus.
-/

import YMGap.Continuum.PhysicalSeparatorContinuumRealization
import YMGap.Continuum.WilsonLinkedOSReconstruction

namespace YMGap.Continuum.WilsonExactRateGapHandoff

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.CanonicalTransferFormGap
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.OSExactLogGap
open YMGap.Continuum.OSReconstruction
open YMGap.Continuum.PhysicalSeparatorContinuumRealization
open YMGap.Continuum.TuranPositivity
open YMGap.Continuum.WilsonLinkedOSReconstruction

/-- A strictly positive exact logarithmic rate attached to the same concrete
Wilson GNS datum that owns the selected transfer operator and form gap. -/
structure WilsonPositiveExactLogGapWitness
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonLinkedOSGNSData H) : Type 2 where
  /-- The exact-rate witness for the reconstruction sharing the selected
  Wilson datum's OS4 model and separator. -/
  reconstructionGap : PositiveExactLogGapWitness D.reconstruction

namespace WilsonPositiveExactLogGapWitness

/-- Attach an already constructed reconstruction-side exact-rate witness to
the concrete Wilson datum sharing its OS4 model and separator. -/
def ofReconstructionWitness
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonLinkedOSGNSData H)
    (P : PositiveExactLogGapWitness D.reconstruction) :
    WilsonPositiveExactLogGapWitness D where
  reconstructionGap := P

/-- The positive exact logarithmic rate. -/
def rate
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonLinkedOSGNSData H}
    (P : WilsonPositiveExactLogGapWitness D) : CReal :=
  P.reconstructionGap.rate

/-- Constructive eventual positivity of the exact rate. -/
theorem rate_posEv
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonLinkedOSGNSData H}
    (P : WilsonPositiveExactLogGapWitness D) : PosEv P.rate :=
  P.reconstructionGap.rate_posEv

/-- The selected concrete Wilson datum carries the operator-form inequality
at the OS4 model and separator used to compute `rate`. -/
def selectedFormGap
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonLinkedOSGNSData H}
    (_P : WilsonPositiveExactLogGapWitness D) :
    CanonicalTransferFormGap
      (selectedSpectralGapData D.measureLinked D.timeTranslation) :=
  D.reconstructionCanonicalFormGap

/-- The exact-rate witness's finite spectral bound is definitionally the bound
of the selected concrete Wilson spectral datum. -/
theorem selectedSpectralGapBound
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonLinkedOSGNSData H}
    (P : WilsonPositiveExactLogGapWitness D) :
    SpectralGap.SpectralGapBound
      (selectedSpectralGapData D.measureLinked D.timeTranslation).model
      (selectedSpectralGapData D.measureLinked D.timeTranslation).gap.sep :=
  P.reconstructionGap.exactGap.spectralGapBound

/-- The exact rate is equivalent to the constructive logarithm computed from
the selected concrete Wilson datum's separator (via its shared
reconstruction). -/
theorem rate_equiv_selectedSeparatorExactLog
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonLinkedOSGNSData H}
    (P : WilsonPositiveExactLogGapWitness D) :
    CReal.Equiv P.rate
      (exactLogGap D.reconstruction
        P.reconstructionGap.exactGap.positiveGapBound) :=
  P.reconstructionGap.exactGap.rate_equiv

end WilsonPositiveExactLogGapWitness

end YMGap.Continuum.WilsonExactRateGapHandoff

#print axioms YMGap.Continuum.WilsonExactRateGapHandoff.WilsonPositiveExactLogGapWitness.ofReconstructionWitness
#print axioms YMGap.Continuum.WilsonExactRateGapHandoff.WilsonPositiveExactLogGapWitness.rate_posEv
#print axioms YMGap.Continuum.WilsonExactRateGapHandoff.WilsonPositiveExactLogGapWitness.selectedFormGap
#print axioms YMGap.Continuum.WilsonExactRateGapHandoff.WilsonPositiveExactLogGapWitness.selectedSpectralGapBound
#print axioms YMGap.Continuum.WilsonExactRateGapHandoff.WilsonPositiveExactLogGapWitness.rate_equiv_selectedSeparatorExactLog
