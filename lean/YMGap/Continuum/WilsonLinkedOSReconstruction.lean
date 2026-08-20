/-
M4h -- pin the measure-linked OS reconstruction to concrete Wilson GNS
dynamics without pretending that the legacy abstract Hilbert placeholder is
the completed GNS carrier.

`MeasureLinkedOSGNSData` fixes the projective OS functional and constructs an
`OSReconstruction` from the same OS4 spectral model and separator.  It does
not yet select a time translation on the concrete Wilson GNS completion.
Conversely, `WilsonGNSData` constructs that completion but, by itself,
underdetermines its dynamics.

This module joins the two boundaries honestly:

* `wilson.E = H.os_axioms.E.E` pins the static Wilson form to the selected OS
  functional;
* `WilsonTimeTranslationPin` selects a genuine positive self-adjoint
  contraction on the concrete completion;
* `selectedSpectralGapData` uses exactly that operator and exactly the OS
  bundle's spectral model and separator;
* `formGap` is the remaining operator/model identification.  It is a named
  analytic input, not derived from the static GNS datum.

The legacy `OSReconstruction.space` still has no carrier or inner product, so
no fake equality between it and the concrete completion is asserted here.
-/

import YMGap.Continuum.CanonicalTransferFormGap
import YMGap.Continuum.MeasureLinkedOSReconstruction
import YMGap.Continuum.WilsonGNSTransferUnderdetermination

namespace YMGap.Continuum.WilsonLinkedOSReconstruction

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CanonicalTransferFormGap
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.MeasureLinkedOSReconstruction
open YMGap.Continuum.OSReconstruction
open YMGap.Continuum.WilsonGNS
open YMGap.Continuum.WilsonGNSTransferUnderdetermination

/-! ## The bundle-pinned concrete spectral datum -/

/-- The OS bundle's located finite spectral gap, using the strict separator
and spectral bound already carried by the measure-linked reconstruction data. -/
def bundleLocatedGap
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : MeasureLinkedOSGNSData H) : LocatedSpectralGap H.os_axioms.S where
  sep := H.os_axioms.μ
  sep_lt_one := D.reconstructionData.gapBound_lt_one
  bound := D.reconstructionData.hasGap

/-- The concrete completed-Wilson-GNS spectral datum.  Its operator is the
selected Wilson time translation, while its model and separator are exactly
the ones in the fixed OS bundle. -/
def selectedSpectralGapData
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : MeasureLinkedOSGNSData H)
    {W : WilsonGNSData H.os_axioms.A}
    (P : WilsonTimeTranslationPin W) :
    SpectralGapData W.toGNSData.gnsComplete where
  op := P.op
  model := H.os_axioms.S
  gap := bundleLocatedGap D

/-! ## The strengthened same-object OS/GNS handoff -/

/-- Measure-linked OS data strengthened by a concrete Wilson GNS completion
and selected transfer dynamics.

The only operator/spectrum bridge is the explicit `formGap` field.  This is
the genuine analytic input excluded by the static-GNS underdetermination
theorem; no general inhabitant is supplied here. -/
structure WilsonLinkedOSGNSData
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    (H : ContinuumYMExistence mu) : Type 2 where
  /-- Projective functional and abstract OS reconstruction, already pinned to
  the bundle's OS4 model and separator. -/
  measureLinked : MeasureLinkedOSGNSData H
  /-- Wilson module structure on the very observable algebra of the bundle. -/
  wilson : WilsonGNSData H.os_axioms.A
  /-- The Wilson expectation is the selected projective OS functional. -/
  expectationPinned : wilson.E = H.os_axioms.E.E
  /-- A selected Euclidean one-step time translation on the concrete GNS
  completion. -/
  timeTranslation : WilsonTimeTranslationPin wilson
  /-- The selected operator realizes the same finite spectral separator that
  the OS bundle and abstract reconstruction use. -/
  formGap : CanonicalTransferFormGap
    (selectedSpectralGapData measureLinked timeTranslation)

namespace WilsonLinkedOSGNSData

/-! ## Reduction of the form-gap field to finite character Schur data -/

/-- The finite Schur datum together with the two OS4 identifications needed to
interpret its operator-form inequality as the selected continuum bundle's
inequality.

The identifications are kept fieldwise rather than collapsed into an equality
of `SpectralGapData` records.  Such a record equality would require transporting
the bundle's dependent spectral-bound proof through an unrelated finite-model
presentation.  The form-gap proposition itself depends only on the shared
operator and vacuum, while these two pins record that its model and numerical
separator have the intended OS4 meaning. -/
structure WilsonCharacterOS4Pin
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : MeasureLinkedOSGNSData H)
    {W : WilsonGNSData H.os_axioms.A}
    (P : WilsonTimeTranslationPin W)
    {w t : Q'} (ht : (0 : Q') <= t) (N : Nat)
    (hw0 : (0 : Q') <= w) (hw1 : w < (1 : Q'))
    : Type 2 where
  /-- Physical character coordinates and the two diagonal Schur identities. -/
  character : WilsonCharacterSpectrumPin W P w t ht N
  /-- The normalized finite character model is the selected OS4 model. -/
  modelPinned : (selectedSpectralGapData D P).model =
    (P.normalizedCharacterGapData (N := N) hw0 hw1).model
  /-- Its normalized heat-kernel separator is the selected OS4 separator. -/
  separatorPinned : (selectedSpectralGapData D P).gap.sep =
    (P.normalizedCharacterGapData (N := N) hw0 hw1).gap.sep

/-- The finite Schur pin supplies the operator-form inequality for the selected
Wilson transfer.  Both spectral data use definitionally the same operator and
vacuum, so no dependent equality of their model records is required. -/
def WilsonCharacterOS4Pin.toSelectedFormGap
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : MeasureLinkedOSGNSData H}
    {W : WilsonGNSData H.os_axioms.A}
    {P : WilsonTimeTranslationPin W}
    {w t : Q'} {ht : (0 : Q') <= t} {N : Nat}
    {hw0 : (0 : Q') <= w} {hw1 : w < (1 : Q')}
    (B : WilsonCharacterOS4Pin D P ht N hw0 hw1) :
    CanonicalTransferFormGap (selectedSpectralGapData D P) where
  form_gap := by
    intro x hx
    rw [B.separatorPinned]
    let Br := WilsonSpectralBridge.wilsonTransferSpectralBridge
      P.op w hw0 hw1 N RCScaleClose.rcScaleResidualPlus
      WilsonSchurIdentities.rscale_mono
      (PhysicalWilsonBridge.physicalCharacterDiagResolution
        P.op w t ht N B.character.diagonal)
    exact
      (CanonicalTransferFormGap.HamiltonianScalar.TransferSpectralBridge.toCanonicalFormGap
        Br).form_gap hx

/-- Construct the strengthened OS/GNS handoff from the smaller finite Schur
residual.  `WilsonCharacterSpectrumPin` carries the physical character
coordinate map and its two diagonal identities; its existing theorem supplies
the operator-form gap once the normalized model and separator are pinned to
the selected OS bundle. -/
def ofCharacterSpectrumPin
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : MeasureLinkedOSGNSData H)
    (W : WilsonGNSData H.os_axioms.A)
    (expectationPinned : W.E = H.os_axioms.E.E)
    (P : WilsonTimeTranslationPin W)
    {w t : Q'} {ht : (0 : Q') <= t} {N : Nat}
    (hw0 : (0 : Q') <= w) (hw1 : w < (1 : Q'))
    (characterOS4 : WilsonCharacterOS4Pin D P ht N hw0 hw1) :
    WilsonLinkedOSGNSData H where
  measureLinked := D
  wilson := W
  expectationPinned := expectationPinned
  timeTranslation := P
  formGap := characterOS4.toSelectedFormGap

/-- The abstract reconstruction built from the same projective OS bundle. -/
def reconstruction
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonLinkedOSGNSData H) : OSReconstruction mu :=
  D.measureLinked.reconstruction

/-- The concrete selected spectral model and the abstract reconstruction use
definitionally the same OS4 model. -/
theorem selectedModel_eq_reconstructionSpec
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonLinkedOSGNSData H) :
    (selectedSpectralGapData D.measureLinked D.timeTranslation).model =
      D.reconstruction.spec :=
  rfl

/-- The concrete selected separator and the abstract reconstruction use
definitionally the same OS4 rate. -/
theorem selectedSep_eq_reconstructionGapBound
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonLinkedOSGNSData H) :
    (selectedSpectralGapData D.measureLinked D.timeTranslation).gap.sep =
      D.reconstruction.gapBound :=
  rfl

/-- The canonical operator-form gap exposed at the model and separator shared
with the abstract reconstruction.  Its right-hand side is definitionally the
concrete `separator * inner` scalar action. -/
def reconstructionCanonicalFormGap
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonLinkedOSGNSData H) :
    CanonicalTransferFormGap
      (selectedSpectralGapData D.measureLinked D.timeTranslation) :=
  D.formGap

/-- Compatibility projection to the older residual interface. -/
def reconstructionFormGap
    {M : Nat -> Type} {mu : ContinuumMeasure.ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonLinkedOSGNSData H) :
    TransferFormGapResidual
      (selectedSpectralGapData D.measureLinked D.timeTranslation) :=
  D.reconstructionCanonicalFormGap.toResidual

end WilsonLinkedOSGNSData

end YMGap.Continuum.WilsonLinkedOSReconstruction

#print axioms YMGap.Continuum.WilsonLinkedOSReconstruction.bundleLocatedGap
#print axioms YMGap.Continuum.WilsonLinkedOSReconstruction.selectedSpectralGapData
#print axioms YMGap.Continuum.WilsonLinkedOSReconstruction.WilsonLinkedOSGNSData.WilsonCharacterOS4Pin
#print axioms YMGap.Continuum.WilsonLinkedOSReconstruction.WilsonLinkedOSGNSData.WilsonCharacterOS4Pin.toSelectedFormGap
#print axioms YMGap.Continuum.WilsonLinkedOSReconstruction.WilsonLinkedOSGNSData.ofCharacterSpectrumPin
#print axioms YMGap.Continuum.WilsonLinkedOSReconstruction.WilsonLinkedOSGNSData.selectedModel_eq_reconstructionSpec
#print axioms YMGap.Continuum.WilsonLinkedOSReconstruction.WilsonLinkedOSGNSData.selectedSep_eq_reconstructionGapBound
#print axioms YMGap.Continuum.WilsonLinkedOSReconstruction.WilsonLinkedOSGNSData.reconstructionCanonicalFormGap
#print axioms YMGap.Continuum.WilsonLinkedOSReconstruction.WilsonLinkedOSGNSData.reconstructionFormGap
