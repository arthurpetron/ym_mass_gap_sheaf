/-
M4m -- the bounded-transfer form of the same-object Wilson mass-gap handoff.

The selected concrete Wilson datum already carries a canonical linear form
gap.  `WilsonOperatorNormGapHandoff` upgrades it, from one square Schur
identity, to the genuine bounded-operator estimate on the vacuum complement.
`WilsonExactRateGapHandoff` independently attaches the positive cutoff-removed
logarithmic rate to the same datum and the same OS4 separator.

The structure below records both conclusions on one `WilsonLinkedOSGNSData`.
It is a conditional endpoint: this module does not construct continuum
Yang--Mills data, the projective OS handoff, the Wilson time translation, the
character pins, the square identity, or exact-rate convergence.
-/

import YMGap.Continuum.WilsonExactRateGapHandoff
import YMGap.Continuum.WilsonQuadraticFormGapHandoff

namespace YMGap.Continuum.WilsonBoundedMassGapHandoff

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.MeasureLinkedOSReconstruction
open YMGap.Continuum.WilsonExactRateGapHandoff
open YMGap.Continuum.WilsonLinkedOSReconstruction
open YMGap.Continuum.WilsonOperatorNormGapHandoff
open YMGap.Continuum.WilsonQuadraticFormGapHandoff
open YMGap.Continuum.TuranPositivity

/-- One concrete Wilson GNS datum carrying both the bounded transfer-operator
gap and its positive exact logarithmic rate.  Both statements use the selected
OS4 separator definitionally. -/
structure WilsonBoundedMassGap
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonLinkedOSGNSData H) : Type 2 where
  /-- The cutoff-removed positive exact logarithmic rate on this datum. -/
  exactRate : WilsonPositiveExactLogGapWitness D
  /-- The selected bounded transfer contracts the vacuum complement by the
  square of the same separator. -/
  operatorNormGap : forall
      {x : D.wilson.toGNSData.gnsComplete.hilbert.carrier},
    (selectedSpectralGapData D.measureLinked D.timeTranslation).vacPerp x ->
      RCle
        (D.wilson.toGNSData.gnsComplete.hilbert.cinner
          (D.timeTranslation.op.T x) (D.timeTranslation.op.T x))
        (RCscale
          ((selectedSpectralGapData D.measureLinked D.timeTranslation).gap.sep *
            (selectedSpectralGapData D.measureLinked D.timeTranslation).gap.sep)
          (D.wilson.toGNSData.gnsComplete.hilbert.cinner x x))

namespace WilsonBoundedMassGap

/-- Construct the same-object bounded mass-gap handoff from the exact-rate
witness and the minimal quadratic-form inequality. -/
def ofQuadraticFormGapPin
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonLinkedOSGNSData H)
    (E : WilsonPositiveExactLogGapWitness D)
    (Q : WilsonQuadraticFormGapPin D) : WilsonBoundedMassGap D where
  exactRate := E
  operatorNormGap := fun hx => Q.selectedOperatorNormGap hx

/-- Construct the same-object bounded mass-gap handoff from the exact-rate
witness and the single missing square Schur identity. -/
def ofCharacterSquarePin
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonLinkedOSGNSData H)
    (E : WilsonPositiveExactLogGapWitness D)
    {w t : Q'} {ht : (0 : Q') <= t} {N : Nat}
    {hw0 : (0 : Q') <= w} {hw1 : w < (1 : Q')}
    {B : WilsonLinkedOSGNSData.WilsonCharacterOS4Pin
      D.measureLinked D.timeTranslation ht N hw0 hw1}
    (S : WilsonCharacterSquarePin B) : WilsonBoundedMassGap D where
  exactRate := E
  operatorNormGap := fun hx =>
    (WilsonQuadraticFormGapPin.ofCharacterSquarePin D S).selectedOperatorNormGap hx

/-- The positive exact rate carried by the endpoint. -/
def rate
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonLinkedOSGNSData H}
    (G : WilsonBoundedMassGap D) : CReal :=
  G.exactRate.rate

/-- Constructive eventual positivity of the exact rate. -/
theorem rate_posEv
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonLinkedOSGNSData H}
    (G : WilsonBoundedMassGap D) : PosEv G.rate :=
  G.exactRate.rate_posEv

/-- The same endpoint retains the canonical, literally scaled form gap. -/
def canonicalFormGap
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonLinkedOSGNSData H}
    (G : WilsonBoundedMassGap D) :
    CanonicalTransferFormGap.CanonicalTransferFormGap
      (selectedSpectralGapData D.measureLinked D.timeTranslation) :=
  G.exactRate.selectedFormGap

/-- The endpoint's rate is computed from the exact logarithm of the
reconstruction separator, which is definitionally the selected concrete
Wilson separator. -/
theorem rate_equiv_selectedSeparatorExactLog
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonLinkedOSGNSData H}
    (G : WilsonBoundedMassGap D) :
    CReal.Equiv G.rate
      (OSExactLogGap.exactLogGap D.reconstruction
        G.exactRate.reconstructionGap.exactGap.positiveGapBound) :=
  G.exactRate.rate_equiv_selectedSeparatorExactLog

end WilsonBoundedMassGap

end YMGap.Continuum.WilsonBoundedMassGapHandoff

#print axioms YMGap.Continuum.WilsonBoundedMassGapHandoff.WilsonBoundedMassGap.ofCharacterSquarePin
#print axioms YMGap.Continuum.WilsonBoundedMassGapHandoff.WilsonBoundedMassGap.ofQuadraticFormGapPin
#print axioms YMGap.Continuum.WilsonBoundedMassGapHandoff.WilsonBoundedMassGap.rate_posEv
#print axioms YMGap.Continuum.WilsonBoundedMassGapHandoff.WilsonBoundedMassGap.canonicalFormGap
#print axioms YMGap.Continuum.WilsonBoundedMassGapHandoff.WilsonBoundedMassGap.rate_equiv_selectedSeparatorExactLog
