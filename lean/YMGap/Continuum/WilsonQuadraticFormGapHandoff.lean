/-
M4m -- isolate the minimal quadratic-form input needed to upgrade the selected
Wilson linear form gap to a bounded transfer-operator norm gap.

The exact square Schur resolution in `WilsonOperatorNormGapHandoff` is one
sufficient route, but it is stronger than the final argument needs.  Once the
selected canonical linear form gap is known, the only extra inequality is

  <T^2 x,x> <= sep * <T x,x>

on the selected vacuum complement.  Self-adjointness then identifies the left
side with `||T x||^2`, and scalar monotonicity composes the inequality with the
linear form gap.

No continuum datum or quadratic-form pin is constructed here.
-/

import YMGap.Continuum.WilsonOperatorNormGapHandoff

namespace YMGap.Continuum.WilsonQuadraticFormGapHandoff

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.BoundedTransferCalculus
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.MeasureLinkedOSReconstruction
open YMGap.Continuum.WilsonLinkedOSReconstruction
open YMGap.Continuum.WilsonOperatorNormGapHandoff

/-- The minimal extra spectral-order statement beyond the already-selected
canonical linear form gap. -/
structure WilsonQuadraticFormGapPin
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonLinkedOSGNSData H) : Type 2 where
  squareFormGap : forall
      {x : D.wilson.toGNSData.gnsComplete.hilbert.carrier},
    (selectedSpectralGapData D.measureLinked D.timeTranslation).vacPerp x ->
      RCle
        (D.wilson.toGNSData.gnsComplete.hilbert.cinner
          (D.timeTranslation.op.T (D.timeTranslation.op.T x)) x)
        (RCscale
          (selectedSpectralGapData D.measureLinked D.timeTranslation).gap.sep
          (D.wilson.toGNSData.gnsComplete.hilbert.cinner
            (D.timeTranslation.op.T x) x))

namespace WilsonQuadraticFormGapPin

/-- The exact square Schur identity supplies the weaker quadratic-form pin. -/
def ofCharacterSquarePin
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonLinkedOSGNSData H)
    {w t : Q'} {ht : (0 : Q') <= t} {N : Nat}
    {hw0 : (0 : Q') <= w} {hw1 : w < (1 : Q')}
    {B : WilsonLinkedOSGNSData.WilsonCharacterOS4Pin
      D.measureLinked D.timeTranslation ht N hw0 hw1}
    (S : WilsonCharacterSquarePin B) : WilsonQuadraticFormGapPin D where
  squareFormGap := fun hx =>
    BoundedTransferCalculus.squareFormGap S.toSelectedDiagResolution hx

/-- The genuine bounded-operator gap follows from the minimal quadratic-form
pin and the selected canonical linear form gap. -/
theorem selectedOperatorNormGap
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonLinkedOSGNSData H}
    (Q : WilsonQuadraticFormGapPin D)
    {x : D.wilson.toGNSData.gnsComplete.hilbert.carrier}
    (hx : (selectedSpectralGapData D.measureLinked D.timeTranslation).vacPerp x) :
    RCle
      (D.wilson.toGNSData.gnsComplete.hilbert.cinner
        (D.timeTranslation.op.T x) (D.timeTranslation.op.T x))
      (RCscale
        ((selectedSpectralGapData D.measureLinked D.timeTranslation).gap.sep *
          (selectedSpectralGapData D.measureLinked D.timeTranslation).gap.sep)
        (D.wilson.toGNSData.gnsComplete.hilbert.cinner x x)) := by
  have hsa :
      D.wilson.toGNSData.gnsComplete.hilbert.cinner
          (D.timeTranslation.op.T x) (D.timeTranslation.op.T x) =
        D.wilson.toGNSData.gnsComplete.hilbert.cinner
          (D.timeTranslation.op.T (D.timeTranslation.op.T x)) x :=
    (D.timeTranslation.op.selfAdjoint (D.timeTranslation.op.T x) x).symm
  rw [hsa]
  refine RCle_trans (Q.squareFormGap hx) ?_
  have hlinear := D.reconstructionCanonicalFormGap.form_gap hx
  have hscaled := RCscale_mono
    (selectedSpectralGapData D.measureLinked D.timeTranslation).gap.sep_nonneg
    hlinear
  refine RCle_trans hscaled ?_
  rw [RCscale_RCscale]
  exact RCle_refl _

end WilsonQuadraticFormGapPin

end YMGap.Continuum.WilsonQuadraticFormGapHandoff

#print axioms YMGap.Continuum.WilsonQuadraticFormGapHandoff.WilsonQuadraticFormGapPin.ofCharacterSquarePin
#print axioms YMGap.Continuum.WilsonQuadraticFormGapHandoff.WilsonQuadraticFormGapPin.selectedOperatorNormGap
