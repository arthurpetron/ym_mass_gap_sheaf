/-
# ORIGINAL time-separated connected correlations in one explicit finite stage

Padding n and time lags s,t in {0,...,n} are separate arguments. Each lag
is realized by the actual displaced plaquette expression, and all three
expectations use ONE original slab functional and ONE partition reciprocal.
The represented centered states lie in that stage's existing completion;
their pairing is exactly the returned connected correlation, with QCauchy
data. Reflection symmetry, diagonal positivity and sharp Cauchy--Schwarz
are unconditional at every rational 0<w<1.

Geometric reflected separation grows by s+t, but no equality of correlations
at equal s+t is asserted: finite boundaries and padding still matter. No
limit in padding, inter-stage isometry, transfer-power identification,
stationary vacuum or decay estimate is supplied. At padding and lags zero,
the previous strictly positive original plaquette covariance is recovered.
Spatial coordinates are not shifted: this time embedding alone is not a
bulk-centered four-dimensional exhaustion.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteTimeEmbedding
import YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCenteredNontriviality

namespace YMGap.Continuum.BF4ExactSlabPlaquetteTimeCorrelations

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteTimeEmbedding
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedInner
open YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion
open YMGap.Continuum.BF4ExactSlabPlaquetteCenteredDensity
open YMGap.Continuum.BF4ExactSlabPlaquetteConnectedCovariance
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
open YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels

def atTime {half : Nat} (padding : Nat) (s : Fin (padding+1)) (e : PlaquetteExpression half) :
    PlaquetteExpression (half+padding) := displaced padding s.val (by have h := s.isLt; omega) e

def lowerAt {half : Nat} (padding : Nat) (s : Fin (padding+1)) (e : PlaquetteExpression half) : RatPoly :=
  evaluate (fun id spin => characterPolynomial (correctedSlabPlaquettePolynomial (centralExtent (half+padding))
    (timeShiftPlaquette (padding-s.val) (slabPlaquetteAt (centralExtent half) id))).scalar spin) e

def upperAt {half : Nat} (padding : Nat) (s : Fin (padding+1)) (e : PlaquetteExpression half) : RatPoly :=
  evaluate (fun id spin => characterPolynomial (correctedSlabPlaquettePolynomial (centralExtent (half+padding))
    (timeShiftPlaquette (padding+s.val) (timeReflectPlaquette (centralExtent half)
      (slabPlaquetteAt (centralExtent half) id)))).scalar spin) e

theorem lowerAt_pin {half : Nat} (padding : Nat) (s : Fin (padding+1)) (e : PlaquetteExpression half) :
    lower (atTime padding s e) = lowerAt padding s e :=
  lower_translate padding (padding-s.val) (Nat.sub_le padding s.val) e

theorem upperAt_pin {half : Nat} (padding : Nat) (s : Fin (padding+1)) (e : PlaquetteExpression half) :
    upper (atTime padding s e) = upperAt padding s e :=
  upper_displaced padding s.val (by have h := s.isLt; omega) e

theorem atTime_zero {half : Nat} (e : PlaquetteExpression half) : atTime 0 ⟨0, by omega⟩ e = e :=
  translate_zero e

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {half : Nat}

def correlation (padding : Nat) (s t : Fin (padding+1)) (e f : PlaquetteExpression half) : CReal :=
  connectedCovariance w hw0 hw1 (atTime padding s e) (atTime padding t f)

def correlationCauchy (padding : Nat) (s t : Fin (padding+1)) (e f : PlaquetteExpression half) :
    QCauchy (correlation w hw0 hw1 padding s t e f).approx :=
  connectedCovarianceCauchy w hw0 hw1 (atTime padding s e) (atTime padding t f)

/-- The literal time-separated polynomial moments, all under the same
original finite-stage probability functional after representation-cutoff removal. -/
theorem correlation_formula (padding : Nat) (s t : Fin (padding+1)) (e f : PlaquetteExpression half) :
    Equiv (correlation w hw0 hw1 padding s t e f)
      (CReal.sub (expectation w hw0 hw1 (half+padding) (polyMul (upperAt padding s e) (lowerAt padding t f)))
        (CReal.mul (expectation w hw0 hw1 (half+padding) (lowerAt padding s e))
          (expectation w hw0 hw1 (half+padding) (lowerAt padding t f)))) := by
  have h := CReal.sub_congr_left
    (y := CReal.mul (mean w hw0 hw1 (atTime padding s e)) (mean w hw0 hw1 (atTime padding t f)))
    (form_reflected w hw0 hw1 (atTime padding s e) (atTime padding t f)).symm
  change Equiv (correlation w hw0 hw1 padding s t e f) _ at h
  simpa only [form, mean, lowerAt_pin, upperAt_pin] using h

def point (padding : Nat) (s : Fin (padding+1)) (e : PlaquetteExpression half) :
    UnitComplement w hw0 hw1 (half+padding) := centeredExpression w hw0 hw1 (atTime padding s e)

theorem correlation_pairing (padding : Nat) (s t : Fin (padding+1)) (e f : PlaquetteExpression half) :
    completedInner w hw0 hw1 (point w hw0 hw1 padding s e).val (point w hw0 hw1 padding t f).val =
      Quotient.mk crealSetoid (correlation w hw0 hw1 padding s t e f) :=
  connectedCovariance_pairing w hw0 hw1 (atTime padding s e) (atTime padding t f)

theorem correlation_symm (padding : Nat) (s t : Fin (padding+1)) (e f : PlaquetteExpression half) :
    Equiv (correlation w hw0 hw1 padding s t e f) (correlation w hw0 hw1 padding t s f e) :=
  connectedCovariance_symm w hw0 hw1 (atTime padding s e) (atTime padding t f)

theorem correlation_nonnegative (padding : Nat) (s : Fin (padding+1)) (e : PlaquetteExpression half) :
    leEv czero (correlation w hw0 hw1 padding s s e e) :=
  connectedCovariance_nonnegative w hw0 hw1 (atTime padding s e)

theorem correlation_cauchySchwarz (padding : Nat) (s t : Fin (padding+1)) (e f : PlaquetteExpression half) :
    leEv (CReal.mul (correlation w hw0 hw1 padding s t e f) (correlation w hw0 hw1 padding s t e f))
      (CReal.mul (correlation w hw0 hw1 padding s s e e) (correlation w hw0 hw1 padding t t f f)) :=
  connectedCovariance_cauchySchwarz w hw0 hw1 (atTime padding s e) (atTime padding t f)

theorem correlation_zero (e f : PlaquetteExpression half) :
    correlation w hw0 hw1 0 ⟨0, by omega⟩ ⟨0, by omega⟩ e f = connectedCovariance w hw0 hw1 e f := by
  unfold correlation
  rw [atTime_zero, atTime_zero]

/-- The original positive seed remains literally the zero-padding member.
No positive lower bound at later padding or nonzero lag is claimed. -/
theorem probe_zero_floor :
    leEv (ofQ' BF4ExactSlabPlaquetteSmallNomeCenteredNontriviality.normalizedFloor)
      (correlation nome nome_pos nome_lt_one 0 ⟨0, by omega⟩ ⟨0, by omega⟩ probe probe) := by
  rw [correlation_zero]
  exact BF4ExactSlabPlaquetteSmallNomeCenteredNontriviality.connectedCovariance_floor

end YMGap.Continuum.BF4ExactSlabPlaquetteTimeCorrelations

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteTimeCorrelations.atTime
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteTimeCorrelations.lowerAt
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteTimeCorrelations.upperAt
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteTimeCorrelations.lowerAt_pin
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteTimeCorrelations.upperAt_pin
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteTimeCorrelations.atTime_zero
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteTimeCorrelations.correlation
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteTimeCorrelations.correlationCauchy
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteTimeCorrelations.correlation_formula
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteTimeCorrelations.point
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteTimeCorrelations.correlation_pairing
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteTimeCorrelations.correlation_symm
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteTimeCorrelations.correlation_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteTimeCorrelations.correlation_cauchySchwarz
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteTimeCorrelations.correlation_zero
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteTimeCorrelations.probe_zero_floor
