/-
# Bulk-centered ORIGINAL plaquette observables and correlations

This places space and time in the interior of the enlarged slab. The lag is
independent of padding and is bounded explicitly. Polynomial evaluation is
pinned to the actual shifted faces, including the reflected upper shift.
The connected correlation uses the existing original action and completed
centered pairing, with explicit cutoff-limit Cauchy data. No convergence in
padding or boundary-insensitivity estimate is assumed.
-/

import YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
import YMGap.Continuum.BF4ExactSlabPlaquetteTimeCorrelations

namespace YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabTimeEmbeddingGeometry
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
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

def bulkFaceId (half padding lag id : Nat) : Nat :=
  shiftFaceId (centralExtent half) (centralExtent (half+padding)) padding (padding-lag) id

theorem bulkFaceId_physical {half padding lag id : Nat} (hi : id ∈ slabPhysicalFaceEdges (centralExtent half)) :
    bulkFaceId half padding lag id ∈ slabPhysicalFaceEdges (centralExtent (half+padding)) :=
  shiftFaceId_physical (central_room (by omega)) (central_room (by omega)) hi

theorem bulkFaceId_pin {half padding lag id : Nat} (hi : id ∈ slabPhysicalFaceEdges (centralExtent half)) :
    slabPlaquetteAt (centralExtent (half+padding)) (bulkFaceId half padding lag id) =
      shiftFace padding (padding-lag) (slabPlaquetteAt (centralExtent half) id) :=
  shiftFaceId_pin (central_room (by omega)) (central_room (by omega)) hi

theorem bulkFaceId_lower {half padding lag id : Nat} (hi : id ∈ centralLowerFaceIds half) :
    bulkFaceId half padding lag id ∈ centralLowerFaceIds (half+padding) := by
  apply mem_centralLowerFaceIds.mpr
  refine ⟨bulkFaceId_physical (mem_centralLowerFaceIds.mp hi).1, ?_⟩
  rw [bulkFaceId_pin (mem_centralLowerFaceIds.mp hi).1]
  exact shiftFace_lower (Nat.sub_le padding lag) (mem_centralLowerFaceIds.mp hi).2

/-- A structural map on the existing expression carrier; physical membership
is supplied by the proved bulk-coordinate theorem, not a new algebra. -/
def bulkAtTime {half : Nat} (padding : Nat) (s : Fin (padding+1)) : PlaquetteExpression half → PlaquetteExpression (half+padding)
  | .unit => .unit
  | .character id hi spin => .character (bulkFaceId half padding s.val id) (bulkFaceId_lower hi) spin
  | .add e f => .add (bulkAtTime padding s e) (bulkAtTime padding s f)
  | .mul e f => .mul (bulkAtTime padding s e) (bulkAtTime padding s f)
  | .smul c e => .smul c (bulkAtTime padding s e)

private theorem congrTwo {A B C : Type} (f : A → B → C) {a a' : A} {b b' : B}
    (ha : a = a') (hb : b = b') : f a b = f a' b' := by
  cases ha
  cases hb
  rfl

theorem evaluate_bulkAtTime {half : Nat} (padding : Nat) (s : Fin (padding+1)) (f : Nat → Nat → RatPoly) :
    ∀ e : PlaquetteExpression half, evaluate f (bulkAtTime padding s e) =
      evaluate (fun id spin => f (bulkFaceId half padding s.val id) spin) e
  | .unit => rfl
  | .character _ _ _ => rfl
  | .add e g => congrTwo polyAdd (evaluate_bulkAtTime padding s f e) (evaluate_bulkAtTime padding s f g)
  | .mul e g => congrTwo polyMul (evaluate_bulkAtTime padding s f e) (evaluate_bulkAtTime padding s f g)
  | .smul c e => congrArg (polySmul c) (evaluate_bulkAtTime padding s f e)

def bulkLower {half : Nat} (padding : Nat) (s : Fin (padding+1)) (e : PlaquetteExpression half) : RatPoly :=
  evaluate (fun id spin => characterPolynomial (correctedSlabPlaquettePolynomial (centralExtent (half+padding))
    (shiftFace padding (padding-s.val) (slabPlaquetteAt (centralExtent half) id))).scalar spin) e

def bulkUpper {half : Nat} (padding : Nat) (s : Fin (padding+1)) (e : PlaquetteExpression half) : RatPoly :=
  evaluate (fun id spin => characterPolynomial (correctedSlabPlaquettePolynomial (centralExtent (half+padding))
    (shiftFace padding (padding+s.val) (timeReflectPlaquette (centralExtent half)
      (slabPlaquetteAt (centralExtent half) id)))).scalar spin) e

theorem bulkLower_pin {half : Nat} (padding : Nat) (s : Fin (padding+1)) (e : PlaquetteExpression half) :
    lower (bulkAtTime padding s e) = bulkLower padding s e := by
  unfold lower bulkLower
  rw [evaluate_bulkAtTime]
  apply evaluate_congr
  intro id hi spin
  exact congrArg (fun p => characterPolynomial (correctedSlabPlaquettePolynomial (centralExtent (half+padding)) p).scalar spin)
    (bulkFaceId_pin (mem_centralLowerFaceIds.mp hi).1)

theorem bulkUpper_pin {half : Nat} (padding : Nat) (s : Fin (padding+1)) (e : PlaquetteExpression half) :
    upper (bulkAtTime padding s e) = bulkUpper padding s e := by
  unfold upper bulkUpper
  rw [evaluate_bulkAtTime]
  apply evaluate_congr
  intro id hi spin
  apply congrArg (fun p => characterPolynomial (correctedSlabPlaquettePolynomial (centralExtent (half+padding)) p).scalar spin)
  have hp := (mem_centralLowerFaceIds.mp hi).1
  rw [slabPlaquetteAt_slabFaceReflectId (bulkFaceId_physical hp), bulkFaceId_pin hp,
    shiftFace_reflection (show padding-s.val ≤ padding+padding by omega)
      ((mem_boundaryCompleteSlabPlaquettes _ _).mp (slabPlaquetteAt_mem hp)).2]
  have hs := s.isLt
  rw [show padding+padding-(padding-s.val) = padding+s.val by omega]

theorem bulkAtTime_zero {half : Nat} : ∀ e : PlaquetteExpression half, bulkAtTime 0 ⟨0, by omega⟩ e = e
  | .unit => rfl
  | .character id hi spin => by
      simp only [bulkAtTime, bulkFaceId, Nat.add_zero, Nat.sub_self,
        shiftFaceId_zero (mem_centralLowerFaceIds.mp hi).1]
  | .add e f => congrTwo PlaquetteExpression.add (bulkAtTime_zero e) (bulkAtTime_zero f)
  | .mul e f => congrTwo PlaquetteExpression.mul (bulkAtTime_zero e) (bulkAtTime_zero f)
  | .smul c e => congrArg (PlaquetteExpression.smul c) (bulkAtTime_zero e)

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {half : Nat}

def bulkCorrelation (padding : Nat) (s t : Fin (padding+1)) (e f : PlaquetteExpression half) : CReal :=
  connectedCovariance w hw0 hw1 (bulkAtTime padding s e) (bulkAtTime padding t f)

def bulkCorrelationCauchy (padding : Nat) (s t : Fin (padding+1)) (e f : PlaquetteExpression half) :
    QCauchy (bulkCorrelation w hw0 hw1 padding s t e f).approx :=
  connectedCovarianceCauchy w hw0 hw1 (bulkAtTime padding s e) (bulkAtTime padding t f)

theorem bulkCorrelation_formula (padding : Nat) (s t : Fin (padding+1)) (e f : PlaquetteExpression half) :
    Equiv (bulkCorrelation w hw0 hw1 padding s t e f)
      (CReal.sub (expectation w hw0 hw1 (half+padding) (polyMul (bulkUpper padding s e) (bulkLower padding t f)))
        (CReal.mul (expectation w hw0 hw1 (half+padding) (bulkLower padding s e))
          (expectation w hw0 hw1 (half+padding) (bulkLower padding t f)))) := by
  have h := CReal.sub_congr_left
    (y := CReal.mul (mean w hw0 hw1 (bulkAtTime padding s e)) (mean w hw0 hw1 (bulkAtTime padding t f)))
    (form_reflected w hw0 hw1 (bulkAtTime padding s e) (bulkAtTime padding t f)).symm
  change Equiv (bulkCorrelation w hw0 hw1 padding s t e f) _ at h
  simpa only [form, mean, bulkLower_pin, bulkUpper_pin] using h

def bulkPoint (padding : Nat) (s : Fin (padding+1)) (e : PlaquetteExpression half) :
    UnitComplement w hw0 hw1 (half+padding) := centeredExpression w hw0 hw1 (bulkAtTime padding s e)

theorem bulkCorrelation_pairing (padding : Nat) (s t : Fin (padding+1)) (e f : PlaquetteExpression half) :
    completedInner w hw0 hw1 (bulkPoint w hw0 hw1 padding s e).val (bulkPoint w hw0 hw1 padding t f).val =
      Quotient.mk crealSetoid (bulkCorrelation w hw0 hw1 padding s t e f) :=
  connectedCovariance_pairing w hw0 hw1 (bulkAtTime padding s e) (bulkAtTime padding t f)

theorem bulkCorrelation_zero (e f : PlaquetteExpression half) :
    bulkCorrelation w hw0 hw1 0 ⟨0, by omega⟩ ⟨0, by omega⟩ e f = connectedCovariance w hw0 hw1 e f := by
  unfold bulkCorrelation
  rw [bulkAtTime_zero, bulkAtTime_zero]

theorem bulk_probe_zero_floor :
    leEv (ofQ' BF4ExactSlabPlaquetteSmallNomeCenteredNontriviality.normalizedFloor)
      (bulkCorrelation nome nome_pos nome_lt_one 0 ⟨0, by omega⟩ ⟨0, by omega⟩ probe probe) := by
  rw [bulkCorrelation_zero]
  exact BF4ExactSlabPlaquetteSmallNomeCenteredNontriviality.connectedCovariance_floor

end YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding.bulkFaceId
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding.bulkFaceId_physical
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding.bulkFaceId_pin
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding.bulkFaceId_lower
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding.bulkAtTime
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding.evaluate_bulkAtTime
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding.bulkLower
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding.bulkUpper
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding.bulkLower_pin
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding.bulkUpper_pin
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding.bulkAtTime_zero
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding.bulkCorrelation
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding.bulkCorrelationCauchy
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding.bulkCorrelation_formula
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding.bulkPoint
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding.bulkCorrelation_pairing
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding.bulkCorrelation_zero
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding.bulk_probe_zero_floor
