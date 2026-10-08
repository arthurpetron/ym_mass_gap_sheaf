/-
# Three-column adapter for polynomial matrix envelopes

This is only a zero-padding adapter to the checked six-column square
completion. The unused coefficient slots are zero; their matrix entries are
filled with the genuine `(0,0)` entry so both required signs are inherited
without asking for a certificate for the envelope alone. Dummy vector slots
are represented by `cap 0`, hence vanish coefficientwise while retaining the
ordinary supported-polynomial interface.
-/

import YMGap.Continuum.QuaternionHaarSixPolynomialMatrixEnvelope
import YMGap.Continuum.QPolyHaarFrozenChain
import YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame
import YMGap.Continuum.SU2QuaternionPairedFrameScalarJets

namespace YMGap.Continuum.QuaternionHaarThreePolynomialMatrixEnvelope

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarSixPolynomialMatrixEnvelope
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (threeSum)
open YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame (threeSquare)

private def sixSlot (n : Nat) : Fin 6 := ⟨n % 6, Nat.mod_lt _ (by decide)⟩

private def threeSlot (n : Nat) : Fin 3 := ⟨n % 3, Nat.mod_lt _ (by decide)⟩

private def trimIndex (i : Fin 6) : Option (Fin 3) :=
  if h : i.val < 3 then some ⟨i.val, h⟩ else none

private def padVector (u : Fin 3 → RatPoly) : Fin 6 → RatPoly := fun i =>
  match trimIndex i with
  | some j => u j
  | none => cap 0

private def padMatrix (M : Fin 3 → Fin 3 → RatPoly) : Fin 6 → Fin 6 → RatPoly :=
  fun i j => match trimIndex i, trimIndex j with
    | some a, some b => M a b
    | _, _ => M ⟨0, by decide⟩ ⟨0, by decide⟩

/-- All nine ordered three-slot mixed entries are retained. -/
def quadraticForm (u : Fin 3 → RatPoly) (M : Fin 3 → Fin 3 → RatPoly) : RatPoly :=
  threeSum (fun i => threeSum (fun j =>
    polyMul (polyMul (u i) (u j)) (M i j)))

/-- The three-slot envelope with the unchanged six-column factor. -/
def matrixEnvelope (U : RatPoly) (u : Fin 3 → RatPoly)
    (M : Fin 3 → Fin 3 → RatPoly) : RatPoly :=
  polyAdd (polyMul (polyMul (cap 6) U) (threeSquare u)) (quadraticForm u M)

private def exprSix (f : Fin 6 → PolyExpr) : PolyExpr :=
  .add (f (sixSlot 0)) (.add (f (sixSlot 1)) (.add (f (sixSlot 2))
    (.add (f (sixSlot 3)) (.add (f (sixSlot 4)) (f (sixSlot 5))))))

private def exprThree (f : Fin 3 → PolyExpr) : PolyExpr :=
  .add (f (threeSlot 0)) (.add (f (threeSlot 1)) (f (threeSlot 2)))

private def paddedVectorExpr (i : Fin 6) : PolyExpr :=
  if i.val < 3 then .var (1 + i.val) else .const 0

private def paddedEntryExpr (i j : Fin 6) : PolyExpr :=
  if i.val < 3 then
    if j.val < 3 then .var (4 + 3 * i.val + j.val) else .var 4
  else .var 4

private def sixEnvelopeExpr : PolyExpr :=
  .add
    (.mul (.mul (.const 6) (.var 0))
      (exprSix (fun i => .mul (paddedVectorExpr i) (paddedVectorExpr i))))
    (exprSix (fun i => exprSix (fun j =>
      .mul (.mul (paddedVectorExpr i) (paddedVectorExpr j)) (paddedEntryExpr i j))))

private def threeEnvelopeExpr : PolyExpr :=
  .add
    (.mul (.mul (.const 6) (.var 0))
      (exprThree (fun i => .mul (.var (1 + i.val)) (.var (1 + i.val)))))
    (exprThree (fun i => exprThree (fun j =>
      .mul (.mul (.var (1 + i.val)) (.var (1 + j.val)))
        (.var (4 + 3 * i.val + j.val)))))

private theorem padded_envelope_pin (U : RatPoly) (u : Fin 3 → RatPoly)
    (M : Fin 3 → Fin 3 → RatPoly) :
    RatPolyCoeffEqv
      (YMGap.Continuum.QuaternionHaarSixPolynomialMatrixEnvelope.matrixEnvelope
        U (padVector u) (padMatrix M))
      (matrixEnvelope U u M) := by
  let environment : Nat → RatPoly
    | 0 => U
    | 1 => u 0
    | 2 => u 1
    | 3 => u 2
    | 4 => M 0 0
    | 5 => M 0 1
    | 6 => M 0 2
    | 7 => M 1 0
    | 8 => M 1 1
    | 9 => M 1 2
    | 10 => M 2 0
    | 11 => M 2 1
    | 12 => M 2 2
    | _ => polyZero
  have h := coeffEvalExpr_eqv_of_normalize_eq sixEnvelopeExpr threeEnvelopeExpr
    (by decide) environment
  simpa only [sixEnvelopeExpr, threeEnvelopeExpr, exprSix, exprThree,
    paddedVectorExpr, paddedEntryExpr, environment, coeffEvalExpr,
    YMGap.Continuum.QuaternionHaarSixPolynomialMatrixEnvelope.matrixEnvelope,
    matrixEnvelope, quadraticForm, threeSquare, threeSum,
    YMGap.Continuum.QuaternionHaarSixPolynomialMatrixEnvelope.squareSum,
    YMGap.Continuum.QuaternionHaarSixPolynomialMatrixEnvelope.sixSum,
    cap, padVector, padMatrix, trimIndex, sixSlot, threeSlot] using h

/-- Extend support through the three real slots and coefficientwise-zero
remaining slots. -/
private theorem padded_support {blocks : Nat} (u : Fin 3 → RatPoly)
    (hu : ∀ i, SupportedQuaternionBlocks blocks (u i)) :
    ∀ i, SupportedQuaternionBlocks blocks (padVector u i) := by
  intro i term ht
  cases h : trimIndex i with
  | some j =>
      have ht' : term ∈ u j := by simpa only [padVector, h] using ht
      exact hu j term ht'
  | none =>
      have hs : SupportedQuaternionBlocks blocks (cap 0) := by
        intro t ht0
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht0
        exact supported_one blocks s hs
      have ht' : term ∈ cap 0 := by simpa only [padVector, h] using ht
      exact hs term ht'

/-- Three-polynomial matrix envelope certificate, obtained by zero-padding
the actual coefficient vector and reusing the six-slot certificate. -/
def three_polynomial_matrix_envelope_certificate {blocks : Nat}
    (U : RatPoly) (u : Fin 3 → RatPoly) (M : Fin 3 → Fin 3 → RatPoly)
    (hu : ∀ i, SupportedQuaternionBlocks blocks (u i))
    (P : ∀ i j, Certificate blocks (polyAdd U (M i j)))
    (N : ∀ i j, Certificate blocks (polyAdd U (polyNeg (M i j)))) :
    Certificate blocks (matrixEnvelope U u M) := by
  let u6 := padVector u
  let M6 := padMatrix M
  have P6 : ∀ i j, Certificate blocks (polyAdd U (M6 i j)) := by
    intro i j
    cases hi : trimIndex i with
    | none => cases hj : trimIndex j <;> simpa [M6, padMatrix, hi, hj] using P 0 0
    | some a =>
      cases hj : trimIndex j with
      | none => simpa [M6, padMatrix, hi, hj] using P 0 0
      | some b => simpa [M6, padMatrix, hi, hj] using P a b
  have N6 : ∀ i j, Certificate blocks (polyAdd U (polyNeg (M6 i j))) := by
    intro i j
    cases hi : trimIndex i with
    | none => cases hj : trimIndex j <;> simpa [M6, padMatrix, hi, hj] using N 0 0
    | some a =>
      cases hj : trimIndex j with
      | none => simpa [M6, padMatrix, hi, hj] using N 0 0
      | some b => simpa [M6, padMatrix, hi, hj] using N a b
  have h6 := six_polynomial_matrix_envelope_certificate U u6 M6
    (padded_support u hu) P6 N6
  exact Certificate.ofCoeff (padded_envelope_pin U u M).symm h6

end YMGap.Continuum.QuaternionHaarThreePolynomialMatrixEnvelope

#print axioms YMGap.Continuum.QuaternionHaarThreePolynomialMatrixEnvelope.three_polynomial_matrix_envelope_certificate
