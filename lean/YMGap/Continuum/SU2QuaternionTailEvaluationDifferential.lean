/-
# Differential operators commute with explicit tail evaluation

Evaluation of coordinates after a retained prefix commutes, coefficientwise,
with differentiation in that prefix.  In particular, retaining the first four
coordinates commutes with the head Laplacian and preserves the syntactic degree
of the head quaternion.  These are polynomial-algebra statements only; no Haar
or heat-kernel assertion is made here.
-/

import YMGap.Continuum.SU2QuaternionTailEvaluation

namespace YMGap.Continuum.SU2QuaternionTailEvaluationDifferential

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionTailEvaluation

local infix:50 " ≈ " => Q'.eqv

private theorem map_coeff {A : Type} (f g : A → RatTerm)
    (h : ∀ a, (f a).1 = (g a).1 ∧ (f a).2 ≈ (g a).2) :
    ∀ xs : List A, RatPolyCoeffEqv (xs.map f) (xs.map g)
  | [] => RatPolyCoeffEqv.refl _
  | a :: xs => by
      intro weight
      change (f a).2 * weight (f a).1 + ratWeightedSum weight (xs.map f) ≈
        (g a).2 * weight (g a).1 + ratWeightedSum weight (xs.map g)
      rw [(h a).1]
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ _ (h a).2)
        (map_coeff f g h xs weight)

private theorem exponent_take (monomial : List Nat) : ∀ keep coordinate,
    coordinate < keep →
      exponentAt (monomial.take keep) coordinate =
        exponentAt monomial coordinate
  | 0, _, h => by omega
  | keep + 1, 0, _ => by cases monomial <;> rfl
  | keep + 1, coordinate + 1, h => by
      cases monomial with
      | nil => rfl
      | cons _ rest => exact exponent_take rest keep coordinate (by omega)

private theorem lowerExponentAt_take (monomial : List Nat) : ∀ keep coordinate,
    coordinate < keep →
      lowerExponentAt coordinate (monomial.take keep) =
        (lowerExponentAt coordinate monomial).take keep
  | 0, _, h => by omega
  | keep + 1, 0, _ => by cases monomial <;> rfl
  | keep + 1, coordinate + 1, h => by
      cases monomial with
      | nil => rfl
      | cons exponent rest =>
          change exponent :: lowerExponentAt coordinate (rest.take keep) =
            exponent :: (lowerExponentAt coordinate rest).take keep
          rw [lowerExponentAt_take rest keep coordinate (by omega)]

private theorem lowerExponentAt_drop (monomial : List Nat) : ∀ keep coordinate,
    coordinate < keep →
      (lowerExponentAt coordinate monomial).drop keep = monomial.drop keep
  | 0, _, h => by omega
  | keep + 1, 0, _ => by cases monomial <;> rfl
  | keep + 1, coordinate + 1, h => by
      cases monomial with
      | nil => rfl
      | cons _ rest => exact lowerExponentAt_drop rest keep coordinate (by omega)

/-- Differentiation in a retained coordinate commutes coefficientwise with
explicit evaluation of every coordinate after the retained prefix. -/
theorem evaluate_derivative
    (keep : Nat) (rho : Nat → Q') (coordinate : Nat) (polynomial : RatPoly)
    (hcoordinate : coordinate < keep) :
    RatPolyCoeffEqv
      (evaluateTail keep rho (ratDerivative coordinate polynomial))
      (ratDerivative coordinate (evaluateTail keep rho polynomial)) := by
  simp only [evaluateTail, ratDerivative, List.map_map]
  apply map_coeff
  intro term
  constructor
  · exact (lowerExponentAt_take term.1 keep coordinate hcoordinate).symm
  · simp only [evaluateTerm, Function.comp_apply]
    rw [lowerExponentAt_drop term.1 keep coordinate hcoordinate,
      exponent_take term.1 keep coordinate hcoordinate]
    exact Q'.mul_assoc_eqv _ _ _

/-- Tail evaluation retaining the head quaternion commutes coefficientwise
with the four-coordinate head Laplacian. -/
theorem evaluate_headLaplacian
    (keep : Nat) (rho : Nat → Q') (hkeep : 4 ≤ keep)
    (polynomial : RatPoly) :
    RatPolyCoeffEqv
      (headLaplacian (evaluateTail keep rho polynomial))
      (evaluateTail keep rho (headLaplacian polynomial)) := by
  have hsecond : ∀ coordinate, coordinate < 4 →
      RatPolyCoeffEqv
        (evaluateTail keep rho
          (ratDerivative coordinate (ratDerivative coordinate polynomial)))
        (ratDerivative coordinate
          (ratDerivative coordinate (evaluateTail keep rho polynomial))) := by
    intro coordinate hcoordinate
    have hretained : coordinate < keep := Nat.lt_of_lt_of_le hcoordinate hkeep
    exact (evaluate_derivative keep rho coordinate
      (ratDerivative coordinate polynomial) hretained).trans
        ((evaluate_derivative keep rho coordinate polynomial hretained).derivative coordinate)
  unfold headLaplacian
  rw [evaluate_add, evaluate_add, evaluate_add]
  exact (RatPolyCoeffEqv.add (hsecond 0 (by omega))
    (RatPolyCoeffEqv.add (hsecond 1 (by omega))
      (RatPolyCoeffEqv.add (hsecond 2 (by omega))
        (hsecond 3 (by omega))))).symm

/-- Evaluating coordinates beyond a retained head quaternion preserves the
literal monomial degree in quaternion block zero. -/
theorem evaluate_headDegree
    (keep : Nat) (rho : Nat → Q') (hkeep : 4 ≤ keep)
    {degree : Nat} {polynomial : RatPoly}
    (hdegree : HasQuaternionBlockDegree 0 degree polynomial) :
    HasQuaternionBlockDegree 0 degree (evaluateTail keep rho polynomial) := by
  intro term hterm
  simp only [evaluateTail, List.mem_map] at hterm
  obtain ⟨source, hsource, rfl⟩ := hterm
  change quaternionBlockDegree (source.1.take keep) 0 = degree
  unfold quaternionBlockDegree
  simp only [Nat.mul_zero, Nat.zero_add]
  rw [exponent_take source.1 keep 0 (by omega),
    exponent_take source.1 keep 1 (by omega),
    exponent_take source.1 keep 2 (by omega),
    exponent_take source.1 keep 3 (by omega)]
  exact hdegree source hsource

end YMGap.Continuum.SU2QuaternionTailEvaluationDifferential

#print axioms YMGap.Continuum.SU2QuaternionTailEvaluationDifferential.evaluate_derivative
#print axioms YMGap.Continuum.SU2QuaternionTailEvaluationDifferential.evaluate_headLaplacian
#print axioms YMGap.Continuum.SU2QuaternionTailEvaluationDifferential.evaluate_headDegree
