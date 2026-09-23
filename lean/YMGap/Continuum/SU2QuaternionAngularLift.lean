/-
# Angular differentiation through quaternion boundary lifts

Prepending `n` quaternion blocks shifts every original coordinate by `4*n`.
Formal differentiation and the tangential angular vector fields respect this
shift exactly.  These are finite list identities, with no Haar, support, or
positivity assumptions.
-/

import YMGap.Continuum.SU2QuaternionAngularDerivative
import YMGap.Continuum.SU2QuaternionCoordinateColumnLift

namespace YMGap.Continuum.SU2QuaternionAngularLift

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionCoordinateColumnLift

private theorem ratDerivative_liftHead (coordinate : Nat) (polynomial : RatPoly) :
    ratDerivative (4 + coordinate) (liftHead polynomial) =
      liftHead (ratDerivative coordinate polynomial) := by
  simp only [ratDerivative, liftHead, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro term _
  cases term with
  | mk monomial coefficient =>
      rw [Nat.add_comm 4 coordinate]
      rfl

/-- Differentiating a lifted polynomial in the corresponding shifted
coordinate is coefficientwise the lift of the original derivative. -/
theorem ratDerivative_liftBoundary (n coordinate : Nat) (polynomial : RatPoly) :
    RatPolyCoeffEqv
      (ratDerivative (4 * n + coordinate) (liftBoundary n polynomial))
      (liftBoundary n (ratDerivative coordinate polynomial)) := by
  have heq : ratDerivative (4 * n + coordinate) (liftBoundary n polynomial) =
      liftBoundary n (ratDerivative coordinate polynomial) := by
    induction n with
    | zero => simp only [Nat.mul_zero, Nat.zero_add, liftBoundary]
    | succ n ih =>
        rw [liftBoundary]
        rw [show 4 * (n + 1) + coordinate = 4 + (4 * n + coordinate) by omega]
        rw [ratDerivative_liftHead, ih, liftBoundary]
  rw [heq]
  exact RatPolyCoeffEqv.refl _

/-- Angular differentiation commutes with a quaternion boundary lift after
shifting both coordinate indices past the prepended blocks. -/
theorem angularDerivative_liftBoundary (n i j : Nat) (polynomial : RatPoly) :
    RatPolyCoeffEqv
      (angularDerivative (4 * n + i) (4 * n + j)
        (liftBoundary n polynomial))
      (liftBoundary n (angularDerivative i j polynomial)) := by
  unfold angularDerivative
  refine (((ratDerivative_liftBoundary n j polynomial).mul_left
      (polyVar (4 * n + i))).add
    (((ratDerivative_liftBoundary n i polynomial).mul_left
      (polyVar (4 * n + j))).smul (-1))).trans ?_
  rw [← lift_var n i, ← lift_var n j,
    ← lift_product, ← lift_product, ← lift_smul, ← lift_add]
  exact RatPolyCoeffEqv.refl _

end YMGap.Continuum.SU2QuaternionAngularLift

#print axioms YMGap.Continuum.SU2QuaternionAngularLift.ratDerivative_liftBoundary
#print axioms YMGap.Continuum.SU2QuaternionAngularLift.angularDerivative_liftBoundary
