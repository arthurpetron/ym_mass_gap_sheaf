/-
# A non-plaquette rectangle in the actual spatial Wilson-word family

The six original links form a closed SpatialLoop on the original extent-one
slab. Quaternion associativity and the terminal unit identify its right-fold
character with the existing original rectangle polynomial. Its already-proved
evaluations and pointwise plaquette-only nonrecoding therefore apply here.

This supplies a concrete non-plaquette input to the common temporal-ledger
theorem. It is not a proof of OS-norm or dynamical nondensity, nor an embedding
of this loop into the current plaquette-generated spatial union.
-/

import YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord
import YMGap.Continuum.SU2PlaquetteCharacterNonseparation

namespace YMGap.Continuum.BF4ExactSlabSpatialWilsonRectangle

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyPullback
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv
local infixl:70 " *q " => PolyQuaternion.mul

def rectangleEdges : List OrientedBF4Link :=
  [⟨((0,0,0,0), .x0), false⟩,
   ⟨((1,0,0,0), .x0), false⟩,
   ⟨((2,0,0,0), .x1), false⟩,
   ⟨((1,1,0,0), .x0), true⟩,
   ⟨((0,1,0,0), .x0), true⟩,
   ⟨((0,0,0,0), .x1), true⟩]

/-- A concrete physical closed spatial word, with no geometric premise left over. -/
def rectangle : SpatialLoop 1 0 where
  start := (0,0,0,0)
  edges := rectangleEdges
  compatible := by simp [Compatible, rectangleEdges, entryStart, entryFinish, addE]
  closed := rfl
  physical := by
    intro e he
    simp only [rectangleEdges, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  spatial := by
    intro e he
    simp only [rectangleEdges, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem six_right_to_left (a b c d e f : PolyQuaternion) :
    PolyQuaternionCoeffEqv (a *q (b *q (c *q (d *q (e *q (f *q PolyQuaternion.one))))))
      (((((a *q b) *q c) *q d) *q e) *q f) := by
  have hunit := (PolyQuaternionCoeffEqv.refl a).mul
    ((PolyQuaternionCoeffEqv.refl b).mul ((PolyQuaternionCoeffEqv.refl c).mul
      ((PolyQuaternionCoeffEqv.refl d).mul ((PolyQuaternionCoeffEqv.refl e).mul
        (PolyQuaternionCoeffEqv.mul_one f)))))
  exact hunit.trans
    ((PolyQuaternionCoeffEqv.mul_assoc a b (c *q (d *q (e *q f)))).symm.trans
      ((PolyQuaternionCoeffEqv.mul_assoc (a *q b) c (d *q (e *q f))).symm.trans
        ((PolyQuaternionCoeffEqv.mul_assoc ((a *q b) *q c) d (e *q f)).symm.trans
          (PolyQuaternionCoeffEqv.mul_assoc (((a *q b) *q c) *q d) e f).symm)))

-- The association proof needs the existing symbolic link values, not expansion
-- of the finite carrier search or of the quaternion polynomial arithmetic.
attribute [local irreducible] correctedSlabLinkPolynomial PolyQuaternion.mul
  PolyQuaternion.conj characterPolynomial

/-- Exact coefficient identity to the pre-existing original six-link polynomial. -/
theorem character_pin :
    RatPolyCoeffEqv (character 1 rectangle.edges 1)
      SU2PlaquetteCharacterNonseparation.rectanglePolynomial := by
  exact characterPolynomial_coeffEqv
    (six_right_to_left
      (correctedSlabLinkPolynomial 1 ((0,0,0,0), .x0))
      (correctedSlabLinkPolynomial 1 ((1,0,0,0), .x0))
      (correctedSlabLinkPolynomial 1 ((2,0,0,0), .x1))
      (PolyQuaternion.conj (correctedSlabLinkPolynomial 1 ((1,1,0,0), .x0)))
      (PolyQuaternion.conj (correctedSlabLinkPolynomial 1 ((0,1,0,0), .x0)))
      (PolyQuaternion.conj (correctedSlabLinkPolynomial 1 ((0,0,0,0), .x1)))).scalar 1

private theorem coeff_eval {p q : RatPoly} (h : RatPolyCoeffEqv p q) (rho : Nat → Q') :
    evalRatPoly rho p ≈ evalRatPoly rho q := by
  have pin : ∀ r : RatPoly, evalRatPoly rho r = ratWeightedSum (evalMono rho) r := by
    intro r
    induction r with
    | nil => rfl
    | cons t ts ih => simp only [evalRatPoly, ratWeightedSum, ih]
  rw [pin, pin]
  exact h _

/-- Existing unit-field values transported to the new actual spatial-loop object. -/
theorem rectangle_evaluation (alternate : Bool) :
    evalRatPoly (SU2PlaquetteCharacterNonseparation.fieldEnvironment 1
      (SU2PlaquetteCharacterNonseparation.field alternate)) (character 1 rectangle.edges 1) ≈
      (if alternate then 0 else -2) :=
  Q'.eqv_trans _ _ _ (coeff_eval character_pin _)
    (SU2PlaquetteCharacterNonseparation.rectangle_evaluation alternate)

/-- Pointwise obstruction only, for the explicitly named old plaquette algebra. -/
theorem no_pointwise_plaquette_recoding (e : PlaquetteExpression 0) :
    ¬ (∀ f : RationalUnitQuaternionGaugeField,
      evalRatPoly (SU2PlaquetteCharacterNonseparation.fieldEnvironment 1 f) (lower e) ≈
        evalRatPoly (SU2PlaquetteCharacterNonseparation.fieldEnvironment 1 f)
          (character 1 rectangle.edges 1)) := by
  intro h
  apply SU2PlaquetteCharacterNonseparation.no_pointwise_plaquette_recoding e
  intro f
  exact Q'.eqv_trans _ _ _ (h f) (coeff_eval character_pin _)

theorem no_coefficient_plaquette_recoding (e : PlaquetteExpression 0) :
    ¬ RatPolyCoeffEqv (lower e) (character 1 rectangle.edges 1) :=
  fun h => SU2PlaquetteCharacterNonseparation.no_coefficient_plaquette_recoding e
    (h.trans character_pin)

#print axioms rectangleEdges
#print axioms rectangle
#print axioms character_pin
#print axioms rectangle_evaluation
#print axioms no_pointwise_plaquette_recoding
#print axioms no_coefficient_plaquette_recoding

end YMGap.Continuum.BF4ExactSlabSpatialWilsonRectangle
