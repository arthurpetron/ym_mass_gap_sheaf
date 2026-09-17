/-
# Positive plaquette variance for the actual intrinsic Wilson reflected form

The witnessed original plaquette is an intrinsic radius-zero expression.
Its reflected square is the checked Wilson second moment. Pairing with the
intrinsic unit gives the checked first moment by coefficient-level removal
of the terminal polynomial unit on every original chart, not by identifying
the Cauchy moduli of different expressions.

The positive local-star variance floor therefore applies to the SAME
intrinsic form. This provides the scalar input for a separately constructed
completed centered vector; it constructs no such vector here and asserts no
completed-carrier embedding, strict bound, continuum passage or all-group
result. Nome, spacing and all original small-nome guards remain fixed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquetteMoments

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquetteForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquetteMoments (plaquetteExpression)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison (chartInsertion)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit (spatialLimit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialFunctionalLaws (spatialLimit_congr)
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

/-- The actual closed plaquette already used in the checked moment pins. -/
def plaquette {base : Nat} (face : Z4Plaq) (hf : face ∈ spatialFaces base) :
    IntrinsicExpression base where
  radius := 0
  expression := plaquetteExpression face hf
  within := Nat.le_refl 0

theorem plaquette_radius {base : Nat} (face : Z4Plaq) (hf : face ∈ spatialFaces base) :
    (plaquette face hf).radius = 0 := rfl

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
  {base : Nat} (hb : 0<base) (face : Z4Plaq) (hf : face ∈ spatialFaces base)

local notation "p" => plaquette face hf
local notation "e" => plaquetteExpression face hf
local notation "F" => intrinsicForm hw0 hw1 hsmall hd hs hb
local notation "mean" => spatialLimit hw0 hw1 0 e (Nat.le_refl 0) hsmall hd hs hb
local notation "second" => spatialLimit hw0 hw1 0 (WindowExpression.mul e e)
  (And.intro (Nat.le_refl 0) (Nat.le_refl 0)) hsmall hd hs hb

attribute [local irreducible] spatialLimit

/-- Radius zero fixes the literal plaquette under the actual time reflection. -/
theorem form_square_pin : Equiv (F p p) second := by
  change Equiv
    (spatialLimit hw0 hw1 0 (.mul e e) ⟨Nat.le_refl 0, Nat.le_refl 0⟩ hsmall hd hs hb)
    second
  exact Equiv.refl _

/-- The mean pin removes the polynomial unit on the SAME original chart. -/
theorem form_mean_pin : Equiv (F p (unit base)) mean := by
  change Equiv
    (spatialLimit hw0 hw1 0 (.mul e .one) ⟨Nat.le_refl 0, True.intro⟩ hsmall hd hs hb)
    mean
  apply spatialLimit_congr hw0 hw1 hsmall hd hs hb 0
    (.mul e .one) e ⟨Nat.le_refl 0, True.intro⟩ (Nat.le_refl 0)
  intro r t
  change RatPolyCoeffEqv (polyMul (chartInsertion r 0 t e) polyOne) (chartInsertion r 0 t e)
  exact RatPolyCoeffEqv.mul_one _

/-- Actual intrinsic-form variance equals the checked original Wilson scalar variance. -/
theorem form_variance_pin :
    Equiv (sub (F p p) (mul (F p (unit base)) (F p (unit base))))
      (sub second (mul mean mean)) := by
  have hm := form_mean_pin hw0 hw1 hsmall hd hs hb face hf
  exact Pivot2.add_congr (form_square_pin hw0 hw1 hsmall hd hs hb face hf)
    (CReal.neg_congr ((Pivot2.mul_congr_left hm).trans (Pivot2.mul_congr_right hm)))

/-- The original strictly positive local-star constant bounds THIS form variance. -/
theorem form_variance_floor :
    leEv (ofQ' (starRatio w))
      (sub (F p p) (mul (F p (unit base)) (F p (unit base)))) :=
  leEv_trans
    (BF4ExactSlabFixedSpatialWilsonPlaquetteMoments.variance_floor
      hw0 hw1 face hf hsmall hd hs hb)
    (leEv_of_equiv (form_variance_pin hw0 hw1 hsmall hd hs hb face hf).symm)

theorem form_variance_ne_zero :
    ¬ Equiv (sub (F p p) (mul (F p (unit base)) (F p (unit base)))) (ofQ' 0) :=
  fun hz => BF4ExactSlabFixedSpatialWilsonPlaquetteMoments.variance_ne_zero
    hw0 hw1 face hf hsmall hd hs hb
    ((form_variance_pin hw0 hw1 hsmall hd hs hb face hf).symm.trans hz)

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquetteForm

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquetteForm.plaquette
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquetteForm.plaquette_radius
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquetteForm.form_square_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquetteForm.form_mean_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquetteForm.form_variance_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquetteForm.form_variance_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquetteForm.form_variance_ne_zero
