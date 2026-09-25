/-
# Relative-loss form on the completed complex Wilson carrier

The fixed-nome/width complex two-step form bound can be rewritten as an
explicit same-object deficit bound.  This is the concrete consumer shape
needed by the relative-loss bridge, but it remains a discrete fixed-parameter
statement; no scaling or continuum uniformity is asserted.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexGap

namespace YMGap.Continuum.BF4WilsonAllNomeComplexRelativeLoss

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeComplexGap
open YMGap.Continuum.BF4WilsonAllNomeComplexification
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap
  (twoStepRate twoStepRate_lt_one)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local infix:50 " ≈ " => Q'.eqv
local notation "VC" => ComplexCarrier hw0 hw1 width
local notation "I" => inner hw0 hw1 width
local notation "CT" => complexTime hw0 hw1 width
local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)

private theorem one_sub_mul (r a : Q') : (1 - r) * a ≈ a + -(r * a) :=
  Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 (-r) a)
    (Q'.add_eqv_congr' (Q'.one_mul_eqv a) (Q'.neg_mul_eqv r a))

private theorem deficit_lower (r : Q') (norm form : RC)
    (h : RCle form (RCmul (Rq r) norm)) :
    RCle (RCmul (Rq (1 - r)) norm) (RCsub norm form) := by
  revert h
  refine Quotient.inductionOn₂ norm form ?_
  intro N F h epsilon hepsilon
  obtain ⟨index, hN⟩ := h epsilon hepsilon
  refine ⟨index, fun n hn => ?_⟩
  have hf := hN n hn
  change F.approx n ≤ r * N.approx n + epsilon at hf
  have hneg := Q'.neg_le_neg_add hf
  have hsum := Q'.add_le_add_left (N.approx n) _ _ hneg
  change (1 - r) * N.approx n ≤ (N.approx n + -F.approx n) + epsilon
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (one_sub_mul r (N.approx n)))
    (Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv (Q'.add_assoc_eqv _ _ _)))

/-- The strict two-step bound pays the explicit fixed-parameter deficit. -/
theorem complex_twoStep_relative_loss (x : VC)
    (hx : I (complexUnit hw0 hw1 width) x = (RCzero, RCzero)) :
    RCle
      (RCscale (1 - twoStepRate hw0 hw1 width) (I x x).1)
      (RCsub (I x x).1 (I x (CT 2 x)).1) := by
  exact deficit_lower (twoStepRate hw0 hw1 width) (I x x).1
    (I x (CT 2 x)).1
    (complex_twoStep_form_gap hw0 hw1 width x hx)

theorem complex_twoStep_relative_loss_margin_positive :
    (0 : Q') < 1 - twoStepRate hw0 hw1 width :=
  ClusteringImpliesGap.sub_pos_of_lt (twoStepRate_lt_one hw0 hw1 width)

end YMGap.Continuum.BF4WilsonAllNomeComplexRelativeLoss

#print axioms YMGap.Continuum.BF4WilsonAllNomeComplexRelativeLoss.complex_twoStep_relative_loss
#print axioms YMGap.Continuum.BF4WilsonAllNomeComplexRelativeLoss.complex_twoStep_relative_loss_margin_positive
