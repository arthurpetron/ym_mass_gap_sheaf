/-
# Orthogonal centering on the ORIGINAL completed plaquette space

Subtract the constructed rank-one projection onto the SAME original unit.
The resulting map is self-adjoint, idempotent, linear and nonexpansive.
Its mixed pairing is the original connected reflected covariance; the
orthogonal decomposition gives a Pythagorean norm identity with no loss.

This constructs the unit complement, not a stationary physical vacuum,
a physical time operator, a nonzero excitation or a strict gap estimate.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteUnitProjection

namespace YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient
open YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedInner
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedBilinear
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedGeometry
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedRealScalar
open YMGap.Continuum.BF4ExactSlabPlaquetteUnitProjection

private theorem rc_negative_one (a : RC) : RCmul (Quotient.mk crealSetoid (ofQ' (-1))) a = RCneg a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 (A.approx n)) (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv (A.approx n)))))

private theorem rc_sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.add_neg_self_eqv (A.approx n)))

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_add_zero_eqv (A.approx n)))

private theorem rc_sub_add (a b : RC) : RCadd (RCsub a b) b = a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _) (Q'.add_neg_self_eqv (B.approx n))))
        (QPoly.q_add_zero_eqv (A.approx n)))))

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {half : Nat}

local notation "D" => seminorm w hw0 hw1 half
local notation "u" => completedUnit w hw0 hw1 half
local notation "B" => completedInner w hw0 hw1
local notation "P" => unitProjection w hw0 hw1

theorem completedInner_neg_left (x y : Completion w hw0 hw1 half) :
    B (completedNeg w hw0 hw1 x) y = RCneg (B x y) := by
  change B (completedSmul w hw0 hw1 (-1) x) y = _
  rw [completedInner_smul_left, rc_negative_one]

theorem completedInner_sub_left (x y z : Completion w hw0 hw1 half) :
    B (completedSub w hw0 hw1 x y) z = RCsub (B x z) (B y z) := by
  unfold completedSub RCsub
  rw [completedInner_add_left, completedInner_neg_left]

theorem completedInner_sub_right (x y z : Completion w hw0 hw1 half) :
    B x (completedSub w hw0 hw1 y z) = RCsub (B x y) (B x z) := by
  rw [completedInner_symm w hw0 hw1 x, completedInner_sub_left,
    completedInner_symm w hw0 hw1 y x, completedInner_symm w hw0 hw1 z x]

theorem completedSub_zero (x : Completion w hw0 hw1 half) :
    completedSub w hw0 hw1 x (completedZero w hw0 hw1 half) = x := by
  have h := completedSub_add_cancel w hw0 hw1 x (completedZero w hw0 hw1 half)
  rw [completedAdd_zero] at h
  exact h

def center (x : Completion w hw0 hw1 half) : Completion w hw0 hw1 half := completedSub w hw0 hw1 x (P x)

/-- The centered representative retains the explicit original coefficient/scalar moduli. -/
def centerCauchy (X : (D).Cauchy) : (D).Cauchy :=
  differenceCauchy w hw0 hw1 X (unitProjectionCauchy w hw0 hw1 X)

theorem center_mk (X : (D).Cauchy) :
    center w hw0 hw1 (Quotient.mk (D).completionSetoid X) =
      Quotient.mk (D).completionSetoid (centerCauchy w hw0 hw1 X) := rfl

theorem center_pairing (x y : Completion w hw0 hw1 half) :
    B (center w hw0 hw1 x) y = RCsub (B x y) (RCmul (B x u) (B u y)) := by
  unfold center
  rw [completedInner_sub_left, unitProjection_pairing]

theorem center_selfAdjoint (x y : Completion w hw0 hw1 half) :
    B (center w hw0 hw1 x) y = B x (center w hw0 hw1 y) := by
  unfold center
  rw [completedInner_sub_left, completedInner_sub_right, unitProjection_selfAdjoint]

theorem center_orthogonal (x : Completion w hw0 hw1 half) : B (center w hw0 hw1 x) u = RCzero := by
  unfold center
  rw [completedInner_sub_left, unitProjection_coefficient, rc_sub_self]

theorem center_fixed_iff (x : Completion w hw0 hw1 half) : center w hw0 hw1 x = x ↔ B x u = RCzero := by
  constructor
  · intro h
    rw [← h]
    exact center_orthogonal w hw0 hw1 x
  · intro h
    unfold center
    rw [(unitProjection_zero_iff w hw0 hw1 x).mpr h, completedSub_zero]

theorem center_idempotent (x : Completion w hw0 hw1 half) :
    center w hw0 hw1 (center w hw0 hw1 x) = center w hw0 hw1 x :=
  (center_fixed_iff w hw0 hw1 _).mpr (center_orthogonal w hw0 hw1 x)

theorem center_unit : center w hw0 hw1 u = completedZero w hw0 hw1 half := by
  unfold center
  rw [unitProjection_unit, completedSub_self]

theorem center_zero : center w hw0 hw1 (completedZero w hw0 hw1 half) = completedZero w hw0 hw1 half :=
  (center_fixed_iff w hw0 hw1 _).mpr (completedInner_zero_left w hw0 hw1 u)

theorem unitProjection_center (x : Completion w hw0 hw1 half) : P (center w hw0 hw1 x) = completedZero w hw0 hw1 half :=
  (unitProjection_zero_iff w hw0 hw1 _).mpr (center_orthogonal w hw0 hw1 x)

theorem center_unitProjection (x : Completion w hw0 hw1 half) : center w hw0 hw1 (P x) = completedZero w hw0 hw1 half := by
  unfold center
  rw [unitProjection_idempotent, completedSub_self]

theorem center_decomposition (x : Completion w hw0 hw1 half) :
    completedAdd w hw0 hw1 (center w hw0 hw1 x) (P x) = x := completedSub_add_cancel w hw0 hw1 x (P x)

theorem center_add (x y : Completion w hw0 hw1 half) :
    center w hw0 hw1 (completedAdd w hw0 hw1 x y) =
      completedAdd w hw0 hw1 (center w hw0 hw1 x) (center w hw0 hw1 y) := by
  apply completed_eq_of_pairings w hw0 hw1
  intro z
  rw [center_selfAdjoint, completedInner_add_left, completedInner_add_left, center_selfAdjoint, center_selfAdjoint]

theorem center_realSmul (s : CReal) (cs : QCauchy s.approx) (x : Completion w hw0 hw1 half) :
    center w hw0 hw1 (completedRealSmul w hw0 hw1 s cs x) =
      completedRealSmul w hw0 hw1 s cs (center w hw0 hw1 x) := by
  apply completed_eq_of_pairings w hw0 hw1
  intro y
  rw [center_selfAdjoint, completedInner_realSmul_left, completedInner_realSmul_left, center_selfAdjoint]

theorem center_sub (x y : Completion w hw0 hw1 half) :
    center w hw0 hw1 (completedSub w hw0 hw1 x y) =
      completedSub w hw0 hw1 (center w hw0 hw1 x) (center w hw0 hw1 y) := by
  apply completed_eq_of_pairings w hw0 hw1
  intro z
  rw [center_selfAdjoint, completedInner_sub_left, completedInner_sub_left, center_selfAdjoint, center_selfAdjoint]

theorem centered_inner (x y : Completion w hw0 hw1 half) :
    B (center w hw0 hw1 x) (center w hw0 hw1 y) = RCsub (B x y) (RCmul (B x u) (B u y)) := by
  rw [center_selfAdjoint, center_idempotent, ← center_selfAdjoint, center_pairing]

/-- Pythagoras, including mixed pairings, on the actual original carrier. -/
theorem orthogonal_decomposition_inner (x y : Completion w hw0 hw1 half) :
    RCadd (B (center w hw0 hw1 x) (center w hw0 hw1 y)) (B (P x) (P y)) = B x y := by
  rw [centered_inner, unitProjection_inner, rc_sub_add]

theorem center_norm_le (x : Completion w hw0 hw1 half) :
    RCle (B (center w hw0 hw1 x) (center w hw0 hw1 x)) (B x x) := by
  have h := RCadd_le_add (RCle_refl (B (center w hw0 hw1 x) (center w hw0 hw1 x)))
    (completedInner_nonnegative w hw0 hw1 (P x))
  rw [rc_add_zero, orthogonal_decomposition_inner] at h
  exact h

theorem center_nonexpansive (x y : Completion w hw0 hw1 half) :
    RCle (completedDist w hw0 hw1 (center w hw0 hw1 x) (center w hw0 hw1 y)) (completedDist w hw0 hw1 x y) := by
  unfold completedDist
  rw [← center_sub]
  exact center_norm_le w hw0 hw1 (completedSub w hw0 hw1 x y)

/-- Exactly the unit-orthogonal subspace; no nonzero vector is asserted. -/
def UnitComplement (half : Nat) : Type := {x : Completion w hw0 hw1 half // B x (completedUnit w hw0 hw1 half) = RCzero}

def centeredState (x : Completion w hw0 hw1 half) : UnitComplement w hw0 hw1 half :=
  ⟨center w hw0 hw1 x, center_orthogonal w hw0 hw1 x⟩

theorem centeredState_fixes (x : UnitComplement w hw0 hw1 half) : centeredState w hw0 hw1 x.val = x :=
  Subtype.ext ((center_fixed_iff w hw0 hw1 x.val).mpr x.property)

theorem centered_inner_embedExpression (e f : PlaquetteExpression half) :
    B (center w hw0 hw1 (embedExpression w hw0 hw1 e)) (center w hw0 hw1 (embedExpression w hw0 hw1 f)) =
      RCsub (pairing w hw0 hw1 e f) (RCmul (pairing w hw0 hw1 e .unit) (pairing w hw0 hw1 .unit f)) := by
  rw [centered_inner]
  change RCsub (B (embedExpression w hw0 hw1 e) (embedExpression w hw0 hw1 f))
    (RCmul (B (embedExpression w hw0 hw1 e) (embedExpression w hw0 hw1 .unit))
      (B (embedExpression w hw0 hw1 .unit) (embedExpression w hw0 hw1 f))) = _
  rw [completedInner_embedExpression, completedInner_embedExpression, completedInner_embedExpression]

end YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion.completedInner_neg_left
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion.completedInner_sub_left
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion.completedInner_sub_right
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion.completedSub_zero
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion.center
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion.centerCauchy
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion.center_mk
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion.center_pairing
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion.center_selfAdjoint
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion.center_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion.center_fixed_iff
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion.center_idempotent
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion.center_unit
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion.center_zero
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion.unitProjection_center
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion.center_unitProjection
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion.center_decomposition
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion.center_add
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion.center_realSmul
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion.center_sub
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion.centered_inner
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion.orthogonal_decomposition_inner
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion.center_norm_le
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion.center_nonexpansive
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion.UnitComplement
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion.centeredState
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion.centeredState_fixes
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCenteredCompletion.centered_inner_embedExpression
