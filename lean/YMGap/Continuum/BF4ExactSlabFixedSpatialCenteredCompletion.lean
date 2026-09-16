/-
# Orthogonal centering on the SAME original physical Cauchy carrier

Subtract the constructed rank-one projection onto the SAME original unit.
The resulting map is self-adjoint, idempotent, linear and nonexpansive.
Its mixed pairing is the original connected reflected covariance; the
orthogonal decomposition gives a Pythagorean norm identity with no loss.

The unit is already fixed by the actual physical-time map. This constructs
its orthogonal complement, not a nonzero excitation, isolated vacuum,
strict gap or full Hilbert/OS theory. Nome, width and heat cutoff stay fixed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialUnitProjection

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPosdef
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletionLinear
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedBilinear
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedRealScalar
open YMGap.Continuum.BF4ExactSlabFixedSpatialUnitProjection

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

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width stage : Nat)

local notation "D" => seminorm hw0 hw1 width stage
local notation "u" => completedUnit hw0 hw1 width stage
local notation "B" => completedInner hw0 hw1 width stage
local notation "P" => unitProjection hw0 hw1 width stage

theorem completedInner_neg_left (x y : Completion hw0 hw1 width stage) :
    B (completedNeg hw0 hw1 width stage x) y = RCneg (B x y) := by
  change B (completedSmul hw0 hw1 width stage (-1) x) y = _
  rw [completedInner_smul_left, rc_negative_one]

theorem completedInner_sub_left (x y z : Completion hw0 hw1 width stage) :
    B (completedSub hw0 hw1 width stage x y) z = RCsub (B x z) (B y z) := by
  unfold completedSub RCsub
  rw [completedInner_add_left, completedInner_neg_left]

theorem completedInner_sub_right (x y z : Completion hw0 hw1 width stage) :
    B x (completedSub hw0 hw1 width stage y z) = RCsub (B x y) (B x z) := by
  rw [completedInner_symm hw0 hw1 width stage x, completedInner_sub_left,
    completedInner_symm hw0 hw1 width stage y x, completedInner_symm hw0 hw1 width stage z x]

theorem completedSub_zero (x : Completion hw0 hw1 width stage) :
    completedSub hw0 hw1 width stage x (completedZero hw0 hw1 width stage) = x := by
  have h := completedSub_add_cancel hw0 hw1 width stage x (completedZero hw0 hw1 width stage)
  rw [completedAdd_zero] at h
  exact h

def center (x : Completion hw0 hw1 width stage) : Completion hw0 hw1 width stage := completedSub hw0 hw1 width stage x (P x)

/-- The centered representative retains the explicit original coefficient/scalar moduli. -/
def centerCauchy (X : (D).Cauchy) : (D).Cauchy :=
  differenceCauchy hw0 hw1 width stage X (unitProjectionCauchy hw0 hw1 width stage X)

theorem center_mk (X : (D).Cauchy) :
    center hw0 hw1 width stage (Quotient.mk (D).completionSetoid X) =
      Quotient.mk (D).completionSetoid (centerCauchy hw0 hw1 width stage X) := rfl

theorem center_pairing (x y : Completion hw0 hw1 width stage) :
    B (center hw0 hw1 width stage x) y = RCsub (B x y) (RCmul (B x u) (B u y)) := by
  unfold center
  rw [completedInner_sub_left, unitProjection_pairing]

theorem center_selfAdjoint (x y : Completion hw0 hw1 width stage) :
    B (center hw0 hw1 width stage x) y = B x (center hw0 hw1 width stage y) := by
  unfold center
  rw [completedInner_sub_left, completedInner_sub_right, unitProjection_selfAdjoint]

theorem center_orthogonal (x : Completion hw0 hw1 width stage) : B (center hw0 hw1 width stage x) u = RCzero := by
  unfold center
  rw [completedInner_sub_left, unitProjection_coefficient, rc_sub_self]

theorem center_fixed_iff (x : Completion hw0 hw1 width stage) : center hw0 hw1 width stage x = x ↔ B x u = RCzero := by
  constructor
  · intro h
    rw [← h]
    exact center_orthogonal hw0 hw1 width stage x
  · intro h
    unfold center
    rw [(unitProjection_zero_iff hw0 hw1 width stage x).mpr h, completedSub_zero]

theorem center_idempotent (x : Completion hw0 hw1 width stage) :
    center hw0 hw1 width stage (center hw0 hw1 width stage x) = center hw0 hw1 width stage x :=
  (center_fixed_iff hw0 hw1 width stage _).mpr (center_orthogonal hw0 hw1 width stage x)

theorem center_unit : center hw0 hw1 width stage u = completedZero hw0 hw1 width stage := by
  unfold center
  rw [unitProjection_unit, completedSub_self]

theorem center_zero : center hw0 hw1 width stage (completedZero hw0 hw1 width stage) = completedZero hw0 hw1 width stage :=
  (center_fixed_iff hw0 hw1 width stage _).mpr (completedInner_zero_left hw0 hw1 width stage u)

theorem unitProjection_center (x : Completion hw0 hw1 width stage) : P (center hw0 hw1 width stage x) = completedZero hw0 hw1 width stage :=
  (unitProjection_zero_iff hw0 hw1 width stage _).mpr (center_orthogonal hw0 hw1 width stage x)

theorem center_unitProjection (x : Completion hw0 hw1 width stage) : center hw0 hw1 width stage (P x) = completedZero hw0 hw1 width stage := by
  unfold center
  rw [unitProjection_idempotent, completedSub_self]

theorem center_decomposition (x : Completion hw0 hw1 width stage) :
    completedAdd hw0 hw1 width stage (center hw0 hw1 width stage x) (P x) = x := completedSub_add_cancel hw0 hw1 width stage x (P x)

theorem center_add (x y : Completion hw0 hw1 width stage) :
    center hw0 hw1 width stage (completedAdd hw0 hw1 width stage x y) =
      completedAdd hw0 hw1 width stage (center hw0 hw1 width stage x) (center hw0 hw1 width stage y) := by
  apply completed_eq_of_pairings hw0 hw1 width stage
  intro z
  rw [center_selfAdjoint, completedInner_add_left, completedInner_add_left, center_selfAdjoint, center_selfAdjoint]

theorem center_realSmul (s : CReal) (cs : QCauchy s.approx) (x : Completion hw0 hw1 width stage) :
    center hw0 hw1 width stage (completedRealSmul hw0 hw1 width stage s cs x) =
      completedRealSmul hw0 hw1 width stage s cs (center hw0 hw1 width stage x) := by
  apply completed_eq_of_pairings hw0 hw1 width stage
  intro y
  rw [center_selfAdjoint, completedInner_realSmul_left, completedInner_realSmul_left, center_selfAdjoint]

theorem center_sub (x y : Completion hw0 hw1 width stage) :
    center hw0 hw1 width stage (completedSub hw0 hw1 width stage x y) =
      completedSub hw0 hw1 width stage (center hw0 hw1 width stage x) (center hw0 hw1 width stage y) := by
  apply completed_eq_of_pairings hw0 hw1 width stage
  intro z
  rw [center_selfAdjoint, completedInner_sub_left, completedInner_sub_left, center_selfAdjoint, center_selfAdjoint]

theorem centered_inner (x y : Completion hw0 hw1 width stage) :
    B (center hw0 hw1 width stage x) (center hw0 hw1 width stage y) = RCsub (B x y) (RCmul (B x u) (B u y)) := by
  rw [center_selfAdjoint, center_idempotent, ← center_selfAdjoint, center_pairing]

/-- Pythagoras, including mixed pairings, on the actual original carrier. -/
theorem orthogonal_decomposition_inner (x y : Completion hw0 hw1 width stage) :
    RCadd (B (center hw0 hw1 width stage x) (center hw0 hw1 width stage y)) (B (P x) (P y)) = B x y := by
  rw [centered_inner, unitProjection_inner, rc_sub_add]

theorem center_norm_le (x : Completion hw0 hw1 width stage) :
    RCle (B (center hw0 hw1 width stage x) (center hw0 hw1 width stage x)) (B x x) := by
  have h := RCadd_le_add (RCle_refl (B (center hw0 hw1 width stage x) (center hw0 hw1 width stage x)))
    (completedInner_nonnegative hw0 hw1 width stage (P x))
  rw [rc_add_zero, orthogonal_decomposition_inner] at h
  exact h

theorem center_nonexpansive (x y : Completion hw0 hw1 width stage) :
    RCle (completedDist hw0 hw1 width stage (center hw0 hw1 width stage x) (center hw0 hw1 width stage y)) (completedDist hw0 hw1 width stage x y) := by
  unfold completedDist
  rw [← center_sub]
  exact center_norm_le hw0 hw1 width stage (completedSub hw0 hw1 width stage x y)

/-- Exactly the unit-orthogonal subspace; no nonzero vector is asserted. -/
def UnitComplement : Type := {x : Completion hw0 hw1 width stage // B x (completedUnit hw0 hw1 width stage) = RCzero}

def centeredState (x : Completion hw0 hw1 width stage) : UnitComplement hw0 hw1 width stage :=
  ⟨center hw0 hw1 width stage x, center_orthogonal hw0 hw1 width stage x⟩

theorem centeredState_fixes (x : UnitComplement hw0 hw1 width stage) : centeredState hw0 hw1 width stage x.val = x :=
  Subtype.ext ((center_fixed_iff hw0 hw1 width stage x.val).mpr x.property)

theorem centered_inner_embedSpan (x y : PhysicalSpan width) :
    B (center hw0 hw1 width stage (embedSpan hw0 hw1 width stage x))
        (center hw0 hw1 width stage (embedSpan hw0 hw1 width stage y)) =
      RCsub (Quotient.mk crealSetoid (pairing hw0 hw1 width x.val y.val stage))
        (RCmul (Quotient.mk crealSetoid (pairing hw0 hw1 width x.val (unit width).val stage))
          (Quotient.mk crealSetoid (pairing hw0 hw1 width (unit width).val y.val stage))) := by
  rw [centered_inner]
  change RCsub (B (embedSpan hw0 hw1 width stage x) (embedSpan hw0 hw1 width stage y))
    (RCmul (B (embedSpan hw0 hw1 width stage x) (embedSpan hw0 hw1 width stage (unit width)))
      (B (embedSpan hw0 hw1 width stage (unit width)) (embedSpan hw0 hw1 width stage y))) = _
  rw [completedInner_embedSpan, completedInner_embedSpan, completedInner_embedSpan]

end YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion.completedInner_neg_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion.completedInner_sub_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion.completedInner_sub_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion.completedSub_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion.center
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion.centerCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion.center_mk
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion.center_pairing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion.center_selfAdjoint
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion.center_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion.center_fixed_iff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion.center_idempotent
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion.center_unit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion.center_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion.unitProjection_center
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion.center_unitProjection
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion.center_decomposition
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion.center_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion.center_realSmul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion.center_sub
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion.centered_inner
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion.orthogonal_decomposition_inner
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion.center_norm_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion.center_nonexpansive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion.UnitComplement
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion.centeredState
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion.centeredState_fixes
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion.centered_inner_embedSpan
