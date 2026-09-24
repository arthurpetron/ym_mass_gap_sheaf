/-
# Algebraic laws of the exact represented Neumann inverse

The already constructed inverse of `I - T^2` is rational-linear and commutes
with every discrete physical-time step on the SAME fixed-nome, fixed-width
joint reflected completion.  These are uniqueness consequences of the exact
inverse equations and residual injectivity on the vacuum complement; no new
analytic premise or representative choice is introduced.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannInverse

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannAlgebra

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointUnitComplement
  (completedTime_preserves_orthogonal completedInner_time_balance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointVacuumProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointRangeApproximation (residual)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannInverse

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "V" => JointCompletion hw0 hw1 width
local notation "B" => completedInner hw0 hw1 width
local notation "U" => jointCompletedUnit hw0 hw1 width
local notation "T" => jointCompletedTime hw0 hw1 width
local notation "A" => completedAdd hw0 hw1 width
local notation "S" => completedSmul hw0 hw1 width

private theorem rc_add_sub_exchange (a b c d : RC) :
    RCsub (RCadd a b) (RCadd c d) =
      RCadd (RCsub a c) (RCsub b d) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A' B'
  refine Quotient.inductionOn₂ c d ?_
  intro C' D'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1))
        (.neg (.add (.var 2) (.var 3))))
      (.add (.add (.var 0) (.neg (.var 2)))
        (.add (.var 1) (.neg (.var 3)))) (by decide)
      (fun | 0 => A'.approx n | 1 => B'.approx n | 2 => C'.approx n | _ => D'.approx n)))

private theorem rc_scale_sub (c : Q') (a b : RC) :
    RCsub (RCscale c a) (RCscale c b) = RCscale c (RCsub a b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A' B'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.mul (.var 2) (.var 0))
        (.neg (.mul (.var 2) (.var 1))))
      (.mul (.var 2) (.add (.var 0) (.neg (.var 1)))) (by decide)
      (fun | 0 => A'.approx n | 1 => B'.approx n | _ => c)))

/-- The residual `I - T^2` is additive on the actual completion. -/
theorem residual_add (x y : V) :
    residual hw0 hw1 width (A x y) =
      A (residual hw0 hw1 width x) (residual hw0 hw1 width y) := by
  apply completed_eq_of_pairings hw0 hw1 width
  intro z
  simp only [residual, completedTime_additive, completedInner_sub_left,
    completedInner_add_left]
  exact rc_add_sub_exchange _ _ _ _

/-- The residual `I - T^2` is homogeneous for every rational scalar. -/
theorem residual_smul (c : Q') (x : V) :
    residual hw0 hw1 width (S c x) = S c (residual hw0 hw1 width x) := by
  apply completed_eq_of_pairings hw0 hw1 width
  intro z
  simp only [residual, completedTime_smul, completedInner_sub_left,
    completedInner_smul_left]
  exact rc_scale_sub c _ _

/-- The residual commutes with every discrete physical-time step. -/
theorem residual_time (n : Nat) (x : V) :
    residual hw0 hw1 width (T n x) = T n (residual hw0 hw1 width x) := by
  unfold residual
  rw [completedTime_sub, ← jointCompletedTime_add, ← jointCompletedTime_add]
  rw [Nat.add_comm 2 n]

/-- The residual is self-adjoint for the actual completed pairing. -/
theorem residual_selfAdjoint (x y : V) :
    B (residual hw0 hw1 width x) y = B x (residual hw0 hw1 width y) := by
  rw [residual, residual, completedInner_sub_left, completedInner_sub_right,
    completedInner_time_balance]

/-- Rational additivity of the exact inverse, obtained solely from uniqueness
on the vacuum complement. -/
theorem inverse_add (x y : V) :
    inverse hw0 hw1 width (A x y) =
      A (inverse hw0 hw1 width x) (inverse hw0 hw1 width y) := by
  apply residual_injective_on_complement hw0 hw1 width
  · exact inverse_orthogonal hw0 hw1 width _
  · rw [completedInner_add_left, inverse_orthogonal, inverse_orthogonal]
    rfl
  · rw [inverse_residual, residual_add, inverse_residual, inverse_residual, center_add]

/-- Rational homogeneity of the exact inverse. -/
theorem inverse_smul (c : Q') (x : V) :
    inverse hw0 hw1 width (S c x) = S c (inverse hw0 hw1 width x) := by
  apply residual_injective_on_complement hw0 hw1 width
  · exact inverse_orthogonal hw0 hw1 width _
  · rw [completedInner_smul_left, inverse_orthogonal]
    exact RCscale_RCzero c
  · rw [inverse_residual, residual_smul, inverse_residual, center_smul]

/-- The exact inverse preserves subtraction on the same completion. -/
theorem inverse_sub (x y : V) :
    inverse hw0 hw1 width (completedSub hw0 hw1 width x y) =
      completedSub hw0 hw1 width (inverse hw0 hw1 width x)
        (inverse hw0 hw1 width y) := by
  apply residual_injective_on_complement hw0 hw1 width
  · exact inverse_orthogonal hw0 hw1 width _
  · rw [completedInner_sub_left, inverse_orthogonal, inverse_orthogonal]
    rfl
  · rw [inverse_residual, residual_sub, inverse_residual, inverse_residual, center_sub]

/-- The exact inverse commutes with the existing discrete physical-time
semigroup. -/
theorem inverse_time (n : Nat) (x : V) :
    inverse hw0 hw1 width (T n x) = T n (inverse hw0 hw1 width x) := by
  apply residual_injective_on_complement hw0 hw1 width
  · exact inverse_orthogonal hw0 hw1 width _
  · exact completedTime_preserves_orthogonal hw0 hw1 width n _
      (inverse_orthogonal hw0 hw1 width x)
  · rw [inverse_residual, residual_time, inverse_residual, completedTime_center]

/-- Symmetry of the exact inverse for the actual completed pairing. -/
theorem inverse_selfAdjoint (x y : V) :
    B (inverse hw0 hw1 width x) y = B x (inverse hw0 hw1 width y) := by
  have hix : center hw0 hw1 width (inverse hw0 hw1 width x) =
      inverse hw0 hw1 width x :=
    (center_fixed_iff hw0 hw1 width _).mpr (inverse_orthogonal hw0 hw1 width x)
  have hiy : center hw0 hw1 width (inverse hw0 hw1 width y) =
      inverse hw0 hw1 width y :=
    (center_fixed_iff hw0 hw1 width _).mpr (inverse_orthogonal hw0 hw1 width y)
  calc
    B (inverse hw0 hw1 width x) y =
        B (center hw0 hw1 width (inverse hw0 hw1 width x)) y := by rw [hix]
    _ = B (inverse hw0 hw1 width x) (center hw0 hw1 width y) :=
      center_selfAdjoint hw0 hw1 width _ _
    _ = B (inverse hw0 hw1 width x)
        (residual hw0 hw1 width (inverse hw0 hw1 width y)) := by
      rw [inverse_residual]
    _ = B (residual hw0 hw1 width (inverse hw0 hw1 width x))
        (inverse hw0 hw1 width y) :=
      (residual_selfAdjoint hw0 hw1 width _ _).symm
    _ = B (center hw0 hw1 width x) (inverse hw0 hw1 width y) := by
      rw [inverse_residual]
    _ = B x (center hw0 hw1 width (inverse hw0 hw1 width y)) :=
      center_selfAdjoint hw0 hw1 width _ _
    _ = B x (inverse hw0 hw1 width y) := by rw [hiy]

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannAlgebra.residual_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannAlgebra.residual_smul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannAlgebra.residual_time
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannAlgebra.residual_selfAdjoint
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannAlgebra.inverse_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannAlgebra.inverse_smul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannAlgebra.inverse_sub
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannAlgebra.inverse_time
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannAlgebra.inverse_selfAdjoint

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannAlgebra
