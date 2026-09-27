/-
# Center-preserving iteration of the original conditional generator

The gradient step and its finite iterates act on the SAME original completed
carrier and preserve orthogonality to its actual unscaled constant. These
objects are for the coercivity proof, not new time translations.
-/

import YMGap.Continuum.GNSResidualGeneratorStep
import YMGap.Continuum.BF4ExactSlabSignedNeighborEnergy
import YMGap.Continuum.BF4ExactSlabSweepChebyshev

namespace YMGap.Continuum.BF4ExactSlabConditionalGeneratorIteration

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabSignedNeighborEnergy
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabFullActionScalar
open YMGap.Continuum.BF4ExactSlabSweepChebyshev

private theorem sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => RingNormaliser.poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.var 0))) (.const 0)
      (by decide) (fun _ => A.approx n)))

private theorem zero_add : RCadd RCzero RCzero = RCzero := by
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun _ => (by decide : Q'.eqv ((0 : Q') + 0) 0)))

private theorem sum_zero {A : Type} (xs : List A) (f : A → RC)
    (hf : ∀ i, f i = RCzero) : Family.sumOn xs f = RCzero := by
  induction xs with
  | nil => rfl
  | cons i rest ih => simp only [Family.sumOn, hf, ih, zero_add]

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK
local notation "S" => fullScalarData hw0 hw1 K extent hK
local notation "O" => embedV (fullData hw0 hw1 K extent hK) (constant hw0 hw1 K extent hK)

/-- Every original generator output is orthogonal to the actual constant,
without assuming that its input was centered. -/
theorem generator_orthogonal_constant (x : GNSCompletionSpace F) :
    (F).cinnerCompl (conditionalGenerator hw0 hw1 K extent hK x) O = RCzero := by
  unfold conditionalGenerator
  rw [Family.residualSum_pairing]
  apply sum_zero
  intro i
  change (F).cinnerCompl ((F).cSub x ((P).op i x)) O = RCzero
  rw [(F).cinnerCompl_cSub_left, (P).adjoint,
    constant_fixed hw0 hw1 K extent hK i, sub_self]

/-- The actual rational Euler step of the original conditional generator. -/
def step (s : Q') (x : GNSCompletionSpace F) : GNSCompletionSpace F :=
  GNSResidualGeneratorStep.gradientStep S P (schedule extent) s x

theorem step_centered (s : Q') (x : GNSCompletionSpace F)
    (hx : Centered hw0 hw1 K extent hK x) :
    Centered hw0 hw1 K extent hK (step hw0 hw1 K extent hK s x) := by
  change (F).cinnerCompl (step hw0 hw1 K extent hK s x) O = RCzero
  unfold step
  have hp := GNSResidualGeneratorStep.gradientStep_pair S P (schedule extent) s x O
  change (F).cinnerCompl (GNSResidualGeneratorStep.gradientStep S P (schedule extent) s x) O =
    RCsub ((F).cinnerCompl x O)
      (RCscale s ((F).cinnerCompl (conditionalGenerator hw0 hw1 K extent hK x) O)) at hp
  rw [hp]
  change RCsub ((F).cinnerCompl x O)
    (RCscale s ((F).cinnerCompl (conditionalGenerator hw0 hw1 K extent hK x) O)) = RCzero
  rw [generator_orthogonal_constant, RCscale_RCzero]
  change (F).cinnerCompl x O = RCzero at hx
  rw [hx, sub_self]

/-- Computable finite iteration; no limiting vector or representative choice. -/
def iterate (s : Q') (x : GNSCompletionSpace F) : Nat → GNSCompletionSpace F
  | 0 => x
  | n + 1 => step hw0 hw1 K extent hK s (iterate s x n)

theorem iterate_centered (s : Q') (x : GNSCompletionSpace F)
    (hx : Centered hw0 hw1 K extent hK x) (n : Nat) :
    Centered hw0 hw1 K extent hK (iterate hw0 hw1 K extent hK s x n) := by
  induction n with
  | zero => exact hx
  | succ n ih => exact step_centered hw0 hw1 K extent hK s _ ih

#print axioms generator_orthogonal_constant
#print axioms step
#print axioms step_centered
#print axioms iterate
#print axioms iterate_centered

end YMGap.Continuum.BF4ExactSlabConditionalGeneratorIteration
