/-
# Positive original patch-generator bound and actual energy descent

The all-state complement estimate gives gamma*E_S(x) <= ||H_S x||^2 for
the EXISTING original singleton residual sum. Its kernel is the EXISTING
original block conditional range, including arbitrary exterior dependence.
The same coefficient supplies an actual stable gradient-step contraction.

This baseline depends on nome and patch size; it is not a useful collective
scaling estimate, an OS time operator, or a physical mass-gap theorem.
-/

import YMGap.Continuum.BF4ExactSlabBlockComplementCoercivity
import YMGap.Continuum.BF4ExactSlabFullActionScalar
import YMGap.Continuum.GNSProjectionKernelCoercivity
import YMGap.Continuum.GNSResidualGeneratorDescent
import YMGap.Continuum.GNSResidualGeneratorStepSize

namespace YMGap.Continuum.BF4ExactSlabPatchGeneratorCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.GNSResidualGeneratorStep
open YMGap.Continuum.GNSResidualGeneratorStepSize
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabFullActionScalar
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabBlockFixedSpace
open YMGap.Continuum.BF4ExactSlabBlockComplementCoercivity

private theorem sub_zero (a : RC) : RCsub a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.eqv (-0) 0))
      (Q'.eqv_of_eq (Q'.add_zero' (A.approx n)))))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)
  (tests : List (PhysicalLink extent))

local notation "F" => fullData hw0 hw1 K extent hK
local notation "S" => fullScalarData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK
local notation "C" => BF4ExactSlabBlockConditionalProjection.conditionalProjection
  hw0 hw1 K extent hK (testLinks extent tests) (testLinks_valid extent tests)
local notation "gamma" => blockCoercivity hw0 tests.length

/-- The mixed term retains precisely the original Dirichlet energy. -/
theorem generator_complement_pair (x : GNSCompletionSpace F) :
    (F).cinnerCompl ((P).residualSum tests x) ((F).cSub x (C x)) =
      (P).finalEnergy tests x := by
  have hz : (P).residualSum tests (C x) = embedV F (F).zero :=
    (fixed_iff_generator_zero hw0 hw1 K extent hK tests (C x)).mp
      (BF4ExactSlabBlockConditionalProjection.conditionalProjection_idempotent
        hw0 hw1 K extent hK (testLinks extent tests) (testLinks_valid extent tests) x)
  rw [(F).cinnerCompl_comm _ ((F).cSub x (C x)), (F).cinnerCompl_cSub_left,
    (F).cinnerCompl_comm x, (F).cinnerCompl_comm (C x),
    (P).residualSum_self_pairing, (P).residualSum_adjoint tests x (C x),
    hz, (F).cinnerCompl_embedZero_right, sub_zero]

/-- Positive square-energy bound for the ACTUAL original patch generator,
on every completed input and every finite physical list. -/
theorem patch_generator_square_lower (x : GNSCompletionSpace F) :
    RCle (RCscale gamma ((P).finalEnergy tests x))
      (normSq ((P).residualSum tests x)) :=
  GNSProjectionKernelCoercivity.square_lower_of_coercive_pair S gamma
    (Q'.le_of_lt (blockCoercivity_positive hw0 hw1 tests.length))
    ((P).residualSum tests x) ((F).cSub x (C x)) ((P).finalEnergy tests x)
    (generator_complement_pair hw0 hw1 K extent hK tests x)
    (block_complement_coercivity hw0 hw1 K extent hK tests x)

/-- Explicit internal patch descent rate, not an OS/physical time rate. -/
def patchRate (size : Nat) : Q' :=
  1 + -(stepSize size * blockCoercivity hw0 size)

include hw1 in
theorem patchRate_window (size : Nat) :
    (0 : Q') < patchRate hw0 size ∧ patchRate hw0 size < (1 : Q') :=
  step_window size (blockCoercivity_positive hw0 hw1 size)
    (blockCoercivity_le_one hw0 hw1 size)

/-- The existing constructive gradient step has a supplied strict energy
contraction at every nome, with its actual patch-size-dependent rate. -/
theorem patch_step_energy_contract (x : GNSCompletionSpace F) :
    RCle ((P).finalEnergy tests
      (gradientStep S P tests (stepSize tests.length) x))
      (RCscale (patchRate hw0 tests.length) ((P).finalEnergy tests x)) :=
  GNSResidualGeneratorDescent.energy_contract S P tests
    (stepSize tests.length) gamma
    (Q'.le_of_lt (stepSize_positive _)) (stepSize_times_length_le_one _)
    (Q'.le_of_lt (blockCoercivity_positive hw0 hw1 tests.length))
    (patch_generator_square_lower hw0 hw1 K extent hK tests) x

#print axioms generator_complement_pair
#print axioms patch_generator_square_lower
#print axioms patchRate
#print axioms patchRate_window
#print axioms patch_step_energy_contract

end YMGap.Continuum.BF4ExactSlabPatchGeneratorCoercivity
