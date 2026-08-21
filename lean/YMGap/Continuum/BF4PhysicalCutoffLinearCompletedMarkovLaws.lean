/-
# Rational-linearity of the completed physical BF4 Markov transfer

Once the diagonal-Cauchy and close-preservation modulus constructs the
completed cutoff-limit transfer, no further analytic estimate is needed for
linearity.  The cutoff action preserves zero, addition, and rational scaling
by recursion on the common finite-linear syntax.  Quotient induction reduces
the completed laws to those pointwise identities.

This file proves the three literal completed equalities and bundles the result
as a rational-linear endomorphism of the already constructed completed module.
It does not inhabit the completion modulus or prove inner-form invariance,
vacuum-complement preservation, or a strict contraction.

## Axiom gate

Only explicit Cauchy representatives, pointwise radical nullity, and quotient
descent are used.  There is no classical choice, noncomputable declaration,
custom axiom, or unproved placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovTransfer

namespace YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovLaws

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedAlgebra
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovTransfer
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedModule
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
open YMGap.Continuum.CRealSeminormCompletion

/-! ## 1. Completed rational-linearity laws -/

theorem centralPhysicalCutoffCompletedMarkovTransfer_zero
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half) :
    centralPhysicalCutoffCompletedMarkovTransfer M
        (completedPhysicalLinearZero hw0 hw1 half) =
      completedPhysicalLinearZero hw0 hw1 half := by
  apply Quotient.sound
  exact ⟨SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull
    (fun n =>
      (centralPhysicalCutoffLinearSquaredSeminorm
        hw0 hw1 half).distSq_refl zero)⟩

theorem centralPhysicalCutoffCompletedMarkovTransfer_add
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    (left right : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    centralPhysicalCutoffCompletedMarkovTransfer M
        (completedPhysicalLinearAdd hw0 hw1 half left right) =
      completedPhysicalLinearAdd hw0 hw1 half
        (centralPhysicalCutoffCompletedMarkovTransfer M left)
        (centralPhysicalCutoffCompletedMarkovTransfer M right) := by
  refine Quotient.inductionOn left (fun X => ?_)
  refine Quotient.inductionOn right (fun Y => ?_)
  apply Quotient.sound
  exact ⟨SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull
    (fun n =>
      (centralPhysicalCutoffLinearSquaredSeminorm
        hw0 hw1 half).distSq_refl
          (add
            (centralPhysicalLinearMarkovCutoffAction
              (Q'.le_of_lt hw0) n half (X.seq n))
            (centralPhysicalLinearMarkovCutoffAction
              (Q'.le_of_lt hw0) n half (Y.seq n))))⟩

theorem centralPhysicalCutoffCompletedMarkovTransfer_smul
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half)
    (scalar : Q')
    (observable : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    centralPhysicalCutoffCompletedMarkovTransfer M
        (completedPhysicalLinearSmul
          hw0 hw1 half scalar observable) =
      completedPhysicalLinearSmul hw0 hw1 half scalar
        (centralPhysicalCutoffCompletedMarkovTransfer M observable) := by
  refine Quotient.inductionOn observable (fun X => ?_)
  apply Quotient.sound
  exact ⟨SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull
    (fun n =>
      (centralPhysicalCutoffLinearSquaredSeminorm
        hw0 hw1 half).distSq_refl
          (smul scalar
            (centralPhysicalLinearMarkovCutoffAction
              (Q'.le_of_lt hw0) n half (X.seq n))))⟩

/-! ## 2. Bundled completed rational-linear endomorphism -/

/-- A literal endomorphism of a constructive completed rational module. -/
structure CompletedQLinearEndomorphismData
    (D : CompletedQModuleData) : Type where
  toFun : D.Carrier -> D.Carrier
  map_zero : toFun D.zero = D.zero
  map_add : forall left right,
    toFun (D.add left right) = D.add (toFun left) (toFun right)
  map_smul : forall scalar observable,
    toFun (D.smul scalar observable) = D.smul scalar (toFun observable)

/-- The cutoff-limit transfer, conditional only on the exact completion
modulus, as a rational-linear endomorphism of the concrete completed carrier. -/
def centralPhysicalCutoffCompletedMarkovQLinearEndomorphism
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (M : CentralPhysicalLinearMarkovCompletionModulus hw0 hw1 half) :
    CompletedQLinearEndomorphismData
      (centralPhysicalCutoffCompletedQModule hw0 hw1 half) where
  toFun := centralPhysicalCutoffCompletedMarkovTransfer M
  map_zero := centralPhysicalCutoffCompletedMarkovTransfer_zero M
  map_add := centralPhysicalCutoffCompletedMarkovTransfer_add M
  map_smul := centralPhysicalCutoffCompletedMarkovTransfer_smul M

/-! ## Axiom audit -/

#print axioms centralPhysicalCutoffCompletedMarkovTransfer_zero
#print axioms centralPhysicalCutoffCompletedMarkovTransfer_add
#print axioms centralPhysicalCutoffCompletedMarkovTransfer_smul
#print axioms CompletedQLinearEndomorphismData
#print axioms centralPhysicalCutoffCompletedMarkovQLinearEndomorphism

end YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovLaws
