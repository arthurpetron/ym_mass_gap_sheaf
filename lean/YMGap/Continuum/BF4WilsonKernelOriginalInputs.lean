/-
# Original-window realization of chronological kernels on the whole union

Every finite input has its own support base and time radius. Their computed
maximum with the kernel's support produces a literal original grafted window.
Base coherence identifies its embedded state with the actual kernel action.

For every supplied Cauchy input and positive tolerance, the original modulus
and existing kernel cap compute ONE such finite grafted window within that
squared-distance tolerance of the completed output. No representative is
selected, and no common support bound for the input stream is assumed.
This is fixed-spacing original-input semantics, not continuum OS reconstruction
or an assertion that arbitrary vacuum-equivalent programs are equal operators.
-/

import YMGap.Continuum.BF4WilsonChronologicalBaseCoherence

namespace YMGap.Continuum.BF4WilsonKernelOriginalInputs

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion
open YMGap.Continuum.BF4WilsonSpatialUnion
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedDistance (completedDist)
open YMGap.Continuum.BF4WilsonChronologicalOperator
open YMGap.Continuum.BF4WilsonChronologicalKernel
open YMGap.Continuum.BF4WilsonChronologicalBaseCoherence
open YMGap.Continuum.BF4WilsonKernelInclusionSyntax
open YMGap.Continuum.BF4WilsonWindowRealization
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- A literal original stage computed from the kernel and arbitrary input support. -/
def graftStage {base : Nat} (H : Nat) (e : WindowExpression base) (he : Within H e)
    (x : Stage) : Stage :=
  let N := max base x.base
  let hN : 0 < N := Nat.lt_of_lt_of_le x.positive (Nat.le_max_right _ _)
  let f := atBase x (Nat.le_max_right base x.base)
  ofExpression N hN
    ⟨H+f.radius, graft f.radius (includeExpression (Nat.le_max_left base x.base) e) f.expression,
      graft_within _ _ ((includeExpression_within (Nat.le_max_left base x.base) H e).mpr he)
        f.within⟩

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "D" => unionSeminorm hw0 hw1 hsmall hd hs
local notation "E" => embedStage hw0 hw1 hsmall hd hs
local notation "Op" => act hw0 hw1 hsmall hd hs

/-- Exact equality on EVERY original finite input, without a fixed support base. -/
theorem compileKernel_stage_pin {base : Nat} (H : Nat) (e : WindowExpression base)
    (he : Within H e) (x : Stage) :
    Op (compileKernel H e) (E x) = E (graftStage H e he x) := by
  let N := max base x.base
  have hb : base ≤ N := Nat.le_max_left _ _
  have hx : x.base ≤ N := Nat.le_max_right _ _
  have hN : 0 < N := Nat.lt_of_lt_of_le x.positive hx
  rw [embedStage_atBase hw0 hw1 hsmall hd hs x hx,
    ← act_includeProgram hw0 hw1 hsmall hd hs hb, includeProgram_compileKernel]
  exact compileKernel_graft hw0 hw1 hsmall hd hs hN H (atBase x hx).radius
    (includeExpression hb e) (atBase x hx).expression
    ((includeExpression_within hb H e).mpr he) (atBase x hx).within

/-- Constructive finite ORIGINAL output, using the supplied input modulus. -/
def graftApproximation {base : Nat} (H : Nat) (e : WindowExpression base) (he : Within H e)
    (X : (D).Cauchy) (epsilon : Q') : Stage :=
  graftStage H e he (X.seq (X.modulus (inputTolerance (compileKernel H e) epsilon)))

theorem graftApproximation_bound {base : Nat} (H : Nat) (e : WindowExpression base)
    (he : Within H e) (X : (D).Cauchy) (epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    RCle (completedDist hw0 hw1 hsmall hd hs
      (E (graftApproximation hw0 hw1 hsmall hd hs H e he X epsilon))
      (Op (compileKernel H e) (Quotient.mk (D).completionSetoid X)))
      (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  have h := act_approximationProgram_bound hw0 hw1 hsmall hd hs
    (compileKernel H e) X epsilon hepsilon
  unfold approximationProgram at h
  rw [stageProgram_pin, compileKernel_stage_pin hw0 hw1 hsmall hd hs H e he] at h
  exact h

end YMGap.Continuum.BF4WilsonKernelOriginalInputs

#print axioms YMGap.Continuum.BF4WilsonKernelOriginalInputs.graftStage
#print axioms YMGap.Continuum.BF4WilsonKernelOriginalInputs.compileKernel_stage_pin
#print axioms YMGap.Continuum.BF4WilsonKernelOriginalInputs.graftApproximation
#print axioms YMGap.Continuum.BF4WilsonKernelOriginalInputs.graftApproximation_bound
