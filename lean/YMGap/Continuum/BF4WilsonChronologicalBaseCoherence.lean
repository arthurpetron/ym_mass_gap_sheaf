/-
# Spatial support inclusions preserve the original completed operators

Increasing a loop's witnessed support base retains its physical edges. A
computed common base therefore makes the two multiplier actions literally
equal on stages; the same zero-distance identity passes through their existing
Cauchy maps. Finite programs inherit all-input coherence, not merely vacuum
coherence. No common spatial base for a Cauchy stream is selected.
-/

import YMGap.Continuum.BF4WilsonKernelInclusionSyntax

namespace YMGap.Continuum.BF4WilsonChronologicalBaseCoherence

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression)
open YMGap.Continuum.BF4WilsonSpatialUnion
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroMultiplier
open YMGap.Continuum.BF4WilsonChronologicalProgram
open YMGap.Continuum.BF4WilsonChronologicalOperator
open YMGap.Continuum.BF4WilsonKernelInclusionSyntax
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "D" => unionSeminorm hw0 hw1 hsmall hd hs
local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "E" => embedStage hw0 hw1 hsmall hd hs

/-- A supplied larger support is the SAME completed vector. -/
theorem embedStage_atBase (x : Stage) {larger : Nat} (h : x.base ≤ larger) :
    E x = E (ofExpression larger (Nat.lt_of_lt_of_le x.positive h) (atBase x h)) := by
  apply (D).embedRep_eq_of_null
  have hp := distSq_at_base hw0 hw1 hsmall hd hs x
    (ofExpression larger (Nat.lt_of_lt_of_le x.positive h) (atBase x h)) larger h (Nat.le_refl _)
  simp only [atBase, ofExpression, inclusion_refl] at hp
  exact hp.trans (BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.distSq_refl
    hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le x.positive h) _)

theorem completedMultiply_loopAt {base larger : Nat} (h : base ≤ larger)
    (L : SourceLoop base) (spin : Nat) (x : V) :
    completedMultiply hw0 hw1 hsmall hd hs (loopAt L h) spin x =
      completedMultiply hw0 hw1 hsmall hd hs L spin x := by
  refine Quotient.inductionOn x ?_
  intro X
  apply Quotient.sound
  refine ⟨CRealSeminormCompletion.SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull
    (fun k => ?_)⟩
  let y := X.seq k
  let N := max larger y.base
  have hb : base ≤ N := Nat.le_trans h (Nat.le_max_left _ _)
  have hl : larger ≤ N := Nat.le_max_left _ _
  have hy : y.base ≤ N := Nat.le_max_right _ _
  have hp := distSq_at_base hw0 hw1 hsmall hd hs
    (multiplyStage (loopAt L h) spin y) (multiplyStage L spin y) N
    (Nat.max_le.mpr ⟨hl,hy⟩) (Nat.max_le.mpr ⟨hb,hy⟩)
  simp only [atBase_multiply (loopAt L h) spin y hl hy,
    atBase_multiply L spin y hb hy, loopAt_trans] at hp
  exact hp.trans (BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.distSq_refl
    hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le y.positive hy) _)

theorem act_includeProgram {base larger : Nat} (h : base ≤ larger)
    (p : Program base) (x : V) :
    act hw0 hw1 hsmall hd hs (includeProgram h p) x = act hw0 hw1 hsmall hd hs p x := by
  induction p <;> simp only [includeProgram, act, completedMultiply_loopAt, *]

theorem adjointAct_includeProgram {base larger : Nat} (h : base ≤ larger)
    (p : Program base) (x : V) :
    adjointAct hw0 hw1 hsmall hd hs (includeProgram h p) x =
      adjointAct hw0 hw1 hsmall hd hs p x := by
  induction p generalizing x <;>
    simp only [includeProgram, adjointAct, completedMultiply_loopAt, *]

end YMGap.Continuum.BF4WilsonChronologicalBaseCoherence

#print axioms YMGap.Continuum.BF4WilsonChronologicalBaseCoherence.embedStage_atBase
#print axioms YMGap.Continuum.BF4WilsonChronologicalBaseCoherence.completedMultiply_loopAt
#print axioms YMGap.Continuum.BF4WilsonChronologicalBaseCoherence.act_includeProgram
#print axioms YMGap.Continuum.BF4WilsonChronologicalBaseCoherence.adjointAct_includeProgram
