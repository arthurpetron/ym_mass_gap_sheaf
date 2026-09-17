/-
# A time-zero Wilson multiplier applied to the existing vacuum

The bounded completed multiplier sends the existing completed unit to the
already embedded radius-zero loop expression. Zero-spatial-shift inclusion
retains the literal source loop, and multiplication by the unit is proved
by the actual polynomial identity before observable descent is applied.

The original discrete time orbit is consequently the original loop state's
orbit on the SAME completion. This is not cyclicity of all gauge observables,
an identification of arbitrary OS-null products, or continuum QFT closure.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroMultiplier
import YMGap.Continuum.BF4WilsonSpatialUnionObservableDescent

namespace YMGap.Continuum.BF4WilsonTimeZeroVacuum

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow (shift_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion
  (includeLoop_start includeLoop_edges)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression chart unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison (chartInsertion)
open YMGap.Continuum.BF4WilsonTimeZeroIntrinsicMultiplier (multiply)
open YMGap.Continuum.BF4WilsonSpatialUnion
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroMultiplier
open YMGap.Continuum.BF4WilsonSpatialUnionObservableDescent
  (intrinsic_distSq_zero_of_padded_diagonal)
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- The original source loop on the radius-zero slice, with its support proof. -/
def loopExpression {base : Nat} (L : SourceLoop base) (spin : Nat) :
    IntrinsicExpression base :=
  ⟨0, .loop 0 L spin, Nat.le_refl 0⟩

def loopStage {base : Nat} (hb : 0 < base) (L : SourceLoop base) (spin : Nat) : Stage :=
  ofExpression base hb (loopExpression L spin)

private theorem sourceLoop_ext {base : Nat} (x y : SourceLoop base)
    (hstart : x.start = y.start) (hedges : x.edges = y.edges) : x = y := by
  cases x
  cases y
  cases hstart
  cases hedges
  rfl

private theorem loopAt_self {base : Nat} (L : SourceLoop base) :
    loopAt L (Nat.le_refl base) = L :=
  sourceLoop_ext _ _ (includeLoop_start (Nat.le_refl base) L)
    (includeLoop_edges (Nat.le_refl base) L)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
  {base : Nat} (hb : 0 < base)

/-- A named existing embedded state, not a new carrier or completion. -/
def loopState (L : SourceLoop base) (spin : Nat) : UnionCompletion hw0 hw1 hsmall hd hs :=
  embedStage hw0 hw1 hsmall hd hs (loopStage hb L spin)

attribute [local irreducible] BF4WilsonSpatialUnion.distSq
  BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.distSq

private theorem multiply_unit_distSq_zero (L : SourceLoop base) (spin : Nat) :
    Equiv (BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.distSq
      hw0 hw1 hsmall hd hs hb (multiply L spin (unit base)) (loopExpression L spin)) czero := by
  apply intrinsic_distSq_zero_of_padded_diagonal hw0 hw1 hsmall hd hs hb 0
    (multiply L spin (unit base)) (loopExpression L spin) (Nat.le_refl _) (Nat.le_refl _)
  intro n
  simp only [chart, multiply, unit, loopExpression, Nat.sub_self, shift_zero]
  exact PaddedPolynomialCoeffEqv.of_coeff
    (BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.RatPolyCoeffEqv.mul_one
      (chartInsertion n 0 n (.loop 0 L spin)))

/-- The actual bounded multiplier creates the original embedded loop state
from the already constructed unit, retaining every original analytic guard. -/
theorem completedMultiply_unit (L : SourceLoop base) (spin : Nat) :
    completedMultiply hw0 hw1 hsmall hd hs L spin (completedUnit hw0 hw1 hsmall hd hs) =
      loopState hw0 hw1 hsmall hd hs hb L spin := by
  change completedMultiply hw0 hw1 hsmall hd hs L spin
    (embedStage hw0 hw1 hsmall hd hs unitStage) =
      embedStage hw0 hw1 hsmall hd hs (loopStage hb L spin)
  rw [completedMultiply_embedStage]
  apply (unionSeminorm hw0 hw1 hsmall hd hs).embedRep_eq_of_null
  change Equiv (distSq hw0 hw1 hsmall hd hs
    (multiplyStage L spin unitStage) (loopStage hb L spin)) czero
  have hu : unitStage.base ≤ base := hb
  have hpin := distSq_at_base hw0 hw1 hsmall hd hs
    (multiplyStage L spin unitStage) (loopStage hb L spin) base
    (Nat.max_le.mpr ⟨Nat.le_refl _, hu⟩) (Nat.le_refl _)
  have hloop : atBase (loopStage hb L spin) (Nat.le_refl base) = loopExpression L spin :=
    BF4ExactSlabFixedSpatialWilsonBaseInclusion.inclusion_refl _
  simp only [atBase_multiply L spin unitStage (Nat.le_refl _) hu,
    atBase_unit hu, loopAt_self, hloop] at hpin
  exact hpin.trans (multiply_unit_distSq_zero hw0 hw1 hsmall hd hs hb L spin)

/-- The multiplier-created state's discrete time is the existing original
radius-advanced loop state, not a new dynamical action. -/
theorem completedTime_multiply_unit (n : Nat) (L : SourceLoop base) (spin : Nat) :
    completedTime hw0 hw1 hsmall hd hs n
      (completedMultiply hw0 hw1 hsmall hd hs L spin (completedUnit hw0 hw1 hsmall hd hs)) =
      embedStage hw0 hw1 hsmall hd hs
        (ofExpression base hb (advance n (loopExpression L spin))) := by
  rw [completedMultiply_unit hw0 hw1 hsmall hd hs hb L spin]
  exact completedTime_embedStage hw0 hw1 hsmall hd hs n (loopStage hb L spin)

#print axioms loopExpression
#print axioms loopStage
#print axioms loopState
#print axioms completedMultiply_unit
#print axioms completedTime_multiply_unit

end YMGap.Continuum.BF4WilsonTimeZeroVacuum
