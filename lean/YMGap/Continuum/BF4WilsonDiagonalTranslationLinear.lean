/-
# Linearity of the SAME completed Wilson diagonal translations

Literal recentering commutes with the finite signed algebra. At a computed
common base this gives zero distance between translating a sum and summing
the translates. Quotient descent uses the supplied Cauchy sequences, without
choosing representatives or requiring a support bound for a whole stream.

The consumer is covariance of the existing chronological Wilson operators.
Only rational linearity of the positive diagonal spatial action is asserted;
no inverse, independent-axis action or continuum symmetry is constructed.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionDiagonalTranslation
import YMGap.Continuum.BF4WilsonSpatialUnionLinear

namespace YMGap.Continuum.BF4WilsonDiagonalTranslationLinear

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonDiagonalTranslationSyntax
open YMGap.Continuum.BF4WilsonSpatialUnionDiagonalTranslation
open YMGap.Continuum.BF4WilsonSpatialUnion
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionLinear
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
open YMGap.Continuum.BF4WilsonSpatialUnionPosdef
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression chart)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm (sum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra (smul)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter (recenterExpression)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

private theorem intrinsic_ext {base : Nat} (x y : IntrinsicExpression base)
    (hr : x.radius = y.radius) (he : x.expression = y.expression) : x = y := by
  cases x
  cases y
  cases hr
  cases he
  rfl

theorem translate_sum {base : Nat} (s : Nat) (x y : IntrinsicExpression base) :
    translate s (sum x y) = sum (translate s x) (translate s y) := by
  apply intrinsic_ext
  · rfl
  · change translateExpression s
      (.add (chart (max x.radius y.radius) x) (chart (max x.radius y.radius) y)) =
      .add (chart (max x.radius y.radius) (translate s x))
        (chart (max x.radius y.radius) (translate s y))
    rw [translate_chart, translate_chart]
    rfl

theorem translate_smul {base : Nat} (s : Nat) (c : Q') (x : IntrinsicExpression base) :
    translate s (smul c x) = smul c (translate s x) := rfl

theorem stageTranslate_smul (s : Nat) (c : Q') (x : Stage) :
    stageTranslate s (smulStage c x) = smulStage c (stageTranslate s x) := rfl

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "A" => completedAdd hw0 hw1 hsmall hd hs
local notation "S" => completedSmul hw0 hw1 hsmall hd hs
local notation "Z" => completedZero hw0 hw1 hsmall hd hs
local notation "R" => completedTranslation hw0 hw1 hsmall hd hs

attribute [local irreducible] distSq
  BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.distSq

/-- Computed common-base equality supplies the original null-distance witness. -/
theorem stageTranslate_sum_null (s : Nat) (x y : Stage) :
    Equiv (distSq hw0 hw1 hsmall hd hs (stageTranslate s (sumStage x y))
      (sumStage (stageTranslate s x) (stageTranslate s y))) czero := by
  let base := max x.base y.base
  have hx : x.base ≤ base := Nat.le_max_left _ _
  have hy : y.base ≤ base := Nat.le_max_right _ _
  have h := distSq_at_base hw0 hw1 hsmall hd hs
    (stageTranslate s (sumStage x y)) (sumStage (stageTranslate s x) (stageTranslate s y))
    (base+2*s) (Nat.le_refl _)
    (Nat.max_le.mpr ⟨Nat.add_le_add_right hx (2*s), Nat.add_le_add_right hy (2*s)⟩)
  rw [stageTranslate_atBase s (sumStage x y) (larger := base) (Nat.le_refl base), atBase_sum x y hx hy,
    translate_sum, atBase_sum (stageTranslate s x) (stageTranslate s y)
      (Nat.add_le_add_right hx (2*s)) (Nat.add_le_add_right hy (2*s)),
    stageTranslate_atBase s x hx, stageTranslate_atBase s y hy] at h
  exact h.trans (BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.distSq_refl
    hw0 hw1 hsmall hd hs _ _)

theorem completedTranslation_add_vectors (s : Nat) (x y : V) :
    R s (A x y) = A (R s x) (R s y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  apply Quotient.sound
  exact ⟨CRealSeminormCompletion.SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull
    (fun k => stageTranslate_sum_null hw0 hw1 hsmall hd hs s (X.seq k) (Y.seq k))⟩

theorem completedTranslation_smul (s : Nat) (c : Q') (x : V) :
    R s (S c x) = S c (R s x) := by
  refine Quotient.inductionOn x ?_
  intro X
  apply Quotient.sound
  refine ⟨CRealSeminormCompletion.SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull
    (fun k => ?_)⟩
  change Equiv (distSq hw0 hw1 hsmall hd hs (stageTranslate s (smulStage c (X.seq k)))
    (smulStage c (stageTranslate s (X.seq k)))) czero
  rw [stageTranslate_smul]
  exact distance_refl hw0 hw1 hsmall hd hs _

theorem completedTranslation_zero_vector (s : Nat) : R s Z = Z := by
  apply (completedInner_posdef hw0 hw1 hsmall hd hs _).mp
  rw [completedInner_translate, completedInner_zero_left]

#print axioms translate_sum
#print axioms translate_smul
#print axioms stageTranslate_smul
#print axioms stageTranslate_sum_null
#print axioms completedTranslation_add_vectors
#print axioms completedTranslation_smul
#print axioms completedTranslation_zero_vector

end YMGap.Continuum.BF4WilsonDiagonalTranslationLinear
