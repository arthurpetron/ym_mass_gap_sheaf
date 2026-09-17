/-
# Original finite windows under the actual completed operations

These equalities keep one supplied spatial base and the literal radius-tagged
Wilson expression. Addition, rational scaling, time advance and the bounded
time-zero multiplier act by their actual original syntax. Constant windows
are identified with the existing vacuum through original source-identity
descent, not by choosing a different state or carrier.

The consumers are chronological products and general signed Wilson windows.
No arbitrary positive-time multiplication operator or continuum claim occurs.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroOperator
import YMGap.Continuum.BF4WilsonSpatialUnionSourceIdentity
import YMGap.Continuum.BF4WilsonSpatialUnionFixedBase
import YMGap.Continuum.BF4WilsonSpatialUnionLinearLaws

namespace YMGap.Continuum.BF4WilsonWindowOperatorPins

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow (shift_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression chart unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion
  (inclusion inclusion_refl includeLoop_start includeLoop_edges)
open YMGap.Continuum.BF4WilsonSpatialUnion
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionLinear
open YMGap.Continuum.BF4WilsonSpatialUnionLinearLaws (completedSmul_zero)
open YMGap.Continuum.BF4WilsonSpatialUnionPosdef (completedZero)
open YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroMultiplier
open YMGap.Continuum.BF4WilsonSpatialUnionSourceIdentity
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

private theorem sourceLoop_ext {base : Nat} (x y : SourceLoop base)
    (hstart : x.start = y.start) (hedges : x.edges = y.edges) : x = y := by
  cases x
  cases y
  cases hstart
  cases hedges
  rfl

theorem loopAt_self {base : Nat} (L : SourceLoop base) : loopAt L (Nat.le_refl base) = L :=
  sourceLoop_ext _ _ (includeLoop_start (Nat.le_refl base) L)
    (includeLoop_edges (Nat.le_refl base) L)

private theorem atBase_ofExpression_self {base : Nat} (hb : 0 < base)
    (x : IntrinsicExpression base) : atBase (ofExpression base hb x) (Nat.le_refl base) = x :=
  inclusion_refl x

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
  {base : Nat} (hb : 0 < base)

local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "E" => embedStage hw0 hw1 hsmall hd hs

private theorem embedStage_eq_atBase {larger : Nat} (x y : Stage)
    (hx : x.base ≤ larger) (hy : y.base ≤ larger) (he : atBase x hx = atBase y hy) : E x = E y := by
  apply (unionSeminorm hw0 hw1 hsmall hd hs).embedRep_eq_of_null
  have hpin := distSq_at_base hw0 hw1 hsmall hd hs x y larger hx hy
  rw [he] at hpin
  exact hpin.trans (BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.distSq_refl
    hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le x.positive hx) (atBase y hy))

def embedWindow (H : Nat) (e : WindowExpression base) (he : Within H e) : V :=
  E (ofExpression base hb ⟨H,e,he⟩)

theorem embedWindow_one (H : Nat) :
    embedWindow hw0 hw1 hsmall hd hs hb H .one True.intro =
      completedUnit hw0 hw1 hsmall hd hs := by
  have hunit := BF4WilsonSpatialUnionFixedBase.completionMap_unit hw0 hw1 hsmall hd hs hb
  rw [BF4WilsonSpatialUnionFixedBase.map_embed] at hunit
  refine Eq.trans ?_ hunit
  apply embedStage_eq_of_source_identity hw0 hw1 hsmall hd hs hb H
    ⟨H,.one,True.intro⟩ (unit base) (Nat.le_refl _) (Nat.zero_le _)
  exact PaddedPolynomialCoeffEqv.refl _ _

theorem completedAdd_embedWindow (H : Nat) (e f : WindowExpression base)
    (he : Within H e) (hf : Within H f) :
    completedAdd hw0 hw1 hsmall hd hs
      (embedWindow hw0 hw1 hsmall hd hs hb H e he)
      (embedWindow hw0 hw1 hsmall hd hs hb H f hf) =
      embedWindow hw0 hw1 hsmall hd hs hb H (.add e f) ⟨he,hf⟩ := by
  unfold embedWindow
  rw [completedAdd_embedStage]
  apply embedStage_eq_atBase hw0 hw1 hsmall hd hs (larger := base) _ _
    (Nat.max_le.mpr ⟨Nat.le_refl _,Nat.le_refl _⟩) (Nat.le_refl _)
  simp only [atBase_ofExpression_self]
  have hsum := atBase_sum (ofExpression base hb ⟨H,e,he⟩) (ofExpression base hb ⟨H,f,hf⟩)
    (larger := base) (Nat.le_refl _) (Nat.le_refl _)
  simpa only [atBase_ofExpression_self,
    BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.sum, chart, Nat.max_self,
    Nat.sub_self, shift_zero] using hsum

theorem completedSmul_embedWindow (H : Nat) (c : Q') (e : WindowExpression base)
    (he : Within H e) :
    completedSmul hw0 hw1 hsmall hd hs c (embedWindow hw0 hw1 hsmall hd hs hb H e he) =
      embedWindow hw0 hw1 hsmall hd hs hb H (.smul c e) he := rfl

theorem embedWindow_zero (H : Nat) :
    embedWindow hw0 hw1 hsmall hd hs hb H (.smul 0 .one) True.intro =
      completedZero hw0 hw1 hsmall hd hs := by
  rw [← completedSmul_embedWindow]
  exact completedSmul_zero hw0 hw1 hsmall hd hs _

theorem completedMultiply_embedWindow (H : Nat) (L : SourceLoop base) (spin : Nat)
    (e : WindowExpression base) (he : Within H e) :
    completedMultiply hw0 hw1 hsmall hd hs L spin (embedWindow hw0 hw1 hsmall hd hs hb H e he) =
      embedWindow hw0 hw1 hsmall hd hs hb H (.mul (.loop H L spin) e) ⟨Nat.le_refl _,he⟩ := by
  unfold embedWindow
  rw [completedMultiply_embedStage]
  apply embedStage_eq_atBase hw0 hw1 hsmall hd hs (larger := base) _ _
    (Nat.max_le.mpr ⟨Nat.le_refl _,Nat.le_refl _⟩) (Nat.le_refl _)
  simp only [atBase_ofExpression_self]
  have hmul := atBase_multiply L spin (ofExpression base hb ⟨H,e,he⟩)
    (larger := base) (Nat.le_refl _) (Nat.le_refl _)
  simpa only [atBase_ofExpression_self, loopAt_self,
    BF4WilsonTimeZeroIntrinsicMultiplier.multiply] using hmul

theorem completedTime_embedWindow (H n : Nat) (e : WindowExpression base) (he : Within H e) :
    completedTime hw0 hw1 hsmall hd hs n (embedWindow hw0 hw1 hsmall hd hs hb H e he) =
      embedWindow hw0 hw1 hsmall hd hs hb (H+n) e
        (within_mono (Nat.le_add_right _ _) e he) := rfl

#print axioms loopAt_self
#print axioms embedWindow
#print axioms embedWindow_one
#print axioms completedAdd_embedWindow
#print axioms completedSmul_embedWindow
#print axioms embedWindow_zero
#print axioms completedMultiply_embedWindow
#print axioms completedTime_embedWindow

end YMGap.Continuum.BF4WilsonWindowOperatorPins
