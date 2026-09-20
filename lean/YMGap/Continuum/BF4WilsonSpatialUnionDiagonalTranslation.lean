/-
# Diagonal spatial isometries of the SAME completed Wilson carrier

The new exact cofinal-box identity for original Wilson expressions supplies
the original union-distance bound. The existing completion map therefore
constructs positive diagonal spatial translations, retaining each supplied
Cauchy modulus unchanged. Its original pairing, physical discrete time and
vacuum are preserved. No older plaquette-only carrier is substituted.

This is a fixed-spacing, small-nome SU(2) spatial-symmetry result. Independent
signed-axis translations, inverses, continuum Euclidean covariance and the
changing-spacing/physical-mass/QFT/all-group joins are not supplied here.
-/

import YMGap.Continuum.BF4WilsonDiagonalTranslationForm
import YMGap.Continuum.BF4WilsonSpatialUnionPairingData
import YMGap.Continuum.BF4WilsonSpatialUnionCompletedGap
import YMGap.Continuum.BF4WilsonSpatialUnionCompletedDistance

namespace YMGap.Continuum.BF4WilsonSpatialUnionDiagonalTranslation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonDiagonalTranslationSyntax
open YMGap.Continuum.BF4WilsonSpatialUnion
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedGap (completedCenteredScalar)
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedDistance
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (unit)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- The actual ordered Wilson loops are shifted, not just their support labels. -/
def stageTranslate (s : Nat) (x : Stage) : Stage :=
  ⟨x.base+2*s, by have := x.positive; omega, translate s x.value⟩

private theorem stage_eq {x y : Stage} (hb : x.base = y.base)
    (hx : HEq x.value y.value) : x = y := by
  cases x with
  | mk a ha xa =>
    cases y with
    | mk b hb' yb =>
      dsimp at hb hx
      cases hb
      have hxy := eq_of_heq hx
      cases hxy
      rfl

theorem stageTranslate_zero (x : Stage) : stageTranslate 0 x = x :=
  stage_eq (by simp only [stageTranslate, Nat.mul_zero, Nat.add_zero]) (translate_zero x.value)

theorem stageTranslate_add (m n : Nat) (x : Stage) :
    stageTranslate (m+n) x = stageTranslate m (stageTranslate n x) :=
  stage_eq (by dsimp only [stageTranslate]; omega) (translate_add m n x.value)

theorem stageTranslate_time (s n : Nat) (x : Stage) :
    stageTranslate s (time n x) = time n (stageTranslate s x) := rfl

theorem stageTranslate_atBase (s : Nat) (x : Stage) {larger : Nat} (h : x.base ≤ larger) :
    atBase (stageTranslate s x) (Nat.add_le_add_right h (2*s)) =
      translate s (atBase x h) := translate_inclusion h s x.value

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "D" => unionSeminorm hw0 hw1 hsmall hd hs
local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "T" => completedTime hw0 hw1 hsmall hd hs
local notation "U" => completedUnit hw0 hw1 hsmall hd hs

/-- Both inputs use one computed common base; no uniform support is assumed. -/
theorem pairing_translate (s : Nat) (x y : Stage) :
    Equiv (pairing hw0 hw1 hsmall hd hs (stageTranslate s x) (stageTranslate s y))
      (pairing hw0 hw1 hsmall hd hs x y) := by
  let base := max x.base y.base
  have hx : x.base ≤ base := Nat.le_max_left _ _
  have hy : y.base ≤ base := Nat.le_max_right _ _
  have hl := pairing_at_base hw0 hw1 hsmall hd hs (stageTranslate s x) (stageTranslate s y)
    (base+2*s) (Nat.add_le_add_right hx (2*s)) (Nat.add_le_add_right hy (2*s))
  rw [stageTranslate_atBase s x hx, stageTranslate_atBase s y hy] at hl
  exact hl.trans ((BF4WilsonDiagonalTranslationForm.intrinsicForm_translate hw0 hw1 hsmall hd hs
    (Nat.lt_of_lt_of_le x.positive hx) s (atBase x hx) (atBase y hy)).trans
      (pairing_at_base hw0 hw1 hsmall hd hs x y base hx hy).symm)

theorem distSq_translate (s : Nat) (x y : Stage) :
    Equiv (distSq hw0 hw1 hsmall hd hs (stageTranslate s x) (stageTranslate s y))
      (distSq hw0 hw1 hsmall hd hs x y) := by
  let base := max x.base y.base
  have hx : x.base ≤ base := Nat.le_max_left _ _
  have hy : y.base ≤ base := Nat.le_max_right _ _
  have hl := distSq_at_base hw0 hw1 hsmall hd hs (stageTranslate s x) (stageTranslate s y)
    (base+2*s) (Nat.add_le_add_right hx (2*s)) (Nat.add_le_add_right hy (2*s))
  rw [stageTranslate_atBase s x hx, stageTranslate_atBase s y hy] at hl
  exact hl.trans ((BF4WilsonDiagonalTranslationForm.distSq_translate hw0 hw1 hsmall hd hs
    (Nat.lt_of_lt_of_le x.positive hx) s (atBase x hx) (atBase y hy)).trans
      (distSq_at_base hw0 hw1 hsmall hd hs x y base hx hy).symm)

def translationNonexpansive (s : Nat) : (D).Nonexpansive where
  toFun := stageTranslate s
  contraction := fun x y => leEv_of_equiv (distSq_translate hw0 hw1 hsmall hd hs s x y)

def translationSemigroup : (D).NonexpansiveSemigroup where
  op := translationNonexpansive hw0 hw1 hsmall hd hs
  zero_law := by
    intro x
    change Equiv (distSq hw0 hw1 hsmall hd hs (stageTranslate 0 x) x) czero
    rw [stageTranslate_zero]
    exact distance_refl hw0 hw1 hsmall hd hs x
  add_law := by
    intro m n x
    change Equiv (distSq hw0 hw1 hsmall hd hs (stageTranslate (m+n) x)
      (stageTranslate m (stageTranslate n x))) czero
    rw [stageTranslate_add]
    exact distance_refl hw0 hw1 hsmall hd hs _

/-- An actual map of the existing Wilson completion; not a separately supplied space. -/
def completedTranslation (s : Nat) : V → V :=
  (translationNonexpansive hw0 hw1 hsmall hd hs s).completionMap

theorem translation_cauchy_modulus (s : Nat) (X : (D).Cauchy) :
    ((translationNonexpansive hw0 hw1 hsmall hd hs s).mapCauchy X).modulus = X.modulus := rfl

theorem completedTranslation_embedStage (s : Nat) (x : Stage) :
    completedTranslation hw0 hw1 hsmall hd hs s (embedStage hw0 hw1 hsmall hd hs x) =
      embedStage hw0 hw1 hsmall hd hs (stageTranslate s x) := rfl

theorem completedTranslation_zero (x : V) :
    completedTranslation hw0 hw1 hsmall hd hs 0 x = x :=
  (translationSemigroup hw0 hw1 hsmall hd hs).completionMap_zero x

theorem completedTranslation_add (m n : Nat) (x : V) :
    completedTranslation hw0 hw1 hsmall hd hs (m+n) x =
      completedTranslation hw0 hw1 hsmall hd hs m
        (completedTranslation hw0 hw1 hsmall hd hs n x) :=
  (translationSemigroup hw0 hw1 hsmall hd hs).completionMap_add m n x

/-- Spatial translation commutes with the SAME discrete physical time. -/
theorem completedTranslation_time (s n : Nat) (x : V) :
    completedTranslation hw0 hw1 hsmall hd hs s (T n x) =
      T n (completedTranslation hw0 hw1 hsmall hd hs s x) := by
  refine Quotient.inductionOn x ?_
  intro X
  apply Quotient.sound
  refine ⟨CRealSeminormCompletion.SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull
    (fun k => ?_)⟩
  change Equiv (distSq hw0 hw1 hsmall hd hs (stageTranslate s (time n (X.seq k)))
    (time n (stageTranslate s (X.seq k)))) czero
  rw [stageTranslate_time]
  exact distance_refl hw0 hw1 hsmall hd hs _

theorem stageTranslate_unit_null (s : Nat) :
    Equiv (distSq hw0 hw1 hsmall hd hs (stageTranslate s unitStage) unitStage) czero := by
  have h := distSq_at_base hw0 hw1 hsmall hd hs (stageTranslate s unitStage) unitStage
    (1+2*s) (Nat.le_refl _) (by change 1 ≤ 1+2*s; omega)
  change Equiv (distSq hw0 hw1 hsmall hd hs (stageTranslate s unitStage) unitStage)
    (BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.distSq hw0 hw1 hsmall hd hs (by omega)
      (unit (1+2*s)) (unit (1+2*s))) at h
  exact h.trans (BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.distSq_refl
    hw0 hw1 hsmall hd hs (by omega) _)

theorem completedTranslation_unit (s : Nat) :
    completedTranslation hw0 hw1 hsmall hd hs s U = U := by
  apply Quotient.sound
  exact ⟨CRealSeminormCompletion.SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull
    (fun _ => stageTranslate_unit_null hw0 hw1 hsmall hd hs s)⟩

/-- Original completed mixed form preserved on arbitrary represented inputs. -/
theorem completedInner_translate (s : Nat) (x y : V) :
    B (completedTranslation hw0 hw1 hsmall hd hs s x)
      (completedTranslation hw0 hw1 hsmall hd hs s y) = B x y := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  apply Quotient.sound
  exact Equiv_of_limit_of_equal
    (fun k => pairing_translate hw0 hw1 hsmall hd hs s (X.seq k) (Y.seq k))
    (CRealSeminormPairingCompletion.pairSequence_converges (pairingData hw0 hw1 hsmall hd hs)
      ((translationNonexpansive hw0 hw1 hsmall hd hs s).mapCauchy X)
      ((translationNonexpansive hw0 hw1 hsmall hd hs s).mapCauchy Y))
    (CRealSeminormPairingCompletion.pairSequence_converges (pairingData hw0 hw1 hsmall hd hs) X Y)

/-- Exact squared-distance preservation, stronger than the initial nonexpansive bound. -/
theorem completedDist_translate (s : Nat) (x y : V) :
    completedDist hw0 hw1 hsmall hd hs
      (completedTranslation hw0 hw1 hsmall hd hs s x)
      (completedTranslation hw0 hw1 hsmall hd hs s y) =
      completedDist hw0 hw1 hsmall hd hs x y := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  apply Quotient.sound
  exact Equiv_of_limit_of_equal
    (fun k => distSq_translate hw0 hw1 hsmall hd hs s (X.seq k) (Y.seq k))
    (representativeDist_converges hw0 hw1 hsmall hd hs
      ((translationNonexpansive hw0 hw1 hsmall hd hs s).mapCauchy X)
      ((translationNonexpansive hw0 hw1 hsmall hd hs s).mapCauchy Y))
    (representativeDist_converges hw0 hw1 hsmall hd hs X Y)

theorem completedTranslation_injective (s : Nat) (x y : V)
    (h : completedTranslation hw0 hw1 hsmall hd hs s x =
      completedTranslation hw0 hw1 hsmall hd hs s y) : x = y := by
  apply (completedDist_zero_iff hw0 hw1 hsmall hd hs x y).mp
  rw [← completedDist_translate hw0 hw1 hsmall hd hs s x y, h, completedDist_refl]

/-- The SAME observable/time/vacuum connected scalar is spatially invariant. -/
theorem completedCenteredScalar_translate (s n : Nat) (x y : V) :
    completedCenteredScalar hw0 hw1 hsmall hd hs n
      (completedTranslation hw0 hw1 hsmall hd hs s x)
      (completedTranslation hw0 hw1 hsmall hd hs s y) =
      completedCenteredScalar hw0 hw1 hsmall hd hs n x y := by
  unfold completedCenteredScalar
  rw [← completedTranslation_time, completedInner_translate]
  have hx := completedInner_translate hw0 hw1 hsmall hd hs s x U
  have hy := completedInner_translate hw0 hw1 hsmall hd hs s U y
  rw [completedTranslation_unit] at hx hy
  rw [hx, hy]

#print axioms stageTranslate
#print axioms stageTranslate_zero
#print axioms stageTranslate_add
#print axioms stageTranslate_time
#print axioms stageTranslate_atBase
#print axioms pairing_translate
#print axioms distSq_translate
#print axioms translationNonexpansive
#print axioms translationSemigroup
#print axioms completedTranslation
#print axioms translation_cauchy_modulus
#print axioms completedTranslation_embedStage
#print axioms completedTranslation_zero
#print axioms completedTranslation_add
#print axioms completedTranslation_time
#print axioms stageTranslate_unit_null
#print axioms completedTranslation_unit
#print axioms completedInner_translate
#print axioms completedDist_translate
#print axioms completedTranslation_injective
#print axioms completedCenteredScalar_translate

end YMGap.Continuum.BF4WilsonSpatialUnionDiagonalTranslation
