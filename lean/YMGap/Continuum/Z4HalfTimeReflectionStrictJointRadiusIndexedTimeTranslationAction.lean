/-
# The indexed algebraic action of strict-cylinder time translation

At a fixed admissible pair `(base, radius)`, the strict-cylinder presentation
space carries the radius-specific semantic relation.  Translation by `shift`
is therefore a setoid morphism to `(base + shift, radius + shift)`.  This file
records identity and composition, including the explicit reassociation needed
for the dependent base and radius indices, and its compatibility with vector
addition and rational scaling.

This is only the algebraic directed-system action.  It does not compare a
source reflection form with a translated reflection form and does not assert
state covariance, contraction, norm preservation, or a GNS semigroup.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointRadiusIndexedTimeTranslation

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointRadiusIndexedTimeTranslationAction

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointRadiusIndexedTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointTimeTranslationSemanticDescent
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry

/-! ## 1. Indexed setoid morphisms -/

/-- A quotient-free morphism between two radius-indexed strict-cylinder
semantic carriers. -/
structure StrictJointCylinderRadiusSetoidMorphism
    (sourceBase sourceRadius targetBase targetRadius : Nat) where
  toFun : StrictJointCylinderVector sourceBase →
    StrictJointCylinderVector targetBase
  respects : ∀ {left right},
    StrictJointCylinderVectorEquivalentAtRadius sourceRadius left right →
      StrictJointCylinderVectorEquivalentAtRadius targetRadius
        (toFun left) (toFun right)

theorem StrictJointCylinderRadiusSetoidMorphism.ext
    {sourceBase sourceRadius targetBase targetRadius : Nat}
    {left right : StrictJointCylinderRadiusSetoidMorphism
      sourceBase sourceRadius targetBase targetRadius}
    (h : ∀ vector, left.toFun vector = right.toFun vector) :
    left = right := by
  obtain ⟨leftMap, leftRespects⟩ := left
  obtain ⟨rightMap, rightRespects⟩ := right
  simp only at h
  have hmap : leftMap = rightMap := funext h
  subst rightMap
  rfl

def StrictJointCylinderRadiusSetoidMorphism.identity
    (base radius : Nat) :
    StrictJointCylinderRadiusSetoidMorphism base radius base radius where
  toFun := fun vector => vector
  respects := fun h => h

def StrictJointCylinderRadiusSetoidMorphism.comp
    {firstBase firstRadius middleBase middleRadius
      lastBase lastRadius : Nat}
    (last : StrictJointCylinderRadiusSetoidMorphism
      middleBase middleRadius lastBase lastRadius)
    (first : StrictJointCylinderRadiusSetoidMorphism
      firstBase firstRadius middleBase middleRadius) :
    StrictJointCylinderRadiusSetoidMorphism
      firstBase firstRadius lastBase lastRadius where
  toFun := fun vector => last.toFun (first.toFun vector)
  respects := fun h => last.respects (first.respects h)

@[simp] theorem StrictJointCylinderRadiusSetoidMorphism.identity_apply
    (base radius : Nat) (vector : StrictJointCylinderVector base) :
    (StrictJointCylinderRadiusSetoidMorphism.identity base radius).toFun
      vector = vector := rfl

@[simp] theorem StrictJointCylinderRadiusSetoidMorphism.comp_apply
    {firstBase firstRadius middleBase middleRadius
      lastBase lastRadius : Nat}
    (last : StrictJointCylinderRadiusSetoidMorphism
      middleBase middleRadius lastBase lastRadius)
    (first : StrictJointCylinderRadiusSetoidMorphism
      firstBase firstRadius middleBase middleRadius)
    (vector : StrictJointCylinderVector firstBase) :
    (last.comp first).toFun vector =
      last.toFun (first.toFun vector) := rfl

/-! ## 2. Explicit reindexing along arithmetic equality -/

/-- Rebase a strict-cylinder presentation along a proved equality of its base
index while keeping its roots and coefficient table literally unchanged. -/
def rebaseStrictJointCylinderVector
    {sourceBase targetBase : Nat} (hbase : sourceBase = targetBase)
    (vector : StrictJointCylinderVector sourceBase) :
    StrictJointCylinderVector targetBase where
  roots := vector.roots
  rootsCanonical := by
    intro root hroot
    rw [← hbase]
    exact vector.rootsCanonical root hroot
  coefficient := vector.coefficient

@[simp] theorem rebaseStrictJointCylinderVector_roots
    {sourceBase targetBase : Nat} (hbase : sourceBase = targetBase)
    (vector : StrictJointCylinderVector sourceBase) :
    (rebaseStrictJointCylinderVector hbase vector).roots =
      vector.roots := rfl

@[simp] theorem rebaseStrictJointCylinderVector_coefficient
    {sourceBase targetBase : Nat} (hbase : sourceBase = targetBase)
    (vector : StrictJointCylinderVector sourceBase) :
    (rebaseStrictJointCylinderVector hbase vector).coefficient =
      vector.coefficient := rfl

theorem rebaseStrictJointCylinderVector_equivalentAtRadius
    {sourceBase targetBase sourceRadius targetRadius : Nat}
    (hbase : sourceBase = targetBase)
    (hradius : sourceRadius = targetRadius)
    {left right : StrictJointCylinderVector sourceBase}
    (h : StrictJointCylinderVectorEquivalentAtRadius
      sourceRadius left right) :
    StrictJointCylinderVectorEquivalentAtRadius targetRadius
      (rebaseStrictJointCylinderVector hbase left)
      (rebaseStrictJointCylinderVector hbase right) := by
  subst targetBase
  subst targetRadius
  exact h

def reindexStrictJointCylinderRadiusMorphism
    {sourceBase targetBase sourceRadius targetRadius : Nat}
    (hbase : sourceBase = targetBase)
    (hradius : sourceRadius = targetRadius) :
    StrictJointCylinderRadiusSetoidMorphism
      sourceBase sourceRadius targetBase targetRadius where
  toFun := rebaseStrictJointCylinderVector hbase
  respects := rebaseStrictJointCylinderVector_equivalentAtRadius
    hbase hradius

/-! ## 3. Time translation as the indexed morphism -/

def timeTranslateStrictJointCylinderRadiusMorphism
    {base radius : Nat} (hbase : strictQueryBase base ≤ radius)
    (shift : Nat) :
    StrictJointCylinderRadiusSetoidMorphism
      base radius (base + shift) (radius + shift) where
  toFun := timeTranslateStrictJointCylinderVector shift
  respects := timeTranslateStrictJointCylinderVector_equivalentAtRadius hbase

@[simp] theorem timeTranslateStrictJointCylinderRadiusMorphism_apply
    {base radius : Nat} (hbase : strictQueryBase base ≤ radius)
    (shift : Nat) (vector : StrictJointCylinderVector base) :
    (timeTranslateStrictJointCylinderRadiusMorphism hbase shift).toFun
      vector = timeTranslateStrictJointCylinderVector shift vector := rfl

/-- Zero translation is the identity indexed setoid morphism. -/
theorem timeTranslateStrictJointCylinderRadiusMorphism_zero
    {base radius : Nat} (hbase : strictQueryBase base ≤ radius) :
    timeTranslateStrictJointCylinderRadiusMorphism hbase 0 =
      StrictJointCylinderRadiusSetoidMorphism.identity base radius := by
  apply StrictJointCylinderRadiusSetoidMorphism.ext
  intro vector
  exact timeTranslateStrictJointCylinderVector_zero vector

private theorem strictJointCylinderVector_ext_local
    {base : Nat} {left right : StrictJointCylinderVector base}
    (hroots : left.roots = right.roots)
    (hcoefficient : left.coefficient = right.coefficient) :
    left = right := by
  obtain ⟨leftRoots, leftCanonical, leftCoefficient⟩ := left
  obtain ⟨rightRoots, rightCanonical, rightCoefficient⟩ := right
  simp only at hroots hcoefficient
  subst rightRoots
  subst rightCoefficient
  rfl

/-- Two successive presentation translations equal the translation by the
sum after the target base is explicitly reassociated. -/
theorem rebase_timeTranslateStrictJointCylinderVector_add
    {base : Nat} (first second : Nat)
    (vector : StrictJointCylinderVector base) :
    rebaseStrictJointCylinderVector (Nat.add_assoc base first second)
        (timeTranslateStrictJointCylinderVector second
          (timeTranslateStrictJointCylinderVector first vector)) =
      timeTranslateStrictJointCylinderVector (first + second) vector := by
  apply strictJointCylinderVector_ext_local
  · change
      (vector.roots.map (timeShiftCanonicalRoot first base)).map
          (timeShiftCanonicalRoot second (base + first)) =
        vector.roots.map
          (timeShiftCanonicalRoot (first + second) base)
    rw [List.map_map]
    apply List.map_congr_left
    intro root hroot
    simp only [Function.comp_apply]
    exact timeShiftCanonicalRoot_add first second
      (vector.rootsCanonical root hroot)
  · rfl

/-- Admissibility is preserved at the first translated index. -/
theorem strictQueryBase_le_after_timeTranslate
    {base radius : Nat} (hbase : strictQueryBase base ≤ radius)
    (shift : Nat) :
    strictQueryBase (base + shift) ≤ radius + shift := by
  rw [strictQueryBase_add_shift]
  exact Nat.add_le_add_right hbase shift

/-- The indexed morphisms form the expected additive action after the
canonical associativity reindexing of both target indices. -/
theorem timeTranslateStrictJointCylinderRadiusMorphism_add
    {base radius : Nat} (hbase : strictQueryBase base ≤ radius)
    (first second : Nat) :
    (reindexStrictJointCylinderRadiusMorphism
        (Nat.add_assoc base first second)
        (Nat.add_assoc radius first second)).comp
      ((timeTranslateStrictJointCylinderRadiusMorphism
          (strictQueryBase_le_after_timeTranslate hbase first) second).comp
        (timeTranslateStrictJointCylinderRadiusMorphism hbase first)) =
      timeTranslateStrictJointCylinderRadiusMorphism
        hbase (first + second) := by
  apply StrictJointCylinderRadiusSetoidMorphism.ext
  intro vector
  exact rebase_timeTranslateStrictJointCylinderVector_add
    first second vector

/-! ## 4. Linear covariance of each indexed arrow -/

theorem timeTranslateStrictJointCylinderRadiusMorphism_map_add
    {base radius : Nat} (hbase : strictQueryBase base ≤ radius)
    (shift : Nat) (left right : StrictJointCylinderVector base) :
    (timeTranslateStrictJointCylinderRadiusMorphism hbase shift).toFun
        (left.add right) =
      ((timeTranslateStrictJointCylinderRadiusMorphism hbase shift).toFun
          left).add
        ((timeTranslateStrictJointCylinderRadiusMorphism hbase shift).toFun
          right) := by
  exact timeTranslateStrictJointCylinderVector_add shift left right

theorem timeTranslateStrictJointCylinderRadiusMorphism_map_smul
    {base radius : Nat} (hbase : strictQueryBase base ≤ radius)
    (shift : Nat) (scalar : Q')
    (vector : StrictJointCylinderVector base) :
    (timeTranslateStrictJointCylinderRadiusMorphism hbase shift).toFun
        (vector.smul scalar) =
      ((timeTranslateStrictJointCylinderRadiusMorphism hbase shift).toFun
        vector).smul scalar := by
  exact timeTranslateStrictJointCylinderVector_smul shift scalar vector

/-!
## Exact open boundary

The algebra above supplies no comparison between the source and translated
reflection forms.  The first genuinely physical half-space theorem needed
for a transfer contraction is precisely the following *unproved signature*:

```
theorem strictJointCylinder_positiveTime_reflectionQuadratic_contracts
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base shift : Nat} (vector : StrictJointCylinderVector base) :
    (timeTranslateStrictJointCylinderVector shift vector).reflectionQuadratic
        hcoupling hle ≤
      vector.reflectionQuadratic hcoupling hle
```

Its physical proof requires translation covariance of the constructed
infinite-volume state together with the half-space/reflection compression;
it does not follow from support recoding or finite Gram positivity.  Exact
state invariance of a full observable automorphism must not be substituted
for this compression law (the positive-isometric no-go fence applies).
-/

#print axioms rebaseStrictJointCylinderVector_equivalentAtRadius
#print axioms timeTranslateStrictJointCylinderRadiusMorphism_zero
#print axioms rebase_timeTranslateStrictJointCylinderVector_add
#print axioms strictQueryBase_le_after_timeTranslate
#print axioms timeTranslateStrictJointCylinderRadiusMorphism_add
#print axioms timeTranslateStrictJointCylinderRadiusMorphism_map_add
#print axioms timeTranslateStrictJointCylinderRadiusMorphism_map_smul

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointRadiusIndexedTimeTranslationAction
