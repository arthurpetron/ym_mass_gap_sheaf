/-
# Spatial union squared seminorm and its actual physical-time completion

All distance laws are transported to one computed finite common base.
In particular, nullity is nullity in the spatial limiting form; it is never
asserted at a finite regulator. The completion allows supplied Cauchy streams
whose support bases grow without bound. Original time advance acts on each
stage and retains every supplied stream modulus.

This constructs a carrier and time semigroup, not metric completeness,
the full observable algebra, or a continuum Hamiltonian.
-/

import YMGap.Continuum.BF4SpatialUnion
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime

namespace YMGap.Continuum.BF4SpatialUnionSeminorm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.BF4SpatialUnion
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime (spatialPhysicalTime_contraction)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "d" => distSq hw0 hw1 hsmall hd hs

attribute [local irreducible] distSq spatialDistSq

theorem distance_refl (x : Stage) : Equiv (d x x) czero := by
  have h := distSq_at_base hw0 hw1 hsmall hd hs x x x.base (Nat.le_refl _) (Nat.le_refl _)
  simp only [atBase_self] at h
  exact h.trans (spatialDistSq_refl hw0 hw1 x.base hsmall hd hs x.positive x.value)

theorem distance_symm (x y : Stage) : Equiv (d x y) (d y x) := by
  let N := max x.base y.base
  have hx : x.base ≤ N := Nat.le_max_left _ _
  have hy : y.base ≤ N := Nat.le_max_right _ _
  exact (distSq_at_base hw0 hw1 hsmall hd hs x y N hx hy).trans
    ((spatialDistSq_symm hw0 hw1 N hsmall hd hs (Nat.lt_of_lt_of_le x.positive hx)
      (atBase x hx) (atBase y hy)).trans
      (distSq_at_base hw0 hw1 hsmall hd hs y x N hy hx).symm)

theorem distance_nonnegative (x y : Stage) : leEv czero (d x y) := by
  unfold distSq
  exact spatialDistSq_nonnegative hw0 hw1 _ hsmall hd hs _ _ _

theorem distance_triangle (x y z : Stage) :
    leEv (d x z) (add (add (d x y) (d x y)) (add (d y z) (d y z))) := by
  let N := max x.base (max y.base z.base)
  have hx : x.base ≤ N := by omega
  have hy : y.base ≤ N := by omega
  have hz : z.base ≤ N := by omega
  have hxy := distSq_at_base hw0 hw1 hsmall hd hs x y N hx hy
  have hyz := distSq_at_base hw0 hw1 hsmall hd hs y z N hy hz
  exact leEv_trans (leEv_of_equiv (distSq_at_base hw0 hw1 hsmall hd hs x z N hx hz))
    (leEv_trans (spatialDistSq_triangle hw0 hw1 N hsmall hd hs (Nat.lt_of_lt_of_le x.positive hx)
      (atBase x hx) (atBase y hy) (atBase z hz))
      (leEv_of_equiv (Equiv_add (Equiv_add hxy hxy) (Equiv_add hyz hyz)).symm))

theorem distance_null_congr {x x' y y' : Stage}
    (hx : Equiv (d x x') czero) (hy : Equiv (d y y') czero) :
    Equiv (d x y) (d x' y') := by
  let N := max (max x.base x'.base) (max y.base y'.base)
  have hxN : x.base ≤ N := by omega
  have hxN' : x'.base ≤ N := by omega
  have hyN : y.base ≤ N := by omega
  have hyN' : y'.base ≤ N := by omega
  have hx0 := (distSq_at_base hw0 hw1 hsmall hd hs x x' N hxN hxN').symm.trans hx
  have hy0 := (distSq_at_base hw0 hw1 hsmall hd hs y y' N hyN hyN').symm.trans hy
  exact (distSq_at_base hw0 hw1 hsmall hd hs x y N hxN hyN).trans
    ((spatialDistSq_null_congr hw0 hw1 N hsmall hd hs (Nat.lt_of_lt_of_le x.positive hxN)
      hx0 hy0).trans (distSq_at_base hw0 hw1 hsmall hd hs x' y' N hxN' hyN').symm)

/-- All fields are proved from the original coherent spatial-limit distance. -/
def unionSeminorm : SquaredSeminorm where
  Carrier := Stage
  distSq := d
  distSq_refl := distance_refl hw0 hw1 hsmall hd hs
  distSq_symm := distance_symm hw0 hw1 hsmall hd hs
  distSq_nonneg := distance_nonnegative hw0 hw1 hsmall hd hs
  distSq_triangle := distance_triangle hw0 hw1 hsmall hd hs
  null_congr := distance_null_congr hw0 hw1 hsmall hd hs

local notation "D" => unionSeminorm hw0 hw1 hsmall hd hs

theorem time_contraction (n : Nat) (x y : Stage) :
    leEv (d (time n x) (time n y)) (d x y) := by
  let N := max x.base y.base
  have hx : x.base ≤ N := Nat.le_max_left _ _
  have hy : y.base ≤ N := Nat.le_max_right _ _
  have h := spatialPhysicalTime_contraction hw0 hw1 N hsmall hd hs
    (Nat.lt_of_lt_of_le x.positive hx) n (atBase x hx) (atBase y hy)
  have ht := distSq_at_base hw0 hw1 hsmall hd hs (time n x) (time n y) N hx hy
  simp only [atBase_time] at ht
  exact leEv_trans (leEv_of_equiv ht)
    (leEv_trans h (leEv_of_equiv (distSq_at_base hw0 hw1 hsmall hd hs x y N hx hy).symm))

def timeNonexpansive (n : Nat) : (D).Nonexpansive where
  toFun := time n
  contraction := time_contraction hw0 hw1 hsmall hd hs n

def timeSemigroup : (D).NonexpansiveSemigroup where
  op := timeNonexpansive hw0 hw1 hsmall hd hs
  zero_law := by
    intro x
    change Equiv (d (time 0 x) x) czero
    rw [time_zero]
    exact distance_refl hw0 hw1 hsmall hd hs x
  add_law := by
    intro m n x
    change Equiv (d (time (m+n) x) (time m (time n x))) czero
    rw [time_add]
    exact distance_refl hw0 hw1 hsmall hd hs _

/-- One quotient of arbitrary staged Cauchy streams, not a union of completions. -/
def UnionCompletion : Type := (D).Completion

def embedStage (x : Stage) : UnionCompletion hw0 hw1 hsmall hd hs := (D).embedRep x

def completedTime (n : Nat) : UnionCompletion hw0 hw1 hsmall hd hs → UnionCompletion hw0 hw1 hsmall hd hs :=
  (timeNonexpansive hw0 hw1 hsmall hd hs n).completionMap

theorem completedTime_zero (x : UnionCompletion hw0 hw1 hsmall hd hs) :
    completedTime hw0 hw1 hsmall hd hs 0 x = x :=
  (timeSemigroup hw0 hw1 hsmall hd hs).completionMap_zero x

theorem completedTime_add (m n : Nat) (x : UnionCompletion hw0 hw1 hsmall hd hs) :
    completedTime hw0 hw1 hsmall hd hs (m+n) x =
      completedTime hw0 hw1 hsmall hd hs m (completedTime hw0 hw1 hsmall hd hs n x) :=
  (timeSemigroup hw0 hw1 hsmall hd hs).completionMap_add m n x

theorem completedTime_embedStage (n : Nat) (x : Stage) :
    completedTime hw0 hw1 hsmall hd hs n (embedStage hw0 hw1 hsmall hd hs x) =
      embedStage hw0 hw1 hsmall hd hs (time n x) := rfl

theorem time_cauchy_modulus (n : Nat) (X : (D).Cauchy) :
    ((timeNonexpansive hw0 hw1 hsmall hd hs n).mapCauchy X).modulus = X.modulus := rfl

def completedUnit : UnionCompletion hw0 hw1 hsmall hd hs := embedStage hw0 hw1 hsmall hd hs unitStage

theorem completedUnit_fixed (n : Nat) :
    completedTime hw0 hw1 hsmall hd hs n (completedUnit hw0 hw1 hsmall hd hs) =
      completedUnit hw0 hw1 hsmall hd hs := by
  unfold completedUnit
  rw [completedTime_embedStage, time_unit]

end YMGap.Continuum.BF4SpatialUnionSeminorm

#print axioms YMGap.Continuum.BF4SpatialUnionSeminorm.distance_refl
#print axioms YMGap.Continuum.BF4SpatialUnionSeminorm.distance_symm
#print axioms YMGap.Continuum.BF4SpatialUnionSeminorm.distance_nonnegative
#print axioms YMGap.Continuum.BF4SpatialUnionSeminorm.distance_triangle
#print axioms YMGap.Continuum.BF4SpatialUnionSeminorm.distance_null_congr
#print axioms YMGap.Continuum.BF4SpatialUnionSeminorm.unionSeminorm
#print axioms YMGap.Continuum.BF4SpatialUnionSeminorm.time_contraction
#print axioms YMGap.Continuum.BF4SpatialUnionSeminorm.timeNonexpansive
#print axioms YMGap.Continuum.BF4SpatialUnionSeminorm.timeSemigroup
#print axioms YMGap.Continuum.BF4SpatialUnionSeminorm.UnionCompletion
#print axioms YMGap.Continuum.BF4SpatialUnionSeminorm.embedStage
#print axioms YMGap.Continuum.BF4SpatialUnionSeminorm.completedTime
#print axioms YMGap.Continuum.BF4SpatialUnionSeminorm.completedTime_zero
#print axioms YMGap.Continuum.BF4SpatialUnionSeminorm.completedTime_add
#print axioms YMGap.Continuum.BF4SpatialUnionSeminorm.completedTime_embedStage
#print axioms YMGap.Continuum.BF4SpatialUnionSeminorm.time_cauchy_modulus
#print axioms YMGap.Continuum.BF4SpatialUnionSeminorm.completedUnit
#print axioms YMGap.Continuum.BF4SpatialUnionSeminorm.completedUnit_fixed
