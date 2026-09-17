/-
# Squared seminorm and original physical time on the spatial Wilson union

The actual coherent limiting distance is compared at one computed finite
common base for every finite collection of inputs. Null replacement is a
statement about that limiting reflected form, never about a finite regulator.
The existing Cauchy quotient then permits supplied streams whose spatial
bases and time radii grow without bound. Physical advance acts termwise and
retains each supplied modulus exactly.

The unit is fixed only after its actual zero limiting distance is proved;
time advance does not preserve the radius-tagged unit as literal syntax.
This is one spatial-union carrier and its nonexpansive time semigroup, not
full Hilbert completeness, full gauge-observable coverage, a continuum
Hamiltonian or a changing-spacing/all-group Yang--Mills theorem.
-/

import YMGap.Continuum.BF4WilsonSpatialUnion
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeContraction

namespace YMGap.Continuum.BF4WilsonSpatialUnionSeminorm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.BF4WilsonSpatialUnion
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm
  (distSq_refl distSq_symm distSq_nonnegative distSq_triangle distSq_null_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeForm (advance_unit_null)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeContraction
  (distSq_advance_contraction)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "d" => distSq hw0 hw1 hsmall hd hs

attribute [local irreducible] distSq BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.distSq

theorem distance_refl (x : Stage) : Equiv (d x x) czero := by
  have h := distSq_at_base hw0 hw1 hsmall hd hs x x x.base (Nat.le_refl _) (Nat.le_refl _)
  simp only [atBase_self] at h
  exact h.trans (distSq_refl hw0 hw1 hsmall hd hs x.positive x.value)

theorem distance_symm (x y : Stage) : Equiv (d x y) (d y x) := by
  let N := max x.base y.base
  have hx : x.base ≤ N := Nat.le_max_left _ _
  have hy : y.base ≤ N := Nat.le_max_right _ _
  exact (distSq_at_base hw0 hw1 hsmall hd hs x y N hx hy).trans
    ((distSq_symm hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le x.positive hx)
      (atBase x hx) (atBase y hy)).trans
      (distSq_at_base hw0 hw1 hsmall hd hs y x N hy hx).symm)

theorem distance_nonnegative (x y : Stage) : leEv czero (d x y) := by
  let N := max x.base y.base
  have hx : x.base ≤ N := Nat.le_max_left _ _
  have hy : y.base ≤ N := Nat.le_max_right _ _
  exact leEv_trans (distSq_nonnegative hw0 hw1 hsmall hd hs
      (Nat.lt_of_lt_of_le x.positive hx) (atBase x hx) (atBase y hy))
    (leEv_of_equiv (distSq_at_base hw0 hw1 hsmall hd hs x y N hx hy).symm)

theorem distance_triangle (x y z : Stage) :
    leEv (d x z) (add (add (d x y) (d x y)) (add (d y z) (d y z))) := by
  let N := max x.base (max y.base z.base)
  have hx : x.base ≤ N := by omega
  have hy : y.base ≤ N := by omega
  have hz : z.base ≤ N := by omega
  have hxy := distSq_at_base hw0 hw1 hsmall hd hs x y N hx hy
  have hyz := distSq_at_base hw0 hw1 hsmall hd hs y z N hy hz
  exact leEv_trans (leEv_of_equiv (distSq_at_base hw0 hw1 hsmall hd hs x z N hx hz))
    (leEv_trans (distSq_triangle hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le x.positive hx)
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
    ((distSq_null_congr hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le x.positive hxN)
      hx0 hy0).trans (distSq_at_base hw0 hw1 hsmall hd hs x' y' N hxN' hyN').symm)

/-- Every field concerns the original coherent limiting Wilson distance. -/
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
  have h := distSq_advance_contraction hw0 hw1 hsmall hd hs
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

/-- One quotient of staged Cauchy streams, not a union of fixed-base completions. -/
def UnionCompletion : Type := (D).Completion

def embedStage (x : Stage) : UnionCompletion hw0 hw1 hsmall hd hs := (D).embedRep x

def completedTime (n : Nat) :
    UnionCompletion hw0 hw1 hsmall hd hs → UnionCompletion hw0 hw1 hsmall hd hs :=
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

theorem time_cauchy_seq (n : Nat) (X : (D).Cauchy) (k : Nat) :
    ((timeNonexpansive hw0 hw1 hsmall hd hs n).mapCauchy X).seq k = time n (X.seq k) := rfl

theorem time_cauchy_modulus (n : Nat) (X : (D).Cauchy) :
    ((timeNonexpansive hw0 hw1 hsmall hd hs n).mapCauchy X).modulus = X.modulus := rfl

def completedUnit : UnionCompletion hw0 hw1 hsmall hd hs :=
  embedStage hw0 hw1 hsmall hd hs unitStage

/-- Time changes the raw unit radius, but its SAME limiting distance is zero. -/
theorem time_unit_null (n : Nat) : (D).Null (time n unitStage) unitStage := by
  change Equiv (d (time n unitStage) unitStage) czero
  have h := distSq_ofExpression hw0 hw1 hsmall hd hs 1 (by decide : 0<1)
    (advance n (unit 1)) (unit 1)
  exact h.trans (advance_unit_null hw0 hw1 hsmall hd hs (by decide : 0<1) n)

theorem completedUnit_fixed (n : Nat) :
    completedTime hw0 hw1 hsmall hd hs n (completedUnit hw0 hw1 hsmall hd hs) =
      completedUnit hw0 hw1 hsmall hd hs := by
  unfold completedUnit
  rw [completedTime_embedStage]
  exact (D).embedRep_eq_of_null (time_unit_null hw0 hw1 hsmall hd hs n)

end YMGap.Continuum.BF4WilsonSpatialUnionSeminorm

#print axioms YMGap.Continuum.BF4WilsonSpatialUnionSeminorm.distance_refl
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionSeminorm.distance_symm
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionSeminorm.distance_nonnegative
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionSeminorm.distance_triangle
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionSeminorm.distance_null_congr
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionSeminorm.unionSeminorm
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionSeminorm.time_contraction
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionSeminorm.timeNonexpansive
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionSeminorm.timeSemigroup
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionSeminorm.UnionCompletion
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionSeminorm.embedStage
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionSeminorm.completedTime
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionSeminorm.completedTime_zero
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionSeminorm.completedTime_add
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionSeminorm.completedTime_embedStage
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionSeminorm.time_cauchy_seq
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionSeminorm.time_cauchy_modulus
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionSeminorm.completedUnit
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionSeminorm.time_unit_null
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionSeminorm.completedUnit_fixed
