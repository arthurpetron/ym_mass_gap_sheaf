/-
Actual rational quaternion repair for the finite SAME-Haar Bernstein nodes.

Every raw cube node, including zero and corners, is repaired by the existing
total rational map. The weighted squared repair distance is bounded using the
already checked one-block joint norm-defect concentration. This is finite
polynomial-Haar data, not a continuous Haar measure or uniform sphere
approximation theorem.
-/

import YMGap.Continuum.QuaternionHaarTensorBernsteinConcentration
import YMGap.Continuum.BF4CompactCoupledActionBounds
import YMGap.RepTheory.RationalQuaternionNormRepair

namespace YMGap.Continuum.QuaternionHaarTensorBernsteinRepair

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.RationalTail
open YMGap.RepTheory
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactCoupledActionBounds
open YMGap.Continuum.QuaternionHaarTensorBernsteinCubature
open YMGap.Continuum.QuaternionHaarCubeNormDefect
open YMGap.Continuum.QuaternionHaarTensorBernsteinNormDefect
open YMGap.Continuum.QuaternionHaarTensorBernsteinConcentration
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionSphereNets
open YMGap.RepTheory.RationalQuaternionNormRepair

local infix:50 " ≈ " => Q'.eqv

/-- The literal raw rational quaternion at the four Bernstein grid indices. -/
def rawQuaternion (n k0 k1 k2 k3 : Nat) : RationalQuaternion :=
  ⟨rawCoordinate n k0, rawCoordinate n k1,
    rawCoordinate n k2, rawCoordinate n k3⟩

/-- The actual total rational norm repair, also defined at the zero node. -/
def repairedQuaternion (n k0 k1 k2 k3 : Nat) : UnitNorm :=
  repair (rawQuaternion n k0 k1 k2 k3)

/-- Coordinate order agrees exactly with the original scalar-first raw node. -/
theorem rawQuaternion_coordinate (n k0 k1 k2 k3 : Nat) (i : Fin 4) :
    coordinate (rawQuaternion n k0 k1 k2 k3) i =
      rawNode n k0 k1 k2 k3 i := by
  rcases i with ⟨j,hj⟩
  cases j with
  | zero => rfl
  | succ j => cases j with
    | zero => rfl
    | succ j => cases j with
      | zero => rfl
      | succ j => rfl

/-- Exact norm pin: no surrogate norm or normalized-node assumption. -/
theorem rawQuaternion_normSq (n k0 k1 k2 k3 : Nat) :
    normSq (rawQuaternion n k0 k1 k2 k3) ≈
      nodeNormScalar (rawNode n k0 k1 k2 k3) :=
  poly_identity_of_normal_eq
    (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
      (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3))))
    (.add (.mul (.var 0) (.var 0))
      (.add (.mul (.var 1) (.var 1))
        (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3)))))
    (by decide)
    (fun | 0 => rawCoordinate n k0 | 1 => rawCoordinate n k1
         | 2 => rawCoordinate n k2 | _ => rawCoordinate n k3)

/-- Extend four quaternion coordinates to a Nat-indexed polynomial environment;
all unused coordinates are exactly zero. -/
def environmentOf (q : RationalQuaternion) (index : Nat) : Q' :=
  if h : index < 4 then coordinate q ⟨index,h⟩ else 0

def rawEnvironment (n k0 k1 k2 k3 : Nat) : Nat → Q' :=
  environmentOf (rawQuaternion n k0 k1 k2 k3)

def repairedEnvironment (n k0 k1 k2 k3 : Nat) : Nat → Q' :=
  environmentOf (repairedQuaternion n k0 k1 k2 k3).val

theorem environmentOf_coordinate (q : RationalQuaternion) (i : Fin 4) :
    environmentOf q i.val = coordinate q i := by
  simp only [environmentOf, i.isLt, dite_true]

/-- The raw environment is the same `rawNode`, component by component. -/
theorem rawEnvironment_coordinate (n k0 k1 k2 k3 : Nat) (i : Fin 4) :
    rawEnvironment n k0 k1 k2 k3 i.val =
      rawNode n k0 k1 k2 k3 i := by
  exact (environmentOf_coordinate (rawQuaternion n k0 k1 k2 k3) i).trans
    (rawQuaternion_coordinate n k0 k1 k2 k3 i)

/-- The repaired environment uses the actual repaired unit quaternion. -/
theorem repairedEnvironment_coordinate (n k0 k1 k2 k3 : Nat) (i : Fin 4) :
    repairedEnvironment n k0 k1 k2 k3 i.val =
      coordinate (repairedQuaternion n k0 k1 k2 k3).val i :=
  environmentOf_coordinate _ i

private theorem abs_square (a : Q') : Q'.abs a * Q'.abs a ≈ a*a := by
  unfold Q'.abs
  split
  · exact Q'.eqv_refl _
  · exact poly_identity_of_normal_eq
      (.mul (.neg (.var 0)) (.neg (.var 0)))
      (.mul (.var 0) (.var 0)) (by decide) (fun _ => a)

private theorem abs_le_one_of_square_le {a : Q'}
    (h : a*a ≤ (1 : Q')) : Q'.abs a ≤ 1 :=
  CReal.le_of_sq_le_sq (by decide : (0 : Q') < 1) (Q'.abs_nonneg a)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (abs_square a))
      (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (by decide :
        Q'.eqv (1 : Q') (1*1)))))

private theorem environmentOf_cube (q : RationalQuaternion)
    (hq : ∀ i : Fin 4, Q'.abs (coordinate q i) ≤ (1 : Q')) :
    CompactCubeEnvironment (environmentOf q) := by
  intro index
  by_cases h : index < 4
  · simpa only [environmentOf, h, dite_true] using hq ⟨index,h⟩
  · simpa only [environmentOf, h, dite_false] using
      (by decide : Q'.abs (0 : Q') ≤ (1 : Q'))

/-- Actual raw Bernstein nodes lie in the compact coordinate cube. -/
theorem rawEnvironment_cube (n k0 k1 k2 k3 : Nat)
    (h0 : k0 ≤ n+1) (h1 : k1 ≤ n+1)
    (h2 : k2 ≤ n+1) (h3 : k3 ≤ n+1) :
    CompactCubeEnvironment (rawEnvironment n k0 k1 k2 k3) := by
  apply environmentOf_cube
  intro i
  have hs := rawNode_square_le_one n k0 k1 k2 k3 h0 h1 h2 h3 i
  rw [← rawQuaternion_coordinate n k0 k1 k2 k3 i] at hs
  exact abs_le_one_of_square_le hs

/-- Every repaired rational quaternion is unit norm, so all repaired nodes
lie in the same compact coordinate cube without a grid guard. -/
theorem repairedEnvironment_cube (n k0 k1 k2 k3 : Nat) :
    CompactCubeEnvironment (repairedEnvironment n k0 k1 k2 k3) := by
  apply environmentOf_cube
  intro i
  let q := repairedQuaternion n k0 k1 k2 k3
  have hs : coordinate q.val i * coordinate q.val i ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ (coordinate_square_le q.val i) (Q'.le_of_eqv q.unitNorm)
  exact abs_le_one_of_square_le hs

/-- Literal fourfold finite sum, shared by the actual repair-distance and
downstream finite polynomial approximation budgets. -/
def sum4 (f : Nat → Nat → Nat → Nat → Q') (count : Nat) : Q' :=
  finSum (fun k0 => finSum (fun k1 => finSum (fun k2 =>
    finSum (fun k3 => f k0 k1 k2 k3) count) count) count) count

theorem sum4_congr (f g : Nat → Nat → Nat → Nat → Q')
    (h : ∀ k0 k1 k2 k3, f k0 k1 k2 k3 ≈ g k0 k1 k2 k3)
    (count : Nat) : sum4 f count ≈ sum4 g count := by
  unfold sum4
  exact finSum_eqv_congr _ _ (fun k0 =>
    finSum_eqv_congr _ _ (fun k1 =>
      finSum_eqv_congr _ _ (fun k2 =>
        finSum_eqv_congr _ _ (h k0 k1 k2) count) count) count) count

theorem sum4_add (f g : Nat → Nat → Nat → Nat → Q') (count : Nat) :
    sum4 (fun k0 k1 k2 k3 => f k0 k1 k2 k3 + g k0 k1 k2 k3) count ≈
      sum4 f count + sum4 g count := by
  unfold sum4
  exact Q'.eqv_trans _ _ _
    (finSum_eqv_congr _ _ (fun k0 =>
      Q'.eqv_trans _ _ _
        (finSum_eqv_congr _ _ (fun k1 =>
          Q'.eqv_trans _ _ _
            (finSum_eqv_congr _ _ (fun k2 => finSum_add _ _ count) count)
            (finSum_add _ _ count)) count)
        (finSum_add _ _ count)) count)
    (finSum_add _ _ count)

theorem sum4_const_mul (c : Q')
    (f : Nat → Nat → Nat → Nat → Q') (count : Nat) :
    c * sum4 f count ≈
      sum4 (fun k0 k1 k2 k3 => c * f k0 k1 k2 k3) count := by
  unfold sum4
  exact Q'.eqv_trans _ _ _ (const_mul_finSum _ c count)
    (finSum_eqv_congr _ _ (fun k0 =>
      Q'.eqv_trans _ _ _ (const_mul_finSum _ c count)
        (finSum_eqv_congr _ _ (fun k1 =>
          Q'.eqv_trans _ _ _ (const_mul_finSum _ c count)
            (finSum_eqv_congr _ _ (fun k2 =>
              const_mul_finSum _ c count) count)) count)) count)

private theorem finSum_le_lt (f g : Nat → Q') :
    ∀ count, (∀ k, k < count → f k ≤ g k) →
      finSum f count ≤ finSum g count
  | 0, _ => Q'.le_refl' 0
  | count+1, h =>
      Q'.add_le_add
        (finSum_le_lt f g count (fun k hk => h k (by omega)))
        (h count (by omega))

theorem sum4_le_lt (f g : Nat → Nat → Nat → Nat → Q')
    (count : Nat)
    (h : ∀ k0 k1 k2 k3, k0<count → k1<count → k2<count → k3<count →
      f k0 k1 k2 k3 ≤ g k0 k1 k2 k3) :
    sum4 f count ≤ sum4 g count := by
  unfold sum4
  apply finSum_le_lt
  intro k0 hk0
  apply finSum_le_lt
  intro k1 hk1
  apply finSum_le_lt
  intro k2 hk2
  apply finSum_le_lt
  intro k3 hk3
  exact h k0 k1 k2 k3 hk0 hk1 hk2 hk3

/-- Literal actual-joint-weight squared distance of the repaired node from
the raw node; no normalization or omitted zero-node case. -/
def jointRepairDistance (n : Nat) : Q' :=
  sum4 (fun k0 k1 k2 k3 =>
    jointWeightRaw n k0 k1 k2 k3 *
      distSq (repairedQuaternion n k0 k1 k2 k3).val
        (rawQuaternion n k0 k1 k2 k3)) (n+2)

private theorem mul_congr {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a*b ≈ a'*b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem repair_term_le (n k0 k1 k2 k3 : Nat) :
    jointWeightRaw n k0 k1 k2 k3 *
      distSq (repairedQuaternion n k0 k1 k2 k3).val
        (rawQuaternion n k0 k1 k2 k3) ≤
    jointWeightRaw n k0 k1 k2 k3 *
      ((nodeNormScalar (rawNode n k0 k1 k2 k3) + -1) *
        (nodeNormScalar (rawNode n k0 k1 k2 k3) + -1)) := by
  let q := rawQuaternion n k0 k1 k2 k3
  have he : (normSq q + -1) * (normSq q + -1) ≈
      (nodeNormScalar (rawNode n k0 k1 k2 k3) + -1) *
        (nodeNormScalar (rawNode n k0 k1 k2 k3) + -1) := by
    have hd : normSq q + -1 ≈
        nodeNormScalar (rawNode n k0 k1 k2 k3) + -1 :=
      Q'.add_eqv_congr' (rawQuaternion_normSq n k0 k1 k2 k3)
        (Q'.eqv_refl (-1))
    exact mul_congr hd hd
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (repair_error_le q)
      (jointWeightRaw_nonnegative n k0 k1 k2 k3))
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ he))

/-- Quantitative actual finite repair cost, for all degrees including `n=0`.
The repaired node is the genuine rational unit quaternion from `repair`. -/
theorem jointRepairDistance_le (n : Nat) :
    jointRepairDistance n ≤ 48 * Q'.invSucc n := by
  have hsum : jointRepairDistance n ≤ jointNormDefect n := by
    change sum4 (fun k0 k1 k2 k3 =>
      jointWeightRaw n k0 k1 k2 k3 *
        distSq (repairedQuaternion n k0 k1 k2 k3).val
          (rawQuaternion n k0 k1 k2 k3)) (n+2) ≤
      sum4 (fun k0 k1 k2 k3 =>
        jointWeightRaw n k0 k1 k2 k3 *
          ((nodeNormScalar (rawNode n k0 k1 k2 k3) + -1) *
            (nodeNormScalar (rawNode n k0 k1 k2 k3) + -1))) (n+2)
    exact sum4_le_lt _ _ (n+2) (fun k0 k1 k2 k3 _ _ _ _ =>
      repair_term_le n k0 k1 k2 k3)
  exact Q'.le_trans' _ _ _ hsum (jointNormDefect_le n)

end YMGap.Continuum.QuaternionHaarTensorBernsteinRepair

#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinRepair.rawQuaternion
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinRepair.repairedQuaternion
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinRepair.rawQuaternion_coordinate
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinRepair.rawQuaternion_normSq
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinRepair.environmentOf
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinRepair.rawEnvironment
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinRepair.repairedEnvironment
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinRepair.environmentOf_coordinate
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinRepair.rawEnvironment_coordinate
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinRepair.repairedEnvironment_coordinate
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinRepair.rawEnvironment_cube
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinRepair.repairedEnvironment_cube
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinRepair.sum4
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinRepair.sum4_congr
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinRepair.sum4_add
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinRepair.sum4_const_mul
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinRepair.sum4_le_lt
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinRepair.jointRepairDistance
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinRepair.jointRepairDistance_le
