/-
# Retaining an explicit channel in a reflected-square sum

A leaf is Type-level path data in the ACTUAL square tree. Its weight and
polynomial are computable projections. Scaling and products transport the
path, retaining shared variables. For nonnegative tree weights, that one
weighted Haar square is a lower bound for the full square sum.

A unit leaf additionally pins its weight to one and its polynomial to one
coefficientwise. Multiplying the tree by an arbitrary observable square then
retains that observable's own Haar square. No strict positivity is inferred.
-/

import YMGap.Continuum.BF4ExactSlabLocalSquareExpansion

namespace YMGap.Continuum.ReflectedSquareTreeRetainedChannel

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.BF4ExactSlabAllCutoffReflectionPositivity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

local infix:50 " ≈ " => Q'.eqv

private theorem mul_congr {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha) (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem haar_eq_weighted (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks p = ratWeightedSum (quaternionHaarMono blocks) p
  | [] => rfl
  | _ :: rest => by unfold quaternionHaar ratWeightedSum; rw [haar_eq_weighted blocks rest]

private theorem haar_coeff (blocks : Nat) {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    quaternionHaar blocks p ≈ quaternionHaar blocks q := by
  rw [haar_eq_weighted, haar_eq_weighted]
  exact h _

inductive Leaf : SquareTree → Type where
  | here (w : Q') (p : RatPoly) : Leaf (.term w p)
  | left {s t : SquareTree} : Leaf s → Leaf (.add s t)
  | right {s t : SquareTree} : Leaf t → Leaf (.add s t)

namespace Leaf

def weight : {t : SquareTree} → Leaf t → Q'
  | _, .here w _ => w
  | _, .left l => l.weight
  | _, .right l => l.weight

def channel : {t : SquareTree} → Leaf t → RatPoly
  | _, .here _ p => p
  | _, .left l => l.channel
  | _, .right l => l.channel

def scale (a : Q') : {t : SquareTree} → Leaf t → Leaf (t.scale a)
  | _, .here w p => .here (a * w) p
  | _, .left l => .left (l.scale a)
  | _, .right l => .right (l.scale a)

theorem scale_weight (a : Q') : {t : SquareTree} → (l : Leaf t) → (l.scale a).weight = a * l.weight
  | _, .here _ _ => rfl
  | _, .left l => scale_weight a l
  | _, .right l => scale_weight a l

theorem scale_channel (a : Q') : {t : SquareTree} → (l : Leaf t) → (l.scale a).channel = l.channel
  | _, .here _ _ => rfl
  | _, .left l => scale_channel a l
  | _, .right l => scale_channel a l

def multiplyTerm (a : Q') (p : RatPoly) : {t : SquareTree} → Leaf t → Leaf (t.multiplyTerm a p)
  | _, .here w q => .here (a * w) (polyMul p q)
  | _, .left l => .left (l.multiplyTerm a p)
  | _, .right l => .right (l.multiplyTerm a p)

theorem multiplyTerm_weight (a : Q') (p : RatPoly) : {t : SquareTree} → (l : Leaf t) →
    (l.multiplyTerm a p).weight = a * l.weight
  | _, .here _ _ => rfl
  | _, .left l => multiplyTerm_weight a p l
  | _, .right l => multiplyTerm_weight a p l

theorem multiplyTerm_channel (a : Q') (p : RatPoly) : {t : SquareTree} → (l : Leaf t) →
    (l.multiplyTerm a p).channel = polyMul p l.channel
  | _, .here _ _ => rfl
  | _, .left l => multiplyTerm_channel a p l
  | _, .right l => multiplyTerm_channel a p l

def product : {s t : SquareTree} → Leaf s → Leaf t → Leaf (s.product t)
  | _, _, .here a p, r => r.multiplyTerm a p
  | _, _, .left l, r => .left (l.product r)
  | _, _, .right l, r => .right (l.product r)

theorem product_weight : {s t : SquareTree} → (l : Leaf s) → (r : Leaf t) →
    (l.product r).weight = l.weight * r.weight
  | _, _, .here a p, r => r.multiplyTerm_weight a p
  | _, _, .left l, r => product_weight l r
  | _, _, .right l, r => product_weight l r

theorem product_channel : {s t : SquareTree} → (l : Leaf s) → (r : Leaf t) →
    (l.product r).channel = polyMul l.channel r.channel
  | _, _, .here a p, r => r.multiplyTerm_channel a p
  | _, _, .left l, r => product_channel l r
  | _, _, .right l, r => product_channel l r

theorem value_le (blocks : Nat) : {t : SquareTree} → (l : Leaf t) → t.Nonnegative →
    l.weight * (quaternionHaar blocks l.channel * quaternionHaar blocks l.channel) ≤ haarSquareSum blocks t
  | _, .here _ _, _ => Q'.le_refl' _
  | .add _ t, .left l, h => Q'.le_trans' _ _ _ (value_le blocks l h.1)
      (Q'.add_le_self_of_nonneg _ _ (haarSquareSum_nonnegative blocks t h.2))
  | .add s _, .right l, h => Q'.le_trans' _ _ _ (value_le blocks l h.2)
      (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ (haarSquareSum_nonnegative blocks s h.1))
        (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

end Leaf

structure UnitLeaf (t : SquareTree) where
  leaf : Leaf t
  weight_one : leaf.weight ≈ 1
  channel_one : RatPolyCoeffEqv leaf.channel polyOne

namespace UnitLeaf

def one : UnitLeaf (.term 1 polyOne) := ⟨.here 1 polyOne, Q'.eqv_refl _, .refl _⟩

def left {s t : SquareTree} (l : UnitLeaf s) : UnitLeaf (.add s t) :=
  ⟨.left l.leaf, l.weight_one, l.channel_one⟩

def right {s t : SquareTree} (l : UnitLeaf t) : UnitLeaf (.add s t) :=
  ⟨.right l.leaf, l.weight_one, l.channel_one⟩

def scale {t : SquareTree} (a : Q') (ha : a ≈ 1) (l : UnitLeaf t) : UnitLeaf (t.scale a) where
  leaf := l.leaf.scale a
  weight_one := by
    rw [Leaf.scale_weight]
    exact Q'.eqv_trans _ _ _ (mul_congr ha l.weight_one) (Q'.one_mul_eqv 1)
  channel_one := by rw [Leaf.scale_channel]; exact l.channel_one

def product {s t : SquareTree} (l : UnitLeaf s) (r : UnitLeaf t) : UnitLeaf (s.product t) where
  leaf := l.leaf.product r.leaf
  weight_one := by
    rw [Leaf.product_weight]
    exact Q'.eqv_trans _ _ _ (mul_congr l.weight_one r.weight_one) (Q'.one_mul_eqv 1)
  channel_one := by
    rw [Leaf.product_channel]
    exact (l.channel_one.mul r.channel_one).trans (RatPolyCoeffEqv.mul_one polyOne)

theorem observable_square_le {t : SquareTree} (l : UnitLeaf t) (ht : t.Nonnegative)
    (blocks : Nat) (p : RatPoly) :
    quaternionHaar blocks p * quaternionHaar blocks p ≤
      haarSquareSum blocks (t.multiplyTerm 1 p) := by
  have h := (l.leaf.multiplyTerm 1 p).value_le blocks
    (SquareTree.multiplyTerm_nonnegative 1 p Q'.zero_le_one t ht)
  rw [Leaf.multiplyTerm_weight, Leaf.multiplyTerm_channel] at h
  have hc : (quaternionHaar blocks (polyMul p l.leaf.channel)).eqv (quaternionHaar blocks p) :=
    haar_coeff blocks ((l.channel_one.mul_left p).trans (RatPolyCoeffEqv.mul_one p))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.eqv_trans _ _ _
    (mul_congr (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) l.weight_one)
      (mul_congr hc hc)) (Q'.one_mul_eqv _))) h

end UnitLeaf

end YMGap.Continuum.ReflectedSquareTreeRetainedChannel

#print axioms YMGap.Continuum.ReflectedSquareTreeRetainedChannel.Leaf
#print axioms YMGap.Continuum.ReflectedSquareTreeRetainedChannel.Leaf.weight
#print axioms YMGap.Continuum.ReflectedSquareTreeRetainedChannel.Leaf.channel
#print axioms YMGap.Continuum.ReflectedSquareTreeRetainedChannel.Leaf.scale
#print axioms YMGap.Continuum.ReflectedSquareTreeRetainedChannel.Leaf.scale_weight
#print axioms YMGap.Continuum.ReflectedSquareTreeRetainedChannel.Leaf.scale_channel
#print axioms YMGap.Continuum.ReflectedSquareTreeRetainedChannel.Leaf.multiplyTerm
#print axioms YMGap.Continuum.ReflectedSquareTreeRetainedChannel.Leaf.multiplyTerm_weight
#print axioms YMGap.Continuum.ReflectedSquareTreeRetainedChannel.Leaf.multiplyTerm_channel
#print axioms YMGap.Continuum.ReflectedSquareTreeRetainedChannel.Leaf.product
#print axioms YMGap.Continuum.ReflectedSquareTreeRetainedChannel.Leaf.product_weight
#print axioms YMGap.Continuum.ReflectedSquareTreeRetainedChannel.Leaf.product_channel
#print axioms YMGap.Continuum.ReflectedSquareTreeRetainedChannel.Leaf.value_le
#print axioms YMGap.Continuum.ReflectedSquareTreeRetainedChannel.UnitLeaf
#print axioms YMGap.Continuum.ReflectedSquareTreeRetainedChannel.UnitLeaf.one
#print axioms YMGap.Continuum.ReflectedSquareTreeRetainedChannel.UnitLeaf.left
#print axioms YMGap.Continuum.ReflectedSquareTreeRetainedChannel.UnitLeaf.right
#print axioms YMGap.Continuum.ReflectedSquareTreeRetainedChannel.UnitLeaf.scale
#print axioms YMGap.Continuum.ReflectedSquareTreeRetainedChannel.UnitLeaf.product
#print axioms YMGap.Continuum.ReflectedSquareTreeRetainedChannel.UnitLeaf.observable_square_le
