/-
# Two distinct retained channels and a centering-invariant minor

Paths select two different leaves of the ACTUAL reflected-square tree.
Their weighted squares are bounded by its full Haar square sum, with no
double counting. The weighted Lagrange identity then bounds a two-channel
minor by the full centered energy times the retained reference energy.
The minor is unchanged by subtracting ANY rational reference multiple.

This is an exact finite inequality, not a positive-minor witness, a uniform
cutoff estimate, or an assertion of a nonzero physical excitation.
-/

import YMGap.Continuum.ReflectedSquareTreeRetainedChannel
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.ReflectedSquareTreeTwoChannelBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.BF4ExactSlabAllCutoffReflectionPositivity
open YMGap.Continuum.ReflectedSquareTreeRetainedChannel
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

local infix:50 " ≈ " => Q'.eqv

private theorem mul_congr {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha) (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem add_mono {a b c d : Q'} (h : a ≤ b) (k : c ≤ d) : a + c ≤ b + d :=
  Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ h) (Q'.add_le_add_left _ _ _ k)

def energy (w0 w1 a0 a1 : Q') : Q' := w0 * (a0 * a0) + w1 * (a1 * a1)

def determinant (a0 a1 b0 b1 : Q') : Q' := a0 * b1 + -(a1 * b0)

def minor (w0 w1 a0 a1 b0 b1 : Q') : Q' :=
  (w0 * w1) * (determinant a0 a1 b0 b1 * determinant a0 a1 b0 b1)

private def detSyntax (a0 a1 b0 b1 : PolyExpr) : PolyExpr :=
  .add (.mul a0 b1) (.neg (.mul a1 b0))

private def energySyntax (a0 a1 : PolyExpr) : PolyExpr :=
  .add (.mul (.var 0) (.mul a0 a0)) (.mul (.var 1) (.mul a1 a1))

private def lagrangeLeft : PolyExpr :=
  let d := detSyntax (.var 2) (.var 3) (.var 4) (.var 5)
  let s := .add (.mul (.mul (.var 0) (.var 2)) (.var 4))
    (.mul (.mul (.var 1) (.var 3)) (.var 5))
  .add (.mul (.mul (.var 0) (.var 1)) (.mul d d)) (.mul s s)

private def lagrangeRight : PolyExpr :=
  .mul (energySyntax (.var 2) (.var 3)) (energySyntax (.var 4) (.var 5))

theorem weighted_lagrange (w0 w1 a0 a1 b0 b1 : Q') :
    minor w0 w1 a0 a1 b0 b1 +
      ((w0 * a0 * b0 + w1 * a1 * b1) * (w0 * a0 * b0 + w1 * a1 * b1)) ≈
    energy w0 w1 a0 a1 * energy w0 w1 b0 b1 :=
  poly_identity_of_normal_eq lagrangeLeft lagrangeRight (by decide)
    (fun n => match n with | 0 => w0 | 1 => w1 | 2 => a0 | 3 => a1 | 4 => b0 | _ => b1)

theorem determinant_shift (a0 a1 b0 b1 c : Q') :
    determinant (a0 + (-c) * b0) (a1 + (-c) * b1) b0 b1 ≈ determinant a0 a1 b0 b1 :=
  poly_identity_of_normal_eq
    (detSyntax (.add (.var 0) (.mul (.neg (.var 4)) (.var 2)))
      (.add (.var 1) (.mul (.neg (.var 4)) (.var 3))) (.var 2) (.var 3))
    (detSyntax (.var 0) (.var 1) (.var 2) (.var 3)) (by decide)
    (fun n => match n with | 0 => a0 | 1 => a1 | 2 => b0 | 3 => b1 | _ => c)

theorem minor_shift (w0 w1 a0 a1 b0 b1 c : Q') :
    minor w0 w1 (a0 + (-c) * b0) (a1 + (-c) * b1) b0 b1 ≈ minor w0 w1 a0 a1 b0 b1 :=
  Q'.mul_eqv_congr_left _ _ _ (mul_congr (determinant_shift a0 a1 b0 b1 c)
    (determinant_shift a0 a1 b0 b1 c))

theorem energy_nonnegative {w0 w1 : Q'} (h0 : (0 : Q') ≤ w0) (h1 : (0 : Q') ≤ w1)
    (a0 a1 : Q') : (0 : Q') ≤ energy w0 w1 a0 a1 :=
  Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ h0 (SumOfSquares.q_mul_self_nonneg _))
    (Q'.mul_nonneg _ _ h1 (SumOfSquares.q_mul_self_nonneg _))

theorem minor_nonnegative {w0 w1 : Q'} (h0 : (0 : Q') ≤ w0) (h1 : (0 : Q') ≤ w1)
    (a0 a1 b0 b1 : Q') : (0 : Q') ≤ minor w0 w1 a0 a1 b0 b1 :=
  Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ h0 h1) (SumOfSquares.q_mul_self_nonneg _)

theorem minor_le_energy_product (w0 w1 a0 a1 b0 b1 : Q') :
    minor w0 w1 a0 a1 b0 b1 ≤ energy w0 w1 a0 a1 * energy w0 w1 b0 b1 :=
  Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ (SumOfSquares.q_mul_self_nonneg _))
    (Q'.le_of_eqv (weighted_lagrange w0 w1 a0 a1 b0 b1))

/-- The first split separating the paths is retained as data. A leaf cannot
be counted twice, even when two distinct leaves have equal polynomials. -/
inductive Pair : SquareTree → Type where
  | across {s t : SquareTree} : Leaf s → Leaf t → Pair (.add s t)
  | left {s t : SquareTree} : Pair s → Pair (.add s t)
  | right {s t : SquareTree} : Pair t → Pair (.add s t)

namespace Pair

def first : {t : SquareTree} → Pair t → Leaf t
  | _, .across l _ => .left l
  | _, .left p => .left p.first
  | _, .right p => .right p.first

def second : {t : SquareTree} → Pair t → Leaf t
  | _, .across _ r => .right r
  | _, .left p => .left p.second
  | _, .right p => .right p.second

def multiplyTerm (a : Q') (q : RatPoly) : {t : SquareTree} → Pair t → Pair (t.multiplyTerm a q)
  | _, .across l r => .across (l.multiplyTerm a q) (r.multiplyTerm a q)
  | _, .left p => .left (p.multiplyTerm a q)
  | _, .right p => .right (p.multiplyTerm a q)

theorem multiplyTerm_first (a : Q') (q : RatPoly) : {t : SquareTree} → (p : Pair t) →
    (p.multiplyTerm a q).first = p.first.multiplyTerm a q
  | _, .across _ _ => rfl
  | _, .left p => congrArg Leaf.left (multiplyTerm_first a q p)
  | _, .right p => congrArg Leaf.right (multiplyTerm_first a q p)

theorem multiplyTerm_second (a : Q') (q : RatPoly) : {t : SquareTree} → (p : Pair t) →
    (p.multiplyTerm a q).second = p.second.multiplyTerm a q
  | _, .across _ _ => rfl
  | _, .left p => congrArg Leaf.left (multiplyTerm_second a q p)
  | _, .right p => congrArg Leaf.right (multiplyTerm_second a q p)

theorem weight_nonnegative : {t : SquareTree} → (l : Leaf t) → t.Nonnegative → (0 : Q') ≤ l.weight
  | _, .here _ _, h => h
  | _, .left l, h => weight_nonnegative l h.1
  | _, .right l, h => weight_nonnegative l h.2

theorem value_le (blocks : Nat) : {t : SquareTree} → (p : Pair t) → t.Nonnegative →
    energy p.first.weight p.second.weight
      (quaternionHaar blocks p.first.channel) (quaternionHaar blocks p.second.channel) ≤ haarSquareSum blocks t
  | _, .across l r, h => add_mono (l.value_le blocks h.1) (r.value_le blocks h.2)
  | .add _ t, .left p, h => Q'.le_trans' _ _ _ (value_le blocks p h.1)
      (Q'.add_le_self_of_nonneg _ _ (haarSquareSum_nonnegative blocks t h.2))
  | .add s _, .right p, h => Q'.le_trans' _ _ _ (value_le blocks p h.2)
      (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ (haarSquareSum_nonnegative blocks s h.1))
        (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

/-- Actual channel amplitude against a polynomial; shared variables remain. -/
def amplitude (blocks : Nat) {t : SquareTree} (l : Leaf t) (q : RatPoly) : Q' :=
  quaternionHaar blocks (polyMul q l.channel)

theorem observable_energy_le (blocks : Nat) {t : SquareTree} (p : Pair t) (ht : t.Nonnegative)
    (q : RatPoly) : energy p.first.weight p.second.weight
      (amplitude blocks p.first q) (amplitude blocks p.second q) ≤ haarSquareSum blocks (t.multiplyTerm 1 q) := by
  have h := (p.multiplyTerm 1 q).value_le blocks
    (SquareTree.multiplyTerm_nonnegative 1 q Q'.zero_le_one t ht)
  rw [multiplyTerm_first, multiplyTerm_second, Leaf.multiplyTerm_weight, Leaf.multiplyTerm_weight,
    Leaf.multiplyTerm_channel, Leaf.multiplyTerm_channel] at h
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv _))
    (Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv _)))) h

theorem minor_le_full_energy (blocks : Nat) {t : SquareTree} (p : Pair t) (ht : t.Nonnegative)
    (q r : RatPoly) :
    minor p.first.weight p.second.weight (amplitude blocks p.first q) (amplitude blocks p.second q)
      (amplitude blocks p.first r) (amplitude blocks p.second r) ≤
    haarSquareSum blocks (t.multiplyTerm 1 q) *
      energy p.first.weight p.second.weight (amplitude blocks p.first r) (amplitude blocks p.second r) :=
  Q'.le_trans' _ _ _ (minor_le_energy_product _ _ _ _ _ _)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (p.observable_energy_le blocks ht q)
      (energy_nonnegative (weight_nonnegative p.first ht) (weight_nonnegative p.second ht) _ _))

end Pair

end YMGap.Continuum.ReflectedSquareTreeTwoChannelBound

#print axioms YMGap.Continuum.ReflectedSquareTreeTwoChannelBound.energy
#print axioms YMGap.Continuum.ReflectedSquareTreeTwoChannelBound.determinant
#print axioms YMGap.Continuum.ReflectedSquareTreeTwoChannelBound.minor
#print axioms YMGap.Continuum.ReflectedSquareTreeTwoChannelBound.weighted_lagrange
#print axioms YMGap.Continuum.ReflectedSquareTreeTwoChannelBound.determinant_shift
#print axioms YMGap.Continuum.ReflectedSquareTreeTwoChannelBound.minor_shift
#print axioms YMGap.Continuum.ReflectedSquareTreeTwoChannelBound.energy_nonnegative
#print axioms YMGap.Continuum.ReflectedSquareTreeTwoChannelBound.minor_nonnegative
#print axioms YMGap.Continuum.ReflectedSquareTreeTwoChannelBound.minor_le_energy_product
#print axioms YMGap.Continuum.ReflectedSquareTreeTwoChannelBound.Pair
#print axioms YMGap.Continuum.ReflectedSquareTreeTwoChannelBound.Pair.first
#print axioms YMGap.Continuum.ReflectedSquareTreeTwoChannelBound.Pair.second
#print axioms YMGap.Continuum.ReflectedSquareTreeTwoChannelBound.Pair.multiplyTerm
#print axioms YMGap.Continuum.ReflectedSquareTreeTwoChannelBound.Pair.multiplyTerm_first
#print axioms YMGap.Continuum.ReflectedSquareTreeTwoChannelBound.Pair.multiplyTerm_second
#print axioms YMGap.Continuum.ReflectedSquareTreeTwoChannelBound.Pair.weight_nonnegative
#print axioms YMGap.Continuum.ReflectedSquareTreeTwoChannelBound.Pair.value_le
#print axioms YMGap.Continuum.ReflectedSquareTreeTwoChannelBound.Pair.amplitude
#print axioms YMGap.Continuum.ReflectedSquareTreeTwoChannelBound.Pair.observable_energy_le
#print axioms YMGap.Continuum.ReflectedSquareTreeTwoChannelBound.Pair.minor_le_full_energy
