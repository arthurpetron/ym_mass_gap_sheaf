/-
# Relative weight bounds on the SAME finite reflected-square channels

This finite relation compares only weights; every polynomial channel is
literally shared. Products keep overlapping variables and multiply their
explicit comparison factors. The original Haar-square sums inherit the
bound. The local-expansion constructors preserve the relation, so it can
be applied directly to the existing physical crossing-interface trees.

No analytic hypothesis, inverse, density, transfer identification or
continuum assertion is introduced by this finite algebra.
-/

import YMGap.Continuum.BF4ExactSlabLocalSquareExpansion

namespace YMGap.Continuum.BF4ExactSlabSquareWeightComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.RGTransport (qpow)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.BF4ExactSlabAllCutoffReflectionPositivity
open YMGap.Continuum.BF4ExactSlabLocalSquareExpansion

/-- The same finite channels, with an explicit relative lower weight factor. -/
inductive WeightBound (c : Q') : SquareTree → SquareTree → Prop where
  | zero : WeightBound c .zero .zero
  | term (a b : Q') (p : RatPoly) (bound : c*a ≤ b) : WeightBound c (.term a p) (.term b p)
  | add {p q r s : SquareTree} : WeightBound c p r → WeightBound c q s →
      WeightBound c (.add p q) (.add r s)

namespace WeightBound

theorem change_factor {c d : Q'} {p q : SquareTree} (h : WeightBound c p q)
    (he : Q'.eqv d c) : WeightBound d p q := by
  induction h with
  | zero => exact .zero
  | term a b p hab => exact .term a b p (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ a he)) hab)
  | add _ _ ih ik => exact .add ih ik

theorem refl (p : SquareTree) : WeightBound 1 p p := by
  induction p with
  | zero => exact .zero
  | term a p => exact .term a a p (Q'.le_of_eqv (Q'.one_mul_eqv a))
  | add p q ih ik => exact .add ih ik

theorem scaled (p : SquareTree) (hp : p.Nonnegative) (c a b : Q') (h : c*a ≤ b) :
    WeightBound c (p.scale a) (p.scale b) := by
  induction p with
  | zero => exact .zero
  | term s p =>
      exact .term (a*s) (b*s) p (Q'.le_trans' _ _ _
        (Q'.ge_of_eqv (Q'.mul_assoc_eqv c a s))
        (Q'.mul_le_mul_of_nonneg_right _ _ s h hp))
  | add p q ih ik => exact .add (ih hp.1) (ik hp.2)

private theorem multiply_weights {c d a b s t : Q'}
    (hd : (0 : Q') ≤ d) (ha : (0 : Q') ≤ a) (ht : (0 : Q') ≤ t)
    (hcs : c*s ≤ t) (hda : d*a ≤ b) : (c*d)*(s*a) ≤ t*b := by
  have he : Q'.eqv ((c*d)*(s*a)) ((c*s)*(d*a)) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (by decide)
      (fun | 0 => c | 1 => d | 2 => s | _ => a)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he) (Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ (d*a) hcs (Q'.mul_nonneg d a hd ha))
    (Q'.mul_le_mul_of_nonneg_left _ _ t hda ht))

theorem multiplyTerm {c d s t : Q'} {u v : SquareTree}
    (h : WeightBound d u v) (hu : u.Nonnegative)
    (hd : (0 : Q') ≤ d) (ht : (0 : Q') ≤ t) (hcs : c*s ≤ t) (p : RatPoly) :
    WeightBound (c*d) (u.multiplyTerm s p) (v.multiplyTerm t p) := by
  induction h with
  | zero => exact .zero
  | term a b q hab => exact .term (s*a) (t*b) _ (multiply_weights hd hu ht hcs hab)
  | add h k ih ik => exact .add (ih hu.1) (ik hu.2)

theorem product {c d : Q'} {p q r s : SquareTree}
    (h : WeightBound c p q) (k : WeightBound d r s)
    (hr : r.Nonnegative) (hq : q.Nonnegative) (hd : (0 : Q') ≤ d) :
    WeightBound (c*d) (p.product r) (q.product s) := by
  induction h with
  | zero => exact .zero
  | term a b p hab => exact multiplyTerm k hr hd hq hab p
  | add h j ih ik => exact .add (ih hq.1) (ik hq.2)

theorem haar_bound {c : Q'} {p q : SquareTree} (h : WeightBound c p q) (blocks : Nat) :
    c * haarSquareSum blocks p ≤ haarSquareSum blocks q := by
  induction h with
  | zero => exact Q'.le_of_eqv (Q'.mul_zero_eqv c)
  | term a b p hab =>
      exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _))
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hab (SumOfSquares.q_mul_self_nonneg _))
  | add h k ih ik =>
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_add_eqv _ _ _)) (Q'.add_le_add ih ik)

theorem finiteSum {A : Type} {half : Nat} {c : Q'} (f g : A → RatPoly) :
    ∀ xs : List A,
      ∀ P : (a : A) → a ∈ xs → LocalSquareExpansion half (f a),
      ∀ Q : (a : A) → a ∈ xs → LocalSquareExpansion half (g a),
      (∀ a ha, WeightBound c (P a ha).tree (Q a ha).tree) →
      WeightBound c (LocalSquareExpansion.finiteSum f xs P).tree
        (LocalSquareExpansion.finiteSum g xs Q).tree
  | [], _, _, _ => .zero
  | a::xs, P, Q, h => .add (h a List.mem_cons_self)
      (finiteSum f g xs (fun b hb => P b (List.mem_cons_of_mem a hb))
        (fun b hb => Q b (List.mem_cons_of_mem a hb))
        (fun b hb => h b (List.mem_cons_of_mem a hb)))

theorem finiteProduct {A : Type} {half : Nat} (c : Q') (hc : (0 : Q') ≤ c)
    (f g : A → RatPoly) : ∀ xs : List A,
      ∀ P : (a : A) → a ∈ xs → LocalSquareExpansion half (f a),
      ∀ Q : (a : A) → a ∈ xs → LocalSquareExpansion half (g a),
      (∀ a ha, WeightBound c (P a ha).tree (Q a ha).tree) →
      WeightBound (qpow c xs.length) (LocalSquareExpansion.finiteProduct f xs P).tree
        (LocalSquareExpansion.finiteProduct g xs Q).tree
  | [], _, _, _ => .term 1 1 _ (by change (1 : Q')*1 ≤ 1; decide)
  | a::xs, P, Q, h => by
      let pt := LocalSquareExpansion.finiteProduct f xs (fun b hb => P b (List.mem_cons_of_mem a hb))
      let qt := LocalSquareExpansion.finiteProduct g xs (fun b hb => Q b (List.mem_cons_of_mem a hb))
      have ht := finiteProduct c hc f g xs
        (fun b hb => P b (List.mem_cons_of_mem a hb))
        (fun b hb => Q b (List.mem_cons_of_mem a hb))
        (fun b hb => h b (List.mem_cons_of_mem a hb))
      have hk := product (h a List.mem_cons_self) ht pt.weightsNonnegative
        (Q a List.mem_cons_self).weightsNonnegative (RGTransport.qpow_nonneg c hc xs.length)
      exact hk.change_factor (Q'.mul_comm_eqv (qpow c xs.length) c)

end WeightBound
end YMGap.Continuum.BF4ExactSlabSquareWeightComparison

#print axioms YMGap.Continuum.BF4ExactSlabSquareWeightComparison.WeightBound
#print axioms YMGap.Continuum.BF4ExactSlabSquareWeightComparison.WeightBound.change_factor
#print axioms YMGap.Continuum.BF4ExactSlabSquareWeightComparison.WeightBound.refl
#print axioms YMGap.Continuum.BF4ExactSlabSquareWeightComparison.WeightBound.scaled
#print axioms YMGap.Continuum.BF4ExactSlabSquareWeightComparison.WeightBound.multiplyTerm
#print axioms YMGap.Continuum.BF4ExactSlabSquareWeightComparison.WeightBound.product
#print axioms YMGap.Continuum.BF4ExactSlabSquareWeightComparison.WeightBound.haar_bound
#print axioms YMGap.Continuum.BF4ExactSlabSquareWeightComparison.WeightBound.finiteSum
#print axioms YMGap.Continuum.BF4ExactSlabSquareWeightComparison.WeightBound.finiteProduct
