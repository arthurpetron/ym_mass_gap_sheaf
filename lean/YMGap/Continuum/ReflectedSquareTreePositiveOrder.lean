/-
# Positive order on actual finite square-channel trees

The order compares weighted evaluation against EVERY nonnegative function
of the actual polynomial channel. Products keep overlapping variables.
Appending nonnegative trees and enlarging finite spin prefixes preserve
the order. This is proved finite algebra, not an analytic input or a new
physical norm. No transfer or continuum statement is made here.
-/

import YMGap.Continuum.ReflectedSquareTreeRetainedChannel

namespace YMGap.Continuum.ReflectedSquareTreePositiveOrder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.BF4ExactSlabLocalSquareExpansion
open YMGap.Continuum.ReflectedSquareTreeRetainedChannel
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

def value (f : RatPoly → Q') : SquareTree → Q'
  | .zero => 0
  | .term w p => w * f p
  | .add s t => value f s + value f t

theorem value_nonnegative (f : RatPoly → Q') (hf : ∀ p, (0 : Q') ≤ f p) :
    (t : SquareTree) → t.Nonnegative → (0 : Q') ≤ value f t
  | .zero, _ => by change (0 : Q') ≤ 0; decide
  | .term _ _, h => Q'.mul_nonneg _ _ h (hf _)
  | .add s t, h => Q'.zero_le_add _ _ (value_nonnegative f hf s h.1) (value_nonnegative f hf t h.2)

theorem value_mono (f g : RatPoly → Q') (h : ∀ p, f p ≤ g p) :
    (t : SquareTree) → t.Nonnegative → value f t ≤ value g t
  | .zero, _ => Q'.le_refl' _
  | .term _ _, ht => Q'.mul_le_mul_of_nonneg_left _ _ _ (h _) ht
  | .add s t, ht => Q'.add_le_add (value_mono f g h s ht.1) (value_mono f g h t ht.2)

theorem value_multiplyTerm (f : RatPoly → Q') (a : Q') (p : RatPoly) : ∀ t : SquareTree,
    Q'.eqv (value f (t.multiplyTerm a p)) (a * value (fun q => f (polyMul p q)) t)
  | .zero => Q'.eqv_symm (QPoly.q_mul_zero a)
  | .term _ _ => Q'.mul_assoc_eqv _ _ _
  | .add s t => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (value_multiplyTerm f a p s) (value_multiplyTerm f a p t))
      (Q'.eqv_symm (Q'.mul_add_eqv _ _ _))

theorem value_product (f : RatPoly → Q') : ∀ s t : SquareTree,
    Q'.eqv (value f (s.product t)) (value (fun p => value (fun q => f (polyMul p q)) t) s)
  | .zero, _ => Q'.eqv_refl _
  | .term a p, t => value_multiplyTerm f a p t
  | .add s u, t => Q'.add_eqv_congr' (value_product f s t) (value_product f u t)

/-- A finite order law, carrying no existential analytic constants. -/
def PositiveOrder (s t : SquareTree) : Prop :=
  ∀ f : RatPoly → Q', (∀ p, (0 : Q') ≤ f p) → value f s ≤ value f t

namespace PositiveOrder

theorem refl (t : SquareTree) : PositiveOrder t t := fun _ _ => Q'.le_refl' _

theorem trans {s t u : SquareTree} (h : PositiveOrder s t) (k : PositiveOrder t u) : PositiveOrder s u :=
  fun f hf => Q'.le_trans' _ _ _ (h f hf) (k f hf)

theorem add {s t u v : SquareTree} (h : PositiveOrder s t) (k : PositiveOrder u v) :
    PositiveOrder (.add s u) (.add t v) := fun f hf => Q'.add_le_add (h f hf) (k f hf)

theorem product_left {s t : SquareTree} (h : PositiveOrder s t) (r : SquareTree) (hr : r.Nonnegative) :
    PositiveOrder (s.product r) (t.product r) := fun f hf =>
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (value_product f s r))
    (Q'.le_trans' _ _ _ (h _ (fun p => value_nonnegative _ (fun q => hf (polyMul p q)) r hr))
      (Q'.ge_of_eqv (value_product f t r)))

theorem product_right {s t : SquareTree} (h : PositiveOrder s t) (r : SquareTree) (hr : r.Nonnegative) :
    PositiveOrder (r.product s) (r.product t) := fun f hf =>
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (value_product f r s))
    (Q'.le_trans' _ _ _ (value_mono _ _ (fun p => h _ (fun q => hf (polyMul p q))) r hr)
      (Q'.ge_of_eqv (value_product f r t)))

theorem product {s t u v : SquareTree} (h : PositiveOrder s t) (k : PositiveOrder u v)
    (hu : u.Nonnegative) (ht : t.Nonnegative) : PositiveOrder (s.product u) (t.product v) :=
  (h.product_left u hu).trans (k.product_right t ht)

theorem leaf : {t : SquareTree} → (l : Leaf t) → t.Nonnegative → PositiveOrder (.term l.weight l.channel) t
  | .term _ _, .here _ _, _ => refl _
  | .add _ t, .left l, h => fun f hf => Q'.le_trans' _ _ _ (leaf l h.1 f hf)
      (Q'.add_le_self_of_nonneg _ _ (value_nonnegative f hf t h.2))
  | .add s _, .right l, h => fun f hf => Q'.le_trans' _ _ _ (leaf l h.2 f hf)
      (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ (value_nonnegative f hf s h.1))
        (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

private theorem sum_nonnegative {A : Type} (f : A → SquareTree) (hf : ∀ a, (f a).Nonnegative) :
    ∀ xs : List A, (SquareTree.sum f xs).Nonnegative
  | [] => True.intro
  | a :: xs => ⟨hf a, sum_nonnegative f hf xs⟩

private theorem value_sum_append {A : Type} (g : RatPoly → Q') (f : A → SquareTree) : ∀ xs ys : List A,
    Q'.eqv (value g (SquareTree.sum f (xs ++ ys))) (value g (SquareTree.sum f xs) + value g (SquareTree.sum f ys))
  | [], _ => Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _))
  | _ :: xs, ys => Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (value_sum_append g f xs ys))
      (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))

theorem sum_append {A : Type} (f : A → SquareTree) (hf : ∀ a, (f a).Nonnegative) (xs ys : List A) :
    PositiveOrder (SquareTree.sum f xs) (SquareTree.sum f (xs ++ ys)) := fun g hg =>
  Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ (value_nonnegative g hg _ (sum_nonnegative f hf ys)))
    (Q'.ge_of_eqv (value_sum_append g f xs ys))

theorem range_mono (f : Nat → SquareTree) (hf : ∀ i, (f i).Nonnegative) (N K : Nat) (h : N ≤ K) :
    PositiveOrder (SquareTree.sum f (List.range N)) (SquareTree.sum f (List.range K)) := by
  have he : List.range K = List.range N ++ (List.range (K-N)).map (fun i => N+i) :=
    (congrArg List.range (Nat.add_sub_of_le h)).symm.trans List.range_add
  rw [he]
  exact sum_append f hf _ _

theorem finiteProduct {A : Type} {half : Nat} (f g : A → RatPoly) :
    (xs : List A) → (P : (a : A) → a ∈ xs → LocalSquareExpansion half (f a)) →
    (Q : (a : A) → a ∈ xs → LocalSquareExpansion half (g a)) →
    (∀ a ha, PositiveOrder (P a ha).tree (Q a ha).tree) →
    PositiveOrder (LocalSquareExpansion.finiteProduct f xs P).tree (LocalSquareExpansion.finiteProduct g xs Q).tree
  | [], _, _, _ => refl _
  | a :: xs, P, Q, h =>
      (h a List.mem_cons_self).product
        (finiteProduct f g xs (fun b hb => P b (List.mem_cons_of_mem a hb))
          (fun b hb => Q b (List.mem_cons_of_mem a hb)) (fun b hb => h b (List.mem_cons_of_mem a hb)))
        (LocalSquareExpansion.finiteProduct f xs (fun b hb => P b (List.mem_cons_of_mem a hb))).weightsNonnegative
        (Q a List.mem_cons_self).weightsNonnegative

end PositiveOrder

end YMGap.Continuum.ReflectedSquareTreePositiveOrder

#print axioms YMGap.Continuum.ReflectedSquareTreePositiveOrder.value
#print axioms YMGap.Continuum.ReflectedSquareTreePositiveOrder.value_nonnegative
#print axioms YMGap.Continuum.ReflectedSquareTreePositiveOrder.value_mono
#print axioms YMGap.Continuum.ReflectedSquareTreePositiveOrder.value_multiplyTerm
#print axioms YMGap.Continuum.ReflectedSquareTreePositiveOrder.value_product
#print axioms YMGap.Continuum.ReflectedSquareTreePositiveOrder.PositiveOrder
#print axioms YMGap.Continuum.ReflectedSquareTreePositiveOrder.PositiveOrder.refl
#print axioms YMGap.Continuum.ReflectedSquareTreePositiveOrder.PositiveOrder.trans
#print axioms YMGap.Continuum.ReflectedSquareTreePositiveOrder.PositiveOrder.add
#print axioms YMGap.Continuum.ReflectedSquareTreePositiveOrder.PositiveOrder.product_left
#print axioms YMGap.Continuum.ReflectedSquareTreePositiveOrder.PositiveOrder.product_right
#print axioms YMGap.Continuum.ReflectedSquareTreePositiveOrder.PositiveOrder.product
#print axioms YMGap.Continuum.ReflectedSquareTreePositiveOrder.PositiveOrder.leaf
#print axioms YMGap.Continuum.ReflectedSquareTreePositiveOrder.PositiveOrder.sum_append
#print axioms YMGap.Continuum.ReflectedSquareTreePositiveOrder.PositiveOrder.range_mono
#print axioms YMGap.Continuum.ReflectedSquareTreePositiveOrder.PositiveOrder.finiteProduct
