/-
# Ordered finite-product entropy defect

The literal product and the weighted sum retain every occurrence, including
repeated and zero factors. For factors in [0,1], the difference between this
weighted entropy sum and p_N of the product lies in [0,length/(N+1)].
The induction uses the existing finite two-factor defect, with no division,
positive floor, logarithm identity, or independence assumption.

This is finite scalar algebra for a later original-action consumer. It is
not a conditional entropy estimate, signed-response payment, or gap result.
-/

import YMGap.Continuum.RegularizedLogPolynomialProductDefect

namespace YMGap.Continuum.RegularizedLogFiniteProduct

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RegularizedLogPolynomial (partialSum partial_one partial_nonnegative)
open YMGap.Continuum.RegularizedLogPolynomialProductDefect (product_defect_bounds)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private theorem tc {a b c : Q'} (h : a ≈ b) (k : b ≈ c) : a ≈ c :=
  Q'.eqv_trans _ _ _ h k

/-- Literal ordered product, with unit empty product. -/
def product : List Q' → Q'
  | [] => 1
  | x::xs => x*product xs

/-- Each original partial sum carries the product of all other occurrences.
This division-free recursion also defines the expression at zero factors. -/
def weightedEntropy (N : Nat) : List Q' → Q'
  | [] => 0
  | x::xs => product xs*partialSum x N+x*weightedEntropy N xs

/-- Product bounds need no nonzero or distinct-factor assumption. -/
theorem product_bounds (xs : List Q')
    (hxs : ∀ x, x ∈ xs → (0 : Q') ≤ x ∧ x ≤ 1) :
    (0 : Q') ≤ product xs ∧ product xs ≤ 1 := by
  revert hxs
  induction xs with
  | nil => intro _; exact ⟨by decide, Q'.le_refl' 1⟩
  | cons x xs ih =>
      intro hxs
      have hx := hxs x (by simp)
      have ht := ih (fun y hy => hxs y (List.mem_cons_of_mem x hy))
      exact ⟨Q'.mul_nonneg _ _ hx.1 ht.1,
        Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hx.2 ht.1)
          (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _)) ht.2)⟩

theorem weightedEntropy_nonnegative (N : Nat) (xs : List Q')
    (hxs : ∀ x, x ∈ xs → (0 : Q') ≤ x ∧ x ≤ 1) :
    (0 : Q') ≤ weightedEntropy N xs := by
  revert hxs
  induction xs with
  | nil => intro _; exact Q'.le_refl' 0
  | cons x xs ih =>
      intro hxs
      have hx := hxs x (by simp)
      have ht : ∀ y, y ∈ xs → (0 : Q') ≤ y ∧ y ≤ 1 :=
        fun y hy => hxs y (List.mem_cons_of_mem x hy)
      exact Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _ (product_bounds xs ht).1 (partial_nonnegative x hx.1 hx.2 N))
        (Q'.mul_nonneg _ _ hx.1 (ih ht))

/-- Exact finite recurrence, without range assumptions on any factor. -/
theorem defect_cons (N : Nat) (x : Q') (xs : List Q') :
    weightedEntropy N (x::xs)-partialSum (product (x::xs)) N ≈
      x*(weightedEntropy N xs-partialSum (product xs) N)+
        (product xs*partialSum x N+x*partialSum (product xs) N-
          partialSum (x*product xs) N) :=
  poly_identity_of_normal_eq
    (.add (.add (.mul (.var 1) (.var 2)) (.mul (.var 0) (.var 3))) (.neg (.var 5)))
    (.add (.mul (.var 0) (.add (.var 3) (.neg (.var 4))))
      (.add (.add (.mul (.var 1) (.var 2)) (.mul (.var 0) (.var 4))) (.neg (.var 5))))
    (by decide) (fun | 0 => x | 1 => product xs | 2 => partialSum x N | 3 => weightedEntropy N xs | 4 => partialSum (product xs) N | _ => partialSum (x*product xs) N)

/-- The literal weighted entropy exceeds the entropy of the product by at
most one inverse-successor error per occurrence. Includes empty lists and N=0. -/
theorem product_defect_bound (N : Nat) (xs : List Q')
    (hxs : ∀ x, x ∈ xs → (0 : Q') ≤ x ∧ x ≤ 1) :
    (0 : Q') ≤ weightedEntropy N xs-partialSum (product xs) N ∧
      weightedEntropy N xs-partialSum (product xs) N ≤ Q'.ofNat xs.length*Q'.invSucc N := by
  revert hxs
  induction xs with
  | nil =>
      intro _
      have hz : weightedEntropy N []-partialSum (product []) N ≈ 0 :=
        tc (Q'.add_eqv_congr' (Q'.eqv_refl 0) (Q'.neg_eqv_congr _ _ (partial_one N)))
          (by decide)
      exact ⟨Q'.ge_of_eqv hz,
        Q'.le_trans' _ _ _ (Q'.le_of_eqv hz) (Q'.ge_of_eqv (Q'.zero_mul_eqv _))⟩
  | cons x xs ih =>
      intro hxs
      have hx := hxs x (by simp)
      have ht : ∀ y, y ∈ xs → (0 : Q') ≤ y ∧ y ≤ 1 :=
        fun y hy => hxs y (List.mem_cons_of_mem x hy)
      have hp := product_bounds xs ht
      have hi := ih ht
      have hd := product_defect_bounds x (product xs) hx.1 hx.2 hp.1 hp.2 N
      have he := defect_cons N x xs
      have hlo := Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ hx.1 hi.1) hd.1
      have hscaled : x*(weightedEntropy N xs-partialSum (product xs) N) ≤
          Q'.ofNat xs.length*Q'.invSucc N :=
        Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hx.2 hi.1)
          (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _)) hi.2)
      have hcap : Q'.ofNat xs.length*Q'.invSucc N+Q'.invSucc N ≈
          Q'.ofNat (x::xs).length*Q'.invSucc N :=
        tc (poly_identity_of_normal_eq
          (.add (.mul (.var 0) (.var 1)) (.var 1))
          (.mul (.add (.var 0) (.const 1)) (.var 1)) (by decide)
          (fun | 0 => Q'.ofNat xs.length | _ => Q'.invSucc N))
          (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.ofNat_add_eqv xs.length 1)))
      exact ⟨Q'.le_trans' _ _ _ hlo (Q'.ge_of_eqv he),
        Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
          (Q'.le_trans' _ _ _ (Q'.add_le_add hscaled hd.2) (Q'.le_of_eqv hcap))⟩

end YMGap.Continuum.RegularizedLogFiniteProduct

#print axioms YMGap.Continuum.RegularizedLogFiniteProduct.product
#print axioms YMGap.Continuum.RegularizedLogFiniteProduct.weightedEntropy
#print axioms YMGap.Continuum.RegularizedLogFiniteProduct.product_bounds
#print axioms YMGap.Continuum.RegularizedLogFiniteProduct.weightedEntropy_nonnegative
#print axioms YMGap.Continuum.RegularizedLogFiniteProduct.defect_cons
#print axioms YMGap.Continuum.RegularizedLogFiniteProduct.product_defect_bound
