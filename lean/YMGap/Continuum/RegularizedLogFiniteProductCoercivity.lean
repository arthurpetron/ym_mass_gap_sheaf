/-
# Selected finite-product entropy payment

Every factor remains in the literal ordered product and its weighted entropy.
Only selected occurrences contribute to the defect sum and its b/error cost.
The coefficient b and the selected defects may be signed. The prefactor c and
local error e are nonnegative. Zero and repeated factors need no division or
distinctness premise; skipped factors are retained, not erased.

This finite scalar consumer assumes only the displayed local inequalities.
It supplies no original-action instance, conditional integral, or gap estimate.
-/

import YMGap.Continuum.RegularizedLogFiniteProduct

namespace YMGap.Continuum.RegularizedLogFiniteProductCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RegularizedLogPolynomial (partialSum partial_nonnegative)
open YMGap.Continuum.RegularizedLogFiniteProduct
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv
private abbrev PE := PolyExpr
local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance (n : Nat) : OfNat PE n := ⟨.const (Int.ofNat n)⟩

private theorem qr (a b : PE) (h : RingNormaliser.normalize a = RingNormaliser.normalize b)
    (rho : Nat → Q') : RingNormaliser.eval rho a ≈ RingNormaliser.eval rho b :=
  poly_identity_of_normal_eq a b h rho

private theorem tc {a b c : Q'} (h : a ≈ b) (k : b ≈ c) : a ≈ c :=
  Q'.eqv_trans _ _ _ h k

private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  tc (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem nat_nonnegative (n : Nat) : (0 : Q') ≤ Q'.ofNat n := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact Int.natCast_nonneg n

/-- Number of selected occurrences, without deduplicating their labels. -/
def selectedCount {A : Type} (selected : A → Bool) : List A → Nat
  | [] => 0
  | x::xs => match selected x with
    | false => selectedCount selected xs
    | true => selectedCount selected xs+1

/-- The actual signed sum of the selected occurrence defects. -/
def selectedDefectSum {A : Type} (d : A → Q') (selected : A → Bool) : List A → Q'
  | [] => 0
  | x::xs => match selected x with
    | false => selectedDefectSum d selected xs
    | true => d x+selectedDefectSum d selected xs

private theorem mul_unit_cap {x y : Q'} (hx : x ≤ 1) (hy : (0 : Q') ≤ y) : x*y ≤ y :=
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ y hx hy)
    (Q'.le_of_eqv (Q'.one_mul_eqv y))

private theorem keep_step (a p pf S D d t c b e : Q')
    (ha0 : (0 : Q') ≤ a) (ha1 : a ≤ 1) (hp0 : (0 : Q') ≤ p) (hp1 : p ≤ 1)
    (ht0 : (0 : Q') ≤ t) (hc : (0 : Q') ≤ c) (he : (0 : Q') ≤ e)
    (hhead : a*d ≤ c*(pf+b*a+e)) (htail : p*D ≤ c*(S+b*t*p+e*t)) :
    (a*p)*(d+D) ≤ c*(p*pf+a*S+b*(t+1)*(a*p)+e*(t+1)) := by
  have hsum := Q'.add_le_add (Q'.mul_le_mul_of_nonneg_left _ _ p hhead hp0)
    (Q'.mul_le_mul_of_nonneg_left _ _ a htail ha0)
  have hl : (a*p)*(d+D) ≈ p*(a*d)+a*(p*D) :=
    qr ((.var 0*.var 1)*(.var 2+.var 3))
      (.var 1*(.var 0*.var 2)+.var 0*(.var 1*.var 3)) (by decide)
      (fun | 0 => a | 1 => p | 2 => d | _ => D)
  have hu : p*(c*(pf+b*a+e))+a*(c*(S+b*t*p+e*t)) ≈
      c*(p*pf+a*S+b*(t+1)*(a*p)+(p*e+a*(e*t))) :=
    qr (.var 1*(.var 5*(.var 2+.var 6*.var 0+.var 7))+
        .var 0*(.var 5*(.var 3+.var 6*.var 4*.var 1+.var 7*.var 4)))
      (.var 5*(.var 1*.var 2+.var 0*.var 3+
        .var 6*(.var 4+1)*(.var 0*.var 1)+(.var 1*.var 7+.var 0*(.var 7*.var 4))))
      (by decide) (fun | 0 => a | 1 => p | 2 => pf | 3 => S | 4 => t | 5 => c | 6 => b | _ => e)
  have herr : p*e+a*(e*t) ≤ e*(t+1) :=
    Q'.le_trans' _ _ _ (Q'.add_le_add (mul_unit_cap hp1 he)
      (mul_unit_cap ha1 (Q'.mul_nonneg _ _ he ht0)))
      (Q'.le_of_eqv (qr (.var 0+.var 0*.var 1) (.var 0*(.var 1+1))
        (by decide) (fun | 0 => e | _ => t)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hl)
    (Q'.le_trans' _ _ _ hsum (Q'.le_trans' _ _ _ (Q'.le_of_eqv hu)
      (Q'.mul_le_mul_of_nonneg_left _ _ c (Q'.add_le_add_left _ _ _ herr) hc)))

private theorem skip_step (a p pf S D t c b e : Q')
    (ha0 : (0 : Q') ≤ a) (ha1 : a ≤ 1) (hp0 : (0 : Q') ≤ p)
    (hpf0 : (0 : Q') ≤ pf) (ht0 : (0 : Q') ≤ t)
    (hc : (0 : Q') ≤ c) (he : (0 : Q') ≤ e)
    (htail : p*D ≤ c*(S+b*t*p+e*t)) :
    (a*p)*D ≤ c*(p*pf+a*S+b*t*(a*p)+e*t) := by
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ a htail ha0
  have hpad : a*S ≤ p*pf+a*S := Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _ (Q'.mul_nonneg _ _ hp0 hpf0))
    (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
  have herr := mul_unit_cap ha1 (Q'.mul_nonneg _ _ he ht0)
  have hu : a*(c*(S+b*t*p+e*t)) ≈ c*(a*S+b*t*(a*p)+a*(e*t)) :=
    qr (.var 0*(.var 4*(.var 2+.var 5*.var 3*.var 1+.var 6*.var 3)))
      (.var 4*(.var 0*.var 2+.var 5*.var 3*(.var 0*.var 1)+.var 0*(.var 6*.var 3)))
      (by decide) (fun | 0 => a | 1 => p | 2 => S | 3 => t | 4 => c | 5 => b | _ => e)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
    (Q'.le_trans' _ _ _ hscaled (Q'.le_trans' _ _ _ (Q'.le_of_eqv hu)
      (Q'.mul_le_mul_of_nonneg_left _ _ c
        (Q'.add_le_add (Q'.add_le_add_right _ _ _ hpad) herr) hc)))

private theorem mapped_bounds {A : Type} (f : A → Q') (xs : List A)
    (hf : ∀ a, a ∈ xs → (0 : Q') ≤ f a ∧ f a ≤ 1) :
    ∀ x, x ∈ xs.map f → (0 : Q') ≤ x ∧ x ≤ 1 := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  exact hf a ha

/-- Local selected payments on the same ordered product. The entropy term
retains skipped occurrences; b and every d(a) are allowed to be signed. -/
theorem selected_payment {A : Type} (f d : A → Q') (selected : A → Bool)
    (N : Nat) (xs : List A)
    (hf : ∀ a, a ∈ xs → (0 : Q') ≤ f a ∧ f a ≤ 1)
    (c b e : Q') (hc : (0 : Q') ≤ c) (he : (0 : Q') ≤ e)
    (hlocal : ∀ a, a ∈ xs → selected a = true →
      f a*d a ≤ c*(partialSum (f a) N+b*f a+e)) :
    product (xs.map f)*selectedDefectSum d selected xs ≤
      c*(weightedEntropy N (xs.map f)+b*Q'.ofNat (selectedCount selected xs)*product (xs.map f)+
        e*Q'.ofNat (selectedCount selected xs)) := by
  revert hf hlocal
  induction xs with
  | nil =>
      intro _ _
      change (1 : Q')*0 ≤ c*(0+b*0*1+e*0)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide : (1 : Q')*0 ≈ 0))
        (Q'.ge_of_eqv (qr (.var 0*(0+.var 1*0*1+.var 2*0)) 0 (by decide)
          (fun | 0 => c | 1 => b | _ => e)))
  | cons x xs ih =>
      intro hf hlocal
      have hx := hf x (by simp)
      have ht : ∀ a, a ∈ xs → (0 : Q') ≤ f a ∧ f a ≤ 1 :=
        fun a ha => hf a (List.mem_cons_of_mem x ha)
      have hp := product_bounds (xs.map f) (mapped_bounds f xs ht)
      have hi := ih ht (fun a ha hs => hlocal a (List.mem_cons_of_mem x ha) hs)
      cases hs : selected x with
      | false =>
          simpa only [selectedDefectSum, selectedCount, hs, List.map_cons, product, weightedEntropy]
            using skip_step (f x) (product (xs.map f)) (partialSum (f x) N)
              (weightedEntropy N (xs.map f)) (selectedDefectSum d selected xs)
              (Q'.ofNat (selectedCount selected xs)) c b e hx.1 hx.2 hp.1
              (partial_nonnegative (f x) hx.1 hx.2 N) (nat_nonnegative _) hc he hi
      | true =>
          have hhead := hlocal x (by simp) hs
          have hstep := keep_step (f x) (product (xs.map f)) (partialSum (f x) N)
            (weightedEntropy N (xs.map f)) (selectedDefectSum d selected xs) (d x)
            (Q'.ofNat (selectedCount selected xs)) c b e hx.1 hx.2 hp.1 hp.2
            (nat_nonnegative _) hc he hhead hi
          have hk : Q'.ofNat (selectedCount selected xs+1) ≈
              Q'.ofNat (selectedCount selected xs)+1 := Q'.ofNat_add_eqv _ 1
          have hpin : c*(product (xs.map f)*partialSum (f x) N+f x*weightedEntropy N (xs.map f)+
              b*Q'.ofNat (selectedCount selected xs+1)*(f x*product (xs.map f))+
              e*Q'.ofNat (selectedCount selected xs+1)) ≈
            c*(product (xs.map f)*partialSum (f x) N+f x*weightedEntropy N (xs.map f)+
              b*(Q'.ofNat (selectedCount selected xs)+1)*(f x*product (xs.map f))+
              e*(Q'.ofNat (selectedCount selected xs)+1)) :=
            mc (Q'.eqv_refl _) (Q'.add_eqv_congr'
              (Q'.add_eqv_congr' (Q'.eqv_refl _) (mc (mc (Q'.eqv_refl _) hk) (Q'.eqv_refl _)))
              (mc (Q'.eqv_refl _) hk))
          simpa only [selectedDefectSum, selectedCount, hs, List.map_cons, product, weightedEntropy]
            using Q'.le_trans' _ _ _ hstep (Q'.ge_of_eqv hpin)

/-- Replace the complete weighted entropy by the entropy of the same product.
The finite series error counts all occurrences, while b/e count only selected
occurrences. No denominator or factor independence is introduced. -/
theorem selected_product_payment {A : Type} (f d : A → Q') (selected : A → Bool)
    (N : Nat) (xs : List A)
    (hf : ∀ a, a ∈ xs → (0 : Q') ≤ f a ∧ f a ≤ 1)
    (c b e : Q') (hc : (0 : Q') ≤ c) (he : (0 : Q') ≤ e)
    (hlocal : ∀ a, a ∈ xs → selected a = true →
      f a*d a ≤ c*(partialSum (f a) N+b*f a+e)) :
    product (xs.map f)*selectedDefectSum d selected xs ≤
      c*(partialSum (product (xs.map f)) N+Q'.ofNat xs.length*Q'.invSucc N+
        b*Q'.ofNat (selectedCount selected xs)*product (xs.map f)+
        e*Q'.ofNat (selectedCount selected xs)) := by
  have hd := CReal.leAddOfSubLe (product_defect_bound N (xs.map f) (mapped_bounds f xs hf)).2
  have hd' : weightedEntropy N (xs.map f) ≤
      partialSum (product (xs.map f)) N+Q'.ofNat xs.length*Q'.invSucc N := by
    simpa only [List.length_map] using hd
  exact Q'.le_trans' _ _ _ (selected_payment f d selected N xs hf c b e hc he hlocal)
    (Q'.mul_le_mul_of_nonneg_left _ _ c
      (Q'.add_le_add_right _ _ _ (Q'.add_le_add_right _ _ _ hd')) hc)

end YMGap.Continuum.RegularizedLogFiniteProductCoercivity

#print axioms YMGap.Continuum.RegularizedLogFiniteProductCoercivity.selectedCount
#print axioms YMGap.Continuum.RegularizedLogFiniteProductCoercivity.selectedDefectSum
#print axioms YMGap.Continuum.RegularizedLogFiniteProductCoercivity.selected_payment
#print axioms YMGap.Continuum.RegularizedLogFiniteProductCoercivity.selected_product_payment
