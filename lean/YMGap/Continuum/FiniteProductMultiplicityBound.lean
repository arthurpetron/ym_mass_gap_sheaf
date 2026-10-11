/-
# Finite product lower bound from a literal multiplicity cap

For factors in [0,1], replacing every occurrence count by a common upper
bound can only decrease the product. The carrier is a finite duplicate-free
list, and the occurrence list may repeat its members in any order.

This uses the scalar fold of the original-action localization module. The
proof groups occurrences constructively by filtering one carrier element
at a time; it uses neither division by a factor nor permutation-by-erasure.
In particular zero factors, cap zero, and empty lists are included. This is
finite scalar algebra, not an independent-variable or Haar assertion.
-/

import YMGap.Continuum.BF4ExactSlabPolynomialActionLocalization
import YMGap.Continuum.HeatKernelRGStep

namespace YMGap.Continuum.FiniteProductMultiplicityBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabPolynomialActionLocalization (scalarProduct)
open YMGap.Continuum.RGTransport (qpow qpow_nonneg)
open YMGap.Continuum.HeatKernelRGStep (qpow_antitone)

local infix:50 " ≈ " => Q'.eqv

private theorem swap_front (a b c : Q') : a*(b*c) ≈ b*(a*c) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv a b c))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ c (Q'.mul_comm_eqv a b))
      (Q'.mul_assoc_eqv b a c))

private theorem product_nonnegative {A : Type} (f : A → Q') :
    ∀ xs : List A, (∀ a, a ∈ xs → (0 : Q') ≤ f a) →
      (0 : Q') ≤ scalarProduct f xs
  | [], _ => by change (0 : Q') ≤ 1; decide
  | a::xs, hf => Q'.mul_nonneg _ _ (hf a (List.mem_cons_self))
      (product_nonnegative f xs (fun b hb => hf b (List.mem_cons_of_mem a hb)))

/-- Exact head-value grouping with all occurrences and their multiplicity.
No bounds on the factors are required for this identity. -/
theorem scalarProduct_count_split {A : Type} [DecidableEq A] [BEq A] [LawfulBEq A]
    (f : A → Q') (a : A) : ∀ xs : List A,
    scalarProduct f xs ≈ qpow (f a) (xs.count a) *
      scalarProduct f (xs.filter (fun b => decide (b ≠ a)))
  | [] => Q'.eqv_symm (Q'.one_mul_eqv 1)
  | b::xs => by
      by_cases h : b = a
      · subst b
        rw [List.count_cons_self,
          List.filter_cons_of_neg (by
            change ¬ decide (a ≠ a) = true
            intro hh
            exact (of_decide_eq_true hh) rfl)]
        change f a * scalarProduct f xs ≈
          (qpow (f a) (xs.count a) * f a) *
            scalarProduct f (xs.filter (fun b => decide (b ≠ a)))
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (scalarProduct_count_split f a xs))
          (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
            (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)))
      · rw [List.count_cons_of_ne h,
          List.filter_cons_of_pos (p := fun b => decide (b ≠ a)) (decide_eq_true h)]
        change f b * scalarProduct f xs ≈
          qpow (f a) (xs.count a) *
            (f b * scalarProduct f (xs.filter (fun b => decide (b ≠ a))))
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (scalarProduct_count_split f a xs))
          (swap_front _ _ _)

/-- A common exponent cap on a nodup carrier gives a lower bound for the
original occurrence product. Bounds on `f` are needed only on the carrier. -/
theorem scalarProduct_multiplicity_bound {A : Type} [DecidableEq A] [BEq A] [LawfulBEq A]
    (f : A → Q') (cap : Nat) : ∀ (carrier xs : List A),
    carrier.Nodup →
    (∀ a, a ∈ xs → a ∈ carrier) →
    (∀ a, a ∈ carrier → xs.count a ≤ cap) →
    (∀ a, a ∈ carrier → (0 : Q') ≤ f a ∧ f a ≤ (1 : Q')) →
    scalarProduct (fun a => qpow (f a) cap) carrier ≤ scalarProduct f xs
  | [], [], _, _, _, _ => Q'.le_refl' _
  | [], a::_, _, hsub, _, _ =>
      False.elim (List.not_mem_nil (hsub a List.mem_cons_self))
  | a::as, xs, hn, hsub, hcount, hf => by
      let rest := xs.filter (fun b => decide (b ≠ a))
      have hrest : ∀ b, b ∈ rest → b ∈ as := by
        intro b hb
        obtain ⟨hbx, hba⟩ := List.mem_filter.mp hb
        rcases List.mem_cons.mp (hsub b hbx) with heq | htail
        · exact False.elim ((of_decide_eq_true hba) heq)
        · exact htail
      have hcounts : ∀ b, b ∈ as → rest.count b ≤ cap := by
        intro b hb
        exact Nat.le_trans (List.Sublist.count_le b List.filter_sublist)
          (hcount b (List.mem_cons_of_mem a hb))
      have hfTail : ∀ b, b ∈ as → (0 : Q') ≤ f b ∧ f b ≤ (1 : Q') :=
        fun b hb => hf b (List.mem_cons_of_mem a hb)
      have ht := scalarProduct_multiplicity_bound f cap as rest
        (List.nodup_cons.mp hn).2 hrest hcounts hfTail
      have ha := hf a List.mem_cons_self
      have hp := qpow_antitone ha.1 ha.2 (xs.count a) cap
        (hcount a List.mem_cons_self)
      have hrest0 : (0 : Q') ≤ scalarProduct f rest :=
        product_nonnegative f rest (fun b hb => (hfTail b (hrest b hb)).1)
      change qpow (f a) cap * scalarProduct (fun b => qpow (f b) cap) as ≤ _
      exact Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ ht (qpow_nonneg _ ha.1 cap))
        (Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_right _ _ _ hp hrest0)
          (Q'.ge_of_eqv (scalarProduct_count_split f a xs)))

#print axioms scalarProduct_count_split
#print axioms scalarProduct_multiplicity_bound

end YMGap.Continuum.FiniteProductMultiplicityBound
