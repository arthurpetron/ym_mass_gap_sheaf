/-
# Order-safe finite selections and inclusion-exclusion

Selections are exactly ordered sublists. Duplicate-free input gives a
duplicate-free enumeration, so deterministic fiber grouping counts each
selection once. Finite differences of a permutation-invariant functional
are permutation invariant, permitting a filtered split to be concatenated
without changing its signed coefficient.
-/

import YMGap.Continuum.FiniteSelectionMobius
import YMGap.Continuum.CayleyPruferInjection

namespace YMGap.Continuum.FiniteSelectionOrder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteSelectionMobius
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

theorem selected_sublist {A : Type} : ∀ {xs ys : List A},
    ys ∈ selections xs → ys.Sublist xs
  | [], ys, h => by
      have he := List.mem_singleton.mp h
      subst ys
      exact .slnil
  | a :: xs, ys, h => by
      rcases List.mem_append.mp h with h | h
      · exact (selected_sublist h).cons a
      · obtain ⟨zs, hz, rfl⟩ := List.mem_map.mp h
        exact (selected_sublist hz).cons₂ a

theorem sublist_selected {A : Type} {xs ys : List A} (h : ys.Sublist xs) :
    ys ∈ selections xs := by
  induction h with
  | slnil => exact List.mem_cons_self
  | cons a _ ih => exact List.mem_append.mpr (Or.inl ih)
  | cons₂ a _ ih => exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨_, ih, rfl⟩))

theorem filter_selected {A : Type} (keep : A → Bool) : ∀ xs : List A,
    xs.filter keep ∈ selections xs
  | [] => List.mem_cons_self
  | a :: xs => by
      cases hk : keep a with
      | false =>
          simpa only [List.filter_cons, hk] using
            (List.mem_append.mpr (Or.inl (filter_selected keep xs)) :
              xs.filter keep ∈ selections (a::xs))
      | true =>
          simpa only [List.filter_cons, hk] using
            (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨_, filter_selected keep xs, rfl⟩)) :
              a :: xs.filter keep ∈ selections (a::xs))

theorem selections_eq_sublists {A : Type} : ∀ xs : List A,
    selections xs = YMGap.Continuum.PenroseDomInduction.sublists xs
  | [] => rfl
  | a :: xs => by
      change selections xs ++ (selections xs).map _ = _
      rw [selections_eq_sublists xs]
      rfl

theorem selections_nodup {A : Type} (xs : List A) (h : xs.Nodup) :
    (selections xs).Nodup := by
  rw [selections_eq_sublists]
  exact YMGap.Continuum.CayleyPruferInjection.sublists_nodup xs h

/-- The swap case is the commutation of two finite differences. -/
theorem coefficient_perm {A : Type} {xs ys : List A} (h : xs.Perm ys)
    (f : List A → Q')
    (hf : ∀ as bs : List A, as.Perm bs → f as ≈ f bs) :
    coefficient f xs ≈ coefficient f ys := by
  induction h generalizing f with
  | nil => exact Q'.eqv_refl _
  | cons a h ih =>
      exact Q'.add_eqv_congr'
        (ih (fun zs => f (a::zs)) (fun as bs hp => hf _ _ (hp.cons a)))
        (Q'.neg_eqv_congr _ _ (ih f hf))
  | swap a b xs =>
      have hab := coefficient_congr (fun zs => f (b::a::zs)) (fun zs => f (a::b::zs)) xs
        (fun zs _ => hf _ _ (List.Perm.swap a b zs))
      change (coefficient (fun zs => f (b::a::zs)) xs + -coefficient (fun zs => f (b::zs)) xs) +
        -(coefficient (fun zs => f (a::zs)) xs + -coefficient f xs) ≈ _
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.add_eqv_congr' hab (Q'.eqv_refl _)) (Q'.eqv_refl _)) ?_
      exact poly_identity_of_normal_eq
        (.add (.add (.var 0) (.neg (.var 1))) (.neg (.add (.var 2) (.neg (.var 3)))))
        (.add (.add (.var 0) (.neg (.var 2))) (.neg (.add (.var 1) (.neg (.var 3))))) (by decide)
        (fun i => if i = 0 then coefficient (fun zs => f (a::b::zs)) xs
          else if i = 1 then coefficient (fun zs => f (b::zs)) xs
          else if i = 2 then coefficient (fun zs => f (a::zs)) xs else coefficient f xs)
  | trans h₁ h₂ ih₁ ih₂ => exact Q'.eqv_trans _ _ _ (ih₁ f hf) (ih₂ f hf)

end YMGap.Continuum.FiniteSelectionOrder

#print axioms YMGap.Continuum.FiniteSelectionOrder.selected_sublist
#print axioms YMGap.Continuum.FiniteSelectionOrder.sublist_selected
#print axioms YMGap.Continuum.FiniteSelectionOrder.filter_selected
#print axioms YMGap.Continuum.FiniteSelectionOrder.selections_eq_sublists
#print axioms YMGap.Continuum.FiniteSelectionOrder.selections_nodup
#print axioms YMGap.Continuum.FiniteSelectionOrder.coefficient_perm
