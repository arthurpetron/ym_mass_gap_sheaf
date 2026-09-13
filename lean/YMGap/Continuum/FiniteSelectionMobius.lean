/-
# Constructive finite inclusion-exclusion on positional selections

The coefficient is computed by iterated finite differences of the SAME
list functional. Summing it over all positional selections reconstructs
that functional exactly. A coefficient vanishes if the functional vanishes
on all its subselections. No analytic expansion or convergence is assumed.
-/

import YMGap.Continuum.FinitePolynomialSubsetExpansion
import YMGap.Continuum.FiniteDeterministicKernelPushforward

namespace YMGap.Continuum.FiniteSelectionMobius

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

def coefficient {A : Type} (f : List A → Q') : List A → Q'
  | [] => f []
  | a :: xs => coefficient (fun ys => f (a :: ys)) xs + -(coefficient f xs)

theorem coefficient_congr {A : Type} (f g : List A → Q') : ∀ xs : List A,
    (∀ ys, ys ∈ selections xs → f ys ≈ g ys) → coefficient f xs ≈ coefficient g xs
  | [], h => h [] List.mem_cons_self
  | a :: xs, h => Q'.add_eqv_congr'
      (coefficient_congr (fun ys => f (a::ys)) (fun ys => g (a::ys)) xs
        (fun ys hy => h _ (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨ys, hy, rfl⟩)))))
      (Q'.neg_eqv_congr _ _ (coefficient_congr f g xs
        (fun ys hy => h ys (List.mem_append.mpr (Or.inl hy)))))

theorem coefficient_zero {A : Type} : ∀ xs : List A,
    coefficient (fun _ => (0 : Q')) xs ≈ 0
  | [] => Q'.eqv_refl 0
  | _ :: xs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (coefficient_zero xs) (Q'.neg_eqv_congr _ _ (coefficient_zero xs)))
      (Q'.add_neg_self_eqv 0)

theorem coefficient_zero_on {A : Type} (f : List A → Q') (xs : List A)
    (h : ∀ ys, ys ∈ selections xs → f ys ≈ 0) : coefficient f xs ≈ 0 :=
  Q'.eqv_trans _ _ _ (coefficient_congr f (fun _ => 0) xs h) (coefficient_zero xs)

theorem sum_append {A : Type} (f : A → Q') : ∀ xs ys : List A,
    listQSum f (xs++ys) ≈ listQSum f xs + listQSum f ys
  | [], ys => Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' (listQSum f ys)))
  | a :: xs, ys => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl (f a)) (sum_append f xs ys))
      (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))

theorem sum_map {A B : Type} (f : B → Q') (g : A → B) : ∀ xs : List A,
    listQSum f (xs.map g) = listQSum (fun a => f (g a)) xs
  | [] => rfl
  | a :: xs => by change f (g a) + _ = _; rw [sum_map f g xs]; rfl

/-- Exact finite Mobius inversion, including positional multiplicities. -/
theorem reconstruct {A : Type} (f : List A → Q') : ∀ xs : List A,
    listQSum (coefficient f) (selections xs) ≈ f xs
  | [] => Q'.eqv_of_eq (Q'.add_zero' (f []))
  | a :: xs => by
      refine Q'.eqv_trans _ _ _ (sum_append _ _ _) ?_
      rw [sum_map]
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (listQSum_add _ _ _)) ?_
      refine Q'.eqv_trans _ _ _ (listQSum_congr_on _ _ _ (fun ys _ => ?_))
        (reconstruct (fun zs => f (a::zs)) xs)
      exact poly_identity_of_normal_eq (.add (.var 0) (.add (.var 1) (.neg (.var 0))))
        (.var 1) (by decide) (fun i => if i = 0 then coefficient f ys else coefficient (fun zs => f (a::zs)) ys)

theorem sum_filter_zero {A : Type} (f : A → Q') (keep : A → Bool) : ∀ xs : List A,
    (∀ x, x ∈ xs → keep x = false → f x ≈ 0) →
    listQSum f xs ≈ listQSum f (xs.filter keep)
  | [], _ => Q'.eqv_refl 0
  | x :: xs, h => by
      have ht := sum_filter_zero f keep xs (fun y hy => h y (List.mem_cons_of_mem x hy))
      cases hk : keep x with
      | true =>
          simpa only [List.filter_cons, hk, listQSum] using Q'.add_eqv_congr' (Q'.eqv_refl (f x)) ht
      | false =>
          simpa only [List.filter_cons, hk, listQSum] using
            Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (h x List.mem_cons_self hk) ht)
              (Q'.eqv_of_eq (Q'.zero_add' _))

theorem reconstruct_filtered {A : Type} (f : List A → Q') (keep : List A → Bool) (xs : List A)
    (h : ∀ ys, ys ∈ selections xs → keep ys = false → coefficient f ys ≈ 0) :
    f xs ≈ listQSum (coefficient f) ((selections xs).filter keep) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (reconstruct f xs)) (sum_filter_zero _ _ _ h)

end YMGap.Continuum.FiniteSelectionMobius

#print axioms YMGap.Continuum.FiniteSelectionMobius.coefficient
#print axioms YMGap.Continuum.FiniteSelectionMobius.coefficient_congr
#print axioms YMGap.Continuum.FiniteSelectionMobius.coefficient_zero
#print axioms YMGap.Continuum.FiniteSelectionMobius.coefficient_zero_on
#print axioms YMGap.Continuum.FiniteSelectionMobius.sum_append
#print axioms YMGap.Continuum.FiniteSelectionMobius.sum_map
#print axioms YMGap.Continuum.FiniteSelectionMobius.reconstruct
#print axioms YMGap.Continuum.FiniteSelectionMobius.sum_filter_zero
#print axioms YMGap.Continuum.FiniteSelectionMobius.reconstruct_filtered
