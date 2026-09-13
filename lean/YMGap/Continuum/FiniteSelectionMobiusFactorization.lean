/-
# Exact factorization of finite inclusion-exclusion across two lists

Iterated finite differences commute with the split into two ordered lists.
If the original functional factors on every pair of subselections, its
coefficient factors too. This is finite algebra, with all multiplicities
retained, and supplies exact spectator resummation rather than an estimate.
-/

import YMGap.Continuum.FiniteSelectionMobius

namespace YMGap.Continuum.FiniteSelectionMobiusFactorization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteSelectionMobius

local infix:50 " ≈ " => Q'.eqv

theorem coefficient_mul_left {A : Type} (c : Q') (f : List A → Q') : ∀ xs : List A,
    coefficient (fun ys => c*f ys) xs ≈ c*coefficient f xs
  | [] => Q'.eqv_refl _
  | a :: xs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (coefficient_mul_left c (fun ys => f (a::ys)) xs)
        (Q'.neg_eqv_congr _ _ (coefficient_mul_left c f xs)))
      (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
        (.mul (.var 0) (.add (.var 1) (.neg (.var 2)))) (by decide)
        (fun i => if i = 0 then c else if i = 1 then coefficient (fun ys => f (a::ys)) xs else coefficient f xs))

theorem coefficient_mul_right {A : Type} (f : List A → Q') (c : Q') (xs : List A) :
    coefficient (fun ys => f ys*c) xs ≈ coefficient f xs*c :=
  Q'.eqv_trans _ _ _ (coefficient_congr _ _ xs (fun ys _ => Q'.mul_comm_eqv (f ys) c))
    (Q'.eqv_trans _ _ _ (coefficient_mul_left c f xs) (Q'.mul_comm_eqv c _))

theorem coefficient_append {A : Type} (f : List A → Q') : ∀ xs ys : List A,
    coefficient f (xs++ys) ≈ coefficient (fun as => coefficient (fun bs => f (as++bs)) ys) xs
  | [], _ => Q'.eqv_refl _
  | a :: xs, ys => Q'.add_eqv_congr'
      (coefficient_append (fun zs => f (a::zs)) xs ys)
      (Q'.neg_eqv_congr _ _ (coefficient_append f xs ys))

/-- Factorization is required only on actual computed subselections. -/
theorem coefficient_factorizes {A : Type} (f g h : List A → Q') (xs ys : List A)
    (hsplit : ∀ as, as ∈ selections xs → ∀ bs, bs ∈ selections ys → f (as++bs) ≈ g as*h bs) :
    coefficient f (xs++ys) ≈ coefficient g xs * coefficient h ys :=
  Q'.eqv_trans _ _ _ (coefficient_append f xs ys)
    (Q'.eqv_trans _ _ _ (coefficient_congr _ _ xs (fun as ha =>
      Q'.eqv_trans _ _ _ (coefficient_congr _ _ ys (fun bs hb => hsplit as ha bs hb))
        (coefficient_mul_left (g as) h ys))) (coefficient_mul_right g (coefficient h ys) xs))

end YMGap.Continuum.FiniteSelectionMobiusFactorization

#print axioms YMGap.Continuum.FiniteSelectionMobiusFactorization.coefficient_mul_left
#print axioms YMGap.Continuum.FiniteSelectionMobiusFactorization.coefficient_mul_right
#print axioms YMGap.Continuum.FiniteSelectionMobiusFactorization.coefficient_append
#print axioms YMGap.Continuum.FiniteSelectionMobiusFactorization.coefficient_factorizes
