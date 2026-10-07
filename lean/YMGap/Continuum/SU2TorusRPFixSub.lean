/-
# Torus RP (d9l): a ring substitution that fixes the variables of `X` fixes `X`

`poly_fix`: if `S` is a `RingSub n`, literally additive, respects prefix equivalence, has supported outputs, and
`S x_i ≈ x_i` for every variable `i` occurring in `X`, then `S X ≈PE X`. (Split chains satisfy all four.)

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPFixPoly
import YMGap.Continuum.SU2TorusRPStepSub

namespace YMGap.Continuum.SU2TorusRPFixSub

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2HaarAlgebra (PE pe_trans pe_symm pe_refl pe_append)
open YMGap.Continuum.SU2TorusRPSubst (RingSub pe_mul2 pe_smul)
open YMGap.Continuum.SU2TorusRPFixPoly (pw mp mp_single pe_single)

variable {n : Nat} {S : RatPoly → RatPoly} (hS : RingSub n S) (good : Nat → Prop)
  (hvar : ∀ i, good i → PE n (S (polyVar i)) (polyVar i))

include hS hvar in
theorem pw_fix (j : Nat) (hj : good j) : ∀ k, PE n (S (pw (polyVar j) k)) (pw (polyVar j) k)
  | 0 => hS.one
  | k + 1 => pe_trans n (hS.mul _ _) (pe_mul2 n (hvar j hj) (pw_fix j hj k))

include hS hvar in
theorem mp_fix : ∀ (m : List Nat) (j : Nat), (∀ i, exponentAt m i ≠ 0 → good (i + j)) →
    PE n (S (mp j m)) (mp j m)
  | [], _, _ => hS.one
  | e :: r, j, h => by
    refine pe_trans n (hS.mul _ _) (pe_mul2 n ?_ (mp_fix r (j + 1) fun i hi => by
      have := h (i + 1) hi; rwa [show i + 1 + j = i + (j + 1) by omega] at this))
    cases e with
    | zero => exact hS.one
    | succ e =>
      refine pw_fix hS good hvar j ?_ _
      have := h 0 (Nat.succ_ne_zero e); rwa [Nat.zero_add] at this

include hS hvar in
theorem poly_fix (hadd : ∀ p q, S (p ++ q) = S p ++ S q)
    (hpre : ∀ p q, QuaternionPrefixPolynomialEqv n p q → QuaternionPrefixPolynomialEqv n (S p) (S q))
    (hsup : ∀ p, YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini.SupportedQuaternionBlocks n (S p)) :
    ∀ X : RatPoly, (∀ t ∈ X, ∀ i, exponentAt t.1 i ≠ 0 → good i) → PE n (S X) X
  | [], _ => by
    have h := congrArg List.length (hadd [] [])
    rw [List.append_nil, List.length_append] at h
    rw [List.eq_nil_of_length_eq_zero (by omega : (S []).length = 0)]; exact pe_refl _ _
  | t :: X, h => by
    rw [show t :: X = [t] ++ X from rfl, hadd]
    refine pe_append n ?_ (poly_fix hadd hpre hsup X fun s hs => h s (List.mem_cons_of_mem _ hs))
    obtain ⟨mm, d, e, hd, hx⟩ := mp_single t.1 0
    have hR : polySmul t.2 (mp 0 t.1) = [(mm, t.2 * d)] := by rw [e]; rfl
    have hc : (t.2 * d).eqv t.2 := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hd) (Q'.mul_one_eqv _)
    have hex : ∀ i, exponentAt t.1 i = exponentAt mm i := fun i => by rw [hx]; rfl
    have hpq : QuaternionPrefixPolynomialEqv n [t] (polySmul t.2 (mp 0 t.1)) := by
      rw [hR]; exact .cons ⟨Q'.eqv_symm hc, fun i _ => hex i⟩ .nil
    have h1 := YMGap.Continuum.SU2TorusRPStepSub.prefix_pe n (hpre _ _ hpq) (hsup _) (hsup _)
    have h2 : PE n (S (polySmul t.2 (mp 0 t.1))) (polySmul t.2 (mp 0 t.1)) :=
      pe_trans n (hS.smul _ _) (pe_smul n t.2 (mp_fix hS good hvar t.1 0 fun i hi => by
        rw [Nat.add_zero]; exact h t (List.mem_cons_self ..) i hi))
    refine pe_trans n h1 (pe_trans n h2 ?_)
    rw [hR]; exact pe_single n (fun i => (hex i).symm) hc

end YMGap.Continuum.SU2TorusRPFixSub

#print axioms YMGap.Continuum.SU2TorusRPFixSub.poly_fix
