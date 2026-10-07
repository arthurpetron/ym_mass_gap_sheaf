/-
# Haar factorization over arbitrary disjoint block supports (R1, commit 1)

ADDITIVE.  Generalizes Realizer's prefix-split `haar_factor`.  The blocks of `p` and `q` may be
any disjoint sets of link blocks, not only a prefix and its shifted complement.  This is the
form the polymer expansion needs.  Link-disjoint polymers use disjoint sets of
`links.idxOf`-blocks.

* `BlockFree m k`: monomial `m` has zero exponent on all four coordinates of block `k`.
* `mono_disj`: `H_n(m₁m₂) ≈ H_n(m₁) H_n(m₂)` when every block `k < n` is free in `m₁` or in
  `m₂`.
* `haar_disj`: for `A : ℕ → Bool`, suppose `p` is free off `A` and `q` is free on `A`.  Then
  `∫_n p·q ≈ ∫_n p · ∫_n q`.
-/

import YMGap.Continuum.SU2MultiLinkHaarFactorization

namespace YMGap.Continuum.SU2HaarDisjointSupport

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (monoMul PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2MultiLinkHaarFactorization

local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩

/-- Block `k` of `m` is free (all four exponents zero). -/
def BlockFree (m : List Nat) (k : Nat) : Prop := ∀ c, c < 4 → exponentAt m (4 * k + c) = 0

theorem emul (m1 m2 : List Nat) (i : Nat) :
    exponentAt (monoMul m1 m2) i = exponentAt m1 i + exponentAt m2 i :=
  YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal.exponentAt_monoMul m1 m2 i

theorem sm4_zero : (sphereMoment4 0 0 0 0).eqv 1 := by
  have h := quaternionHaarMono_one 1
  unfold quaternionHaarMono quaternionHaarPrefix at h
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_one_eqv _)) h

theorem free0 {m : List Nat} (h : BlockFree m 0) (c : Nat) (hc : c < 4) : exponentAt m c = 0 := by
  have := h c hc; rw [Nat.mul_zero, Nat.zero_add] at this; exact this

theorem drop_mul (m1 m2 : List Nat) :
    ∀ n, quaternionHaarPrefix n ((monoMul m1 m2).drop 4) =
      quaternionHaarPrefix n (monoMul (m1.drop 4) (m2.drop 4)) := fun n =>
  prefix_congr n _ _ (fun i _ => by rw [exponentAt_drop, emul, emul, exponentAt_drop, exponentAt_drop])

/-- Free block 0 in `m₁`: the first sphere moment of the product is `m₂`'s. -/
theorem sm4_left {m1 m2 : List Nat} (h : BlockFree m1 0) :
    sphereMoment4 (exponentAt (monoMul m1 m2) 0) (exponentAt (monoMul m1 m2) 1)
      (exponentAt (monoMul m1 m2) 2) (exponentAt (monoMul m1 m2) 3) =
    sphereMoment4 (exponentAt m2 0) (exponentAt m2 1) (exponentAt m2 2) (exponentAt m2 3) := by
  rw [emul, emul, emul, emul, free0 h 0 (by decide), free0 h 1 (by decide), free0 h 2 (by decide),
    free0 h 3 (by decide), Nat.zero_add, Nat.zero_add, Nat.zero_add, Nat.zero_add]

theorem sm4_right {m1 m2 : List Nat} (h : BlockFree m2 0) :
    sphereMoment4 (exponentAt (monoMul m1 m2) 0) (exponentAt (monoMul m1 m2) 1)
      (exponentAt (monoMul m1 m2) 2) (exponentAt (monoMul m1 m2) 3) =
    sphereMoment4 (exponentAt m1 0) (exponentAt m1 1) (exponentAt m1 2) (exponentAt m1 3) := by
  rw [emul, emul, emul, emul, free0 h 0 (by decide), free0 h 1 (by decide), free0 h 2 (by decide),
    free0 h 3 (by decide), Nat.add_zero, Nat.add_zero, Nat.add_zero, Nat.add_zero]

theorem sm4_one {m : List Nat} (h : BlockFree m 0) :
    (sphereMoment4 (exponentAt m 0) (exponentAt m 1) (exponentAt m 2) (exponentAt m 3)).eqv 1 := by
  rw [free0 h 0 (by decide), free0 h 1 (by decide), free0 h 2 (by decide), free0 h 3 (by decide)]
  exact sm4_zero

theorem free_drop {m : List Nat} {k : Nat} (h : BlockFree m (k + 1)) : BlockFree (m.drop 4) k :=
  fun c hc => by
    rw [exponentAt_drop]
    have e : 4 + (4 * k + c) = 4 * (k + 1) + c := by omega
    rw [e]; exact h c hc

/-- **Prefix factorization over disjoint blocks (PROVED).** -/
theorem prefix_disj : ∀ (n : Nat) (m1 m2 : List Nat),
    (∀ k, k < n → BlockFree m1 k ∨ BlockFree m2 k) →
    (quaternionHaarPrefix n (monoMul m1 m2)).eqv (quaternionHaarPrefix n m1 * quaternionHaarPrefix n m2)
  | 0, _, _, _ => Q'.eqv_symm (Q'.one_mul_eqv _)
  | n + 1, m1, m2, h => by
    have ih := prefix_disj n (m1.drop 4) (m2.drop 4) (fun k hk =>
      (h (k + 1) (Nat.succ_lt_succ hk)).elim (fun a => Or.inl (free_drop a)) (fun b => Or.inr (free_drop b)))
    unfold quaternionHaarPrefix
    rw [drop_mul m1 m2 n]
    let P1 := quaternionHaarPrefix n (m1.drop 4)
    let P2 := quaternionHaarPrefix n (m2.drop 4)
    let V := PolyExpr.var
    rcases h 0 (Nat.succ_pos n) with h0 | h0
    · rw [sm4_left h0]
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ ih) ?_
      refine Q'.eqv_trans _ _ _ ?_ (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (sm4_one h0))))
      exact poly_identity_of_normal_eq (V 0 * (V 1 * V 2)) ((PolyExpr.const 1 * V 1) * (V 0 * V 2))
        (by decide)
        (fun | 0 => sphereMoment4 (exponentAt m2 0) (exponentAt m2 1) (exponentAt m2 2)
                  (exponentAt m2 3) | 1 => P1 | _ => P2)
    · rw [sm4_right h0]
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ ih) ?_
      refine Q'.eqv_trans _ _ _ ?_ (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (sm4_one h0))))
      exact poly_identity_of_normal_eq (V 0 * (V 1 * V 2)) ((V 0 * V 1) * (PolyExpr.const 1 * V 2))
        (by decide)
        (fun | 0 => sphereMoment4 (exponentAt m1 0) (exponentAt m1 1) (exponentAt m1 2)
                  (exponentAt m1 3) | 1 => P1 | _ => P2)

theorem az_mul (m1 m2 : List Nat) (k : Nat) :
    allZero ((monoMul m1 m2).drop k) = (allZero (m1.drop k) && allZero (m2.drop k)) := by
  apply Bool.eq_iff_iff.mpr
  rw [Bool.and_eq_true, allZero_iff, allZero_iff, allZero_iff]
  constructor
  · intro h
    exact ⟨fun i => by have := h i; rw [exponentAt_drop, emul] at this; rw [exponentAt_drop]; omega,
      fun i => by have := h i; rw [exponentAt_drop, emul] at this; rw [exponentAt_drop]; omega⟩
  · intro h i
    have h1 := h.1 i; have h2 := h.2 i
    rw [exponentAt_drop] at h1 h2; rw [exponentAt_drop, emul]; omega

/-- **Monomial factorization over disjoint blocks (PROVED).** -/
theorem mono_disj (n : Nat) (m1 m2 : List Nat) (h : ∀ k, k < n → BlockFree m1 k ∨ BlockFree m2 k) :
    (quaternionHaarMono n (monoMul m1 m2)).eqv (quaternionHaarMono n m1 * quaternionHaarMono n m2) := by
  unfold quaternionHaarMono
  rw [az_mul]
  cases h1 : allZero (m1.drop (4 * n)) <;> cases h2 : allZero (m2.drop (4 * n))
  · exact Q'.eqv_symm (Q'.zero_mul_eqv _)
  · exact Q'.eqv_symm (Q'.zero_mul_eqv _)
  · exact Q'.eqv_symm (Q'.mul_zero_eqv _)
  · exact prefix_disj n m1 m2 h

/-- `p` has every monomial free on blocks outside `A`; `q` free on blocks in `A`. -/
def FreeOff (A : Nat → Bool) (b : Bool) (p : RatPoly) : Prop :=
  ∀ s, s ∈ p → ∀ k, A k = b → BlockFree s.1 k

theorem haar_row (n : Nat) (A : Nat → Bool) (s : RatTerm) (hs : ∀ k, A k = false → BlockFree s.1 k) :
    ∀ q : RatPoly, FreeOff A true q →
      (quaternionHaar n (q.map fun t => (monoMul s.1 t.1, s.2 * t.2))).eqv
        ((s.2 * quaternionHaarMono n s.1) * quaternionHaar n q)
  | [], _ => Q'.eqv_symm (Q'.mul_zero_eqv _)
  | t :: q, hq => by
    have ih := haar_row n A s hs q (fun s' h => hq s' (List.mem_cons_of_mem _ h))
    have hm := mono_disj n s.1 t.1 (fun k _ => by
      cases hk : A k
      · exact Or.inl (hs k hk)
      · exact Or.inr (hq t List.mem_cons_self k hk))
    show ((s.2 * t.2) * quaternionHaarMono n (monoMul s.1 t.1) + _).eqv
      ((s.2 * quaternionHaarMono n s.1) * (t.2 * quaternionHaarMono n t.1 + quaternionHaar n q))
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ hm) ih) ?_
    refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (Q'.mul_add_eqv _ _ _))
    exact Q'.add_eqv_congr' (YMGap.Continuum.RingNormaliser.q_mul4_swap _ _ _ _) (Q'.eqv_refl _)

/-- **Haar factorization over disjoint block supports (PROVED).** -/
theorem haar_disj (n : Nat) (A : Nat → Bool) :
    ∀ p : RatPoly, FreeOff A false p → ∀ q : RatPoly, FreeOff A true q →
      (quaternionHaar n (polyMul p q)).eqv (quaternionHaar n p * quaternionHaar n q)
  | [], _, q, _ => Q'.eqv_symm (Q'.zero_mul_eqv _)
  | s :: p, hp, q, hq => by
    show (quaternionHaar n ((q.map fun t => (monoMul s.1 t.1, s.2 * t.2)) ++ polyMul p q)).eqv
      ((s.2 * quaternionHaarMono n s.1 + quaternionHaar n p) * quaternionHaar n q)
    refine Q'.eqv_trans _ _ _ (YMGap.Continuum.BF4CompactActionCPOrder.quaternionHaar_append _ _ _) ?_
    refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (Q'.add_mul_eqv _ _ _))
    exact Q'.add_eqv_congr' (haar_row n A s (hp s List.mem_cons_self) q hq)
      (haar_disj n A p (fun s' h => hp s' (List.mem_cons_of_mem _ h)) q hq)

end YMGap.Continuum.SU2HaarDisjointSupport
