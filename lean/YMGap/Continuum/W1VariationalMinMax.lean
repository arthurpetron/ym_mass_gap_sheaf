/-
# The easy direction of min-max for the W = 1 model, as finite algebra over Q'

ADDITIVE.  **MODEL, not the true slab.**  It closes the step that
`W1VacuumTailRowSum` cited ("λ₂ ≤ ρ by Courant–Fischer") in its variational form.
No spectral theorem is used.

Vectors are sequences `Nat → Q'` summed over `i < n+1` (arbitrary cutoff), and
`u = chi0` is the vacuum.

* `ip_chi0`: `⟨x, χ₀⟩_{n+1} ≈ x 0`.
* `perp_form_bound` (PROVED): if `x 0 = 0` (`x = kill0 v`), then
  `form_T(x) ≤ ρ ‖x‖²` with `ρ = w^{12} + κ w^{22}`, for the FULL vacuum-included operator
  `(eS w, cS κ w)` (the vacuum coupling `c 0 = κ w⁶` is present), all spins up to the cutoff.
* `twoDim_perp` (PROVED): for ANY `v1 v2`, there are `x` and coefficients `(a, b)` with
  `x ≈ a v1 + b v2` pointwise, `(a, b)` not both ≈ 0, `⟨x, χ₀⟩ ≈ 0`, and
  `form_T(x) ≤ ρ ‖x‖²`.
  - Generic case: `x = ⟨v2,χ₀⟩ v1 − ⟨v1,χ₀⟩ v2`.
  - Degenerate case (`v1 0 ≈ 0` and `v2 0 ≈ 0`, i.e. both ⊥ χ₀): `x = v1`.
* `twoDim_perp_nonzero` (PROVED): if `v1, v2` are linearly independent over the cutoff
  (`∀ a b, (∀ i ≤ n, a v1 i + b v2 i ≈ 0) → a ≈ 0 ∧ b ≈ 0`), then that `x` is not
  identically ≈ 0 on `i ≤ n`.  Nonzero-ness NEEDS this hypothesis.

The eigenvalue reading is a REMARK, not a Lean statement: for a symmetric finite section,
`λ₂ = max_{dim V = 2} min_{x ∈ V∖0} R(x)`.  Every `V` contains a nonzero `x ⊥ χ₀` with
`R(x) ≤ ρ`, so `λ₂ ≤ ρ`.

Axioms: `propext`, `Quot.sound`.
-/

import YMGap.Continuum.W1VacuumTailRowSum

namespace YMGap.Continuum.W1VariationalMinMax

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail (finSum)
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.W1VacuumTailRowSum

local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩
local instance : Neg PolyExpr := ⟨PolyExpr.neg⟩

def ip (x y : Nat → Q') (n : Nat) : Q' := finSum (fun i => x i * y i) n

def chi0 : Nat → Q'
  | 0 => 1
  | _ + 1 => 0

def kill0 (v : Nat → Q') : Nat → Q'
  | 0 => 0
  | k + 1 => v (k + 1)

theorem ip_chi0 (x : Nat → Q') : ∀ n, (ip x chi0 (n + 1)).eqv (x 0)
  | 0 => by
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq (PolyExpr.const 0 + V 0 * PolyExpr.const 1) (V 0)
      (by decide) (fun _ => x 0)
  | n + 1 => by
    let V := PolyExpr.var
    have h : (x 0 + x (n + 1) * 0).eqv (x 0) :=
      poly_identity_of_normal_eq (V 0 + V 1 * PolyExpr.const 0) (V 0)
        (by decide) (fun | 0 => x 0 | _ => x (n + 1))
    exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (ip_chi0 x n) (Q'.eqv_refl _)) h

theorem kill0_perp (v : Nat → Q') (n : Nat) : (ip (kill0 v) chi0 (n + 1)).eqv 0 :=
  ip_chi0 (kill0 v) n

theorem form_shift (e c v : Nat → Q') : ∀ n,
    (triForm e c (kill0 v) (n + 1)).eqv
      (triForm (fun i => e (i + 1)) (fun i => c (i + 1)) (fun k => v (k + 1)) n)
  | 0 => by
    let V := PolyExpr.var
    let Z := PolyExpr.const 0
    exact poly_identity_of_normal_eq (Z + V 0 * (Z * Z) + (Z * (Z * Z) + Z * (Z * Z))) Z
      (by decide) (fun _ => e 0)
  | 1 => by
    let V := PolyExpr.var
    let Z := PolyExpr.const 0
    have h : (c 0 * (0 * v 1) + c 0 * (0 * v 1)).eqv (0 * (0 * v 1) + 0 * (0 * v 1)) :=
      poly_identity_of_normal_eq (V 0 * (Z * V 1) + V 0 * (Z * V 1))
        (Z * (Z * V 1) + Z * (Z * V 1)) (by decide) (fun | 0 => c 0 | _ => v 1)
    exact Q'.add_eqv_congr' (Q'.add_eqv_congr' (form_shift e c v 0) (Q'.eqv_refl _)) h
  | k + 2 =>
    Q'.add_eqv_congr' (Q'.add_eqv_congr' (form_shift e c v (k + 1)) (Q'.eqv_refl _))
      (Q'.eqv_refl _)

theorem norm_shift (v : Nat → Q') : ∀ n,
    (finSum (fun i => kill0 v i * kill0 v i) (n + 1)).eqv
      (finSum (fun k => v (k + 1) * v (k + 1)) n)
  | 0 => by
    let Z := PolyExpr.const 0
    exact poly_identity_of_normal_eq (Z + Z * Z) Z (by decide) (fun _ => (0 : Q'))
  | n + 1 => Q'.add_eqv_congr' (norm_shift v n) (Q'.eqv_refl _)

/-- The form of the FULL vacuum-included operator on `χ₀⊥`. -/
theorem perp_form_bound (w κ : Q') (h0 : (0 : Q') ≤ w) (h1 : w ≤ 1) (hκ : (0 : Q') ≤ κ)
    (hsmall : w ^ 32 + κ * w ^ 22 ≤ w ^ 12) (v : Nat → Q') (n : Nat) :
    triForm (eS w) (cS κ w) (kill0 v) (n + 1) ≤
      (w ^ 12 + κ * w ^ 22) * finSum (fun i => kill0 v i * kill0 v i) (n + 1) := by
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (form_shift (eS w) (cS κ w) v n)) ?_
  refine Q'.le_trans' _ _ _ (excitedForm_bound w κ h0 h1 hκ hsmall (fun k => v (k + 1)) n) ?_
  exact Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (norm_shift v n)))

def comb (v1 v2 : Nat → Q') (i : Nat) : Q' := v2 0 * v1 i + -(v1 0) * v2 i

theorem kill0_comb (v1 v2 : Nat → Q') : ∀ i, (kill0 (comb v1 v2) i).eqv (comb v1 v2 i)
  | 0 => by
    let V := PolyExpr.var
    exact poly_identity_of_normal_eq (PolyExpr.const 0) (V 0 * V 1 + -V 1 * V 0)
      (by decide) (fun | 0 => v2 0 | _ => v1 0)
  | _ + 1 => Q'.eqv_refl _

theorem kill0_degen (v : Nat → Q') (hd : (v 0).eqv 0) : ∀ i, (kill0 v i).eqv (v i)
  | 0 => Q'.eqv_symm hd
  | _ + 1 => Q'.eqv_refl _

theorem lin_one (a : Q') : (a).eqv (1 * a + 0 * a) := by
  let V := PolyExpr.var
  exact poly_identity_of_normal_eq (V 0) (PolyExpr.const 1 * V 0 + PolyExpr.const 0 * V 0)
    (by decide) (fun _ => a)

/-- Variational min-max step: every pair `v1, v2` yields `x ∈ span` with `x ⊥ χ₀` and
`form(x) ≤ ρ‖x‖²`; the coefficient pair is nontrivial. -/
theorem twoDim_perp (w κ : Q') (h0 : (0 : Q') ≤ w) (h1 : w ≤ 1) (hκ : (0 : Q') ≤ κ)
    (hsmall : w ^ 32 + κ * w ^ 22 ≤ w ^ 12) (v1 v2 : Nat → Q') (n : Nat) :
    ∃ x : Nat → Q', ∃ a b : Q',
      (∀ i, (x i).eqv (a * v1 i + b * v2 i)) ∧ ¬ (a.eqv 0 ∧ b.eqv 0) ∧
      (ip x chi0 (n + 1)).eqv 0 ∧
      triForm (eS w) (cS κ w) x (n + 1) ≤
        (w ^ 12 + κ * w ^ 22) * finSum (fun i => x i * x i) (n + 1) := by
  by_cases hd : (v2 0).eqv 0 ∧ (-(v1 0)).eqv 0
  · have hv1 : (v1 0).eqv 0 :=
      Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.neg_neg_eqv (v1 0)))
        (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hd.2) (by decide))
    refine ⟨kill0 v1, 1, 0, fun i => Q'.eqv_trans _ _ _ (kill0_degen v1 hv1 i) ?_,
      fun h => absurd h.1 (by decide), kill0_perp v1 n,
      perp_form_bound w κ h0 h1 hκ hsmall v1 n⟩
    have := lin_one (v1 i)
    have h2 : (0 * v1 i).eqv (0 * v2 i) := by
      let V := PolyExpr.var
      exact poly_identity_of_normal_eq (PolyExpr.const 0 * V 0) (PolyExpr.const 0 * V 1)
        (by decide) (fun | 0 => v1 i | _ => v2 i)
    exact Q'.eqv_trans _ _ _ this (Q'.add_eqv_congr' (Q'.eqv_refl _) h2)
  · exact ⟨kill0 (comb v1 v2), v2 0, -(v1 0), kill0_comb v1 v2, hd,
      kill0_perp (comb v1 v2) n, perp_form_bound w κ h0 h1 hκ hsmall (comb v1 v2) n⟩

/-- Nonzero-ness under linear independence (over indices `i ≤ n`). -/
theorem twoDim_perp_nonzero (v1 v2 : Nat → Q') (n : Nat)
    (hli : ∀ a b : Q', (∀ i, i ≤ n → (a * v1 i + b * v2 i).eqv 0) → a.eqv 0 ∧ b.eqv 0)
    (x : Nat → Q') (a b : Q') (hx : ∀ i, (x i).eqv (a * v1 i + b * v2 i))
    (hab : ¬ (a.eqv 0 ∧ b.eqv 0)) : ¬ (∀ i, i ≤ n → (x i).eqv 0) :=
  fun hz => hab (hli a b (fun i hi => Q'.eqv_trans _ _ _ (Q'.eqv_symm (hx i)) (hz i hi)))

end YMGap.Continuum.W1VariationalMinMax

#print axioms YMGap.Continuum.W1VariationalMinMax.perp_form_bound
#print axioms YMGap.Continuum.W1VariationalMinMax.twoDim_perp
#print axioms YMGap.Continuum.W1VariationalMinMax.twoDim_perp_nonzero
