/-
# DOB-NEU: weighted powers of a nonnegative matrix (Dobrushin–Neumann, combinatorial half)

**Label: finite-index combinatorial scaffolding; also true for U(1); not gap evidence. No chart-closure claim.**
Additive. Constructive: rational inequalities and finite sums only. No `Classical`, no `sorry`.

This is the combinatorial half of Theorem 3.1 of `steps01_uniform.md`, in weighted form. Consumers:
`hDob_OPEN` / `hDobW1_OPEN`. The Föllmer covariance estimate stays OPEN.

## Setup
A nonnegative matrix `C` on a finite index set `{0,…,n−1}`, an ℕ-valued metric `d`
(`d i i = 0`, triangle), and an expansion factor `ρ ≥ 1` (the form with `r ∈ (0,1]` in the
scope note is recovered by `ρ = 1/r`; we use only nonnegative powers of `ρ`). The row-sum
bound is `∀ i < n, Σ_{l<n} C_il · ρ^{d i l} ≤ α` with `α ≥ 0`.

## Recursion and the `tpow` mismatch (flagged, not weakened)
`FiniteTransferTrace.tpow` is left-multiplication starting at `T` itself:
`tpow 0 = T` and `tpow (k+1) = mmul T (tpow k)`, so `tpow k = T^{k+1}`. The bound
`(tpow n C k i j) * ρ^{d i j} ≤ α^k` is therefore **false** at `k = 0` in general:
it would require `C_ij · ρ^{d i j} ≤ 1`, which does not follow from the row-sum bound
(a single entry may be as large as `α`). The `k = 0` case of `C^k` is the identity,
which needs `d i i = 0` and `I_ij = 0` for `i ≠ j`.

The honest restatement uses `cpow`, the same left-multiplication recursion starting at
the identity (`cpow 0 = I`, `cpow (k+1) = mmul C (cpow k)`). Then
`cpow (k+1) = tpow k`, and:
* `cpow_weighted`: `(cpow n C k i j) * ρ^{d i j} ≤ α^k` for `i, j < n`;
* `tpow_weighted`: `(tpow n C k i j) * ρ^{d i j} ≤ α^{k+1}` (the corrected `tpow` form);
* `cpow_resolvent`: for `α < 1`, `(Σ_{k<K} cpow n C k i j) * ρ^{d i j} ≤ 1/(1−α)`.

Because `tpow` starts at `C`, the corresponding sum over `tpow` would be
`Σ_{k<K} tpow k * ρ^{d} ≤ Σ_{m=1}^{K} α^m ≤ α/(1−α)`, a different true bound; the
stated `1/(1−α)` is the sum including the identity, and is proved for `cpow`.

The hypothesis is the **row** form, matching left-multiplication. (The column form would
match `tpow (k+1) = mmul (tpow k) C`, which is not the definition in `FiniteTransferTrace`.)
-/

import YMGap.Continuum.FiniteTransferTrace
import YMGap.Constructive.Geometric
import YMGap.Constructive.Reals
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.DobrushinNeumann

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail (finSum finSum_mul_const const_mul_finSum)
open YMGap.Continuum.FiniteTransferTrace
  (Mat mmul tpow finSum_nonneg finSum_congr)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

/-! ## Local arithmetic -/

theorem finSum_le (f g : Nat → Q') :
    ∀ n, (∀ i, i < n → f i ≤ g i) → finSum f n ≤ finSum g n
  | 0, _ => Q'.le_refl' _
  | n + 1, h =>
      Q'.le_trans' _ _ _
        (Q'.add_le_add_right _ _ _ (finSum_le f g n fun i hi => h i (Nat.lt_succ_of_lt hi)))
        (Q'.add_le_add_left _ _ _ (h n (Nat.lt_succ_self n)))

theorem pow_add (q : Q') : ∀ (a b : Nat), (q ^ (a + b)).eqv (q ^ a * q ^ b)
  | a, 0 => Q'.eqv_symm (Q'.mul_one_eqv (q ^ a))
  | a, b + 1 => by
      have hsucc : a + (b + 1) = (a + b) + 1 := Nat.add_succ a b
      rw [hsucc, Q'.pow_succ, Q'.pow_succ]
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left q _ _ (pow_add q a b)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv q (q ^ a) (q ^ b))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (q ^ b) (Q'.mul_comm_eqv q (q ^ a))) ?_
      exact Q'.mul_assoc_eqv (q ^ a) q (q ^ b)

theorem one_le_pow {ρ : Q'} (hρ : (1 : Q') ≤ ρ) : ∀ n : Nat, (1 : Q') ≤ ρ ^ n
  | 0 => Q'.le_refl' _
  | n + 1 => by
      have hρ0 : (0 : Q') ≤ ρ := Q'.le_trans' _ _ _ (by decide) hρ
      have h1 : ((1 : Q') * 1).eqv (1 : Q') := Q'.mul_one_eqv 1
      have h2 : (ρ * ρ ^ n).eqv (ρ ^ (n + 1)) := by rw [Q'.pow_succ]; exact Q'.eqv_refl _
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm h1)) ?_
      refine Q'.le_trans' _ _ _ ?_ (Q'.le_of_eqv h2)
      exact Q'.mul_le_mul_of_nonneg (by exact hρ) (one_le_pow hρ n) hρ0 (by decide)

theorem pow_mono_exp {ρ : Q'} (hρ : (1 : Q') ≤ ρ) {a b : Nat} (hab : a ≤ b) :
    ρ ^ a ≤ ρ ^ b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  have hρ0 : (0 : Q') ≤ ρ := Q'.le_trans' _ _ _ (by decide) hρ
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv (ρ ^ a)))) ?_
  refine Q'.le_trans' _ _ _ ?_ (Q'.le_of_eqv (Q'.eqv_symm (pow_add ρ a d)))
  exact Q'.mul_le_mul_of_nonneg_left _ _ _ (one_le_pow hρ d) (Q'.pow_nonneg ρ hρ0 a)

theorem one_sub_pos {α : Q'} (h : α < (1 : Q')) : (0 : Q') < (1 : Q') + -α := by
  show (0 : Int) * (((1 : Q') + -α).den : Int) < ((1 : Q') + -α).num * ((0 : Q').den : Int)
  have hnum : ((1 : Q') + -α).num =
      (1 : Q').num * ((-α).den : Int) + (-α).num * ((1 : Q').den : Int) := rfl
  have hz : ((0 : Q').den : Int) = (1 : Int) := rfl
  rw [Int.zero_mul, hz, Int.mul_one, hnum]
  have hα : α.num * ((1 : Q').den : Int) < (1 : Q').num * (α.den : Int) := h
  have h1n : (1 : Q').num = (1 : Int) := rfl
  have h1d : ((1 : Q').den : Int) = (1 : Int) := rfl
  have hnd : ((-α).den : Int) = (α.den : Int) := rfl
  have hnn : (-α).num = -α.num := rfl
  rw [h1n, h1d, Int.mul_one, Int.one_mul] at hα
  rw [h1n, h1d, hnd, hnn, Int.one_mul, Int.mul_one]
  exact Int.sub_pos_of_lt hα

theorem pow_le_one {α : Q'} (hα : (0 : Q') ≤ α) (hα1 : α ≤ 1) :
    ∀ k : Nat, α ^ k ≤ (1 : Q')
  | 0 => Q'.le_refl' _
  | k + 1 =>
      Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hα1 (Q'.pow_nonneg α hα k))
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv (α ^ k))) (pow_le_one hα hα1 k))

theorem geom_mul (α : Q') :
    ∀ K, (((1 : Q') + -α) * finSum (fun k => α ^ k) K).eqv ((1 : Q') + -(α ^ K))
  | 0 => by
      show (((1 : Q') + -α) * (0 : Q')).eqv ((1 : Q') + -(1 : Q'))
      refine Q'.eqv_trans _ _ _ (Q'.mul_zero_eqv _) (Q'.eqv_symm (Q'.add_neg_self_eqv (1 : Q')))
  | K + 1 => by
      let β : Q' := (1 : Q') + -α
      let s := finSum (fun k => α ^ k) K
      have hsplit : (β * (s + α ^ K)).eqv (β * s + β * (α ^ K)) := Q'.mul_add_eqv β s (α ^ K)
      have hterm : (β * (α ^ K)).eqv (α ^ K + -(α ^ (K + 1))) := by
        have e1 : (β * (α ^ K)).eqv (((1 : Q') * (α ^ K)) + ((-α) * (α ^ K))) :=
          Q'.add_mul_eqv (1 : Q') (-α) (α ^ K)
        have e2 : ((1 : Q') * (α ^ K)).eqv (α ^ K) := Q'.one_mul_eqv (α ^ K)
        have e3 : ((-α) * (α ^ K)).eqv (-(α * (α ^ K))) := Q'.neg_mul_eqv α (α ^ K)
        have e4 : (α * (α ^ K)).eqv (α ^ (K + 1)) := by
          rw [Q'.pow_succ]; exact Q'.eqv_refl _
        exact Q'.eqv_trans _ _ _ e1
          (Q'.add_eqv_congr' e2 (Q'.eqv_trans _ _ _ e3 (Q'.neg_eqv_congr _ _ e4)))
      refine Q'.eqv_trans _ _ _ hsplit
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (geom_mul α K) hterm) ?_)
      exact poly_identity_of_normal_eq
        (.add (.add (.const 1) (.neg (.var 0))) (.add (.var 0) (.neg (.var 1))))
        (.add (.const 1) (.neg (.var 1))) (by decide)
        (fun | 0 => α ^ K | _ => α ^ (K + 1))

theorem one_sub_pow_le_one {α : Q'} (hα : (0 : Q') ≤ α) (K : Nat) :
    (1 : Q') + -(α ^ K) ≤ 1 := by
  have hnn : (0 : Q') ≤ α ^ K := Q'.pow_nonneg α hα K
  refine Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hnn) (Q'.le_of_eqv ?_)
  exact Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv (1 : Q') (-(α ^ K)) (α ^ K))
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (1 : Q') _ _ (Q'.neg_add_self_eqv (α ^ K)))
      (by rw [Q'.add_zero']; exact Q'.eqv_refl _))

theorem geom_le {α : Q'} (hα : (0 : Q') ≤ α) (hα1 : α < (1 : Q')) (K : Nat) :
    finSum (fun k => α ^ k) K ≤ Q'.recipPos ((1 : Q') + -α) (one_sub_pos hα1) := by
  let β : Q' := (1 : Q') + -α
  let s := finSum (fun k => α ^ k) K
  let r := Q'.recipPos β (one_sub_pos hα1)
  have hr0 : (0 : Q') ≤ r := Q'.le_of_lt (Q'.recipPos_pos β (one_sub_pos hα1))
  have hs : s ≈ s * (β * r) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_one_eqv s))
      (Q'.mul_eqv_congr_left s _ _ (Q'.eqv_symm (Q'.mul_recipPos_eqv β (one_sub_pos hα1))))
  have hs' : (s * (β * r)).eqv ((s * β) * r) := Q'.eqv_symm (Q'.mul_assoc_eqv s β r)
  have hsβ : (s * β).eqv ((1 : Q') + -(α ^ K)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv s β) (geom_mul α K)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hs)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hs')
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ r hsβ)) ?_))
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (one_sub_pow_le_one hα K) hr0)
    (Q'.le_of_eqv (Q'.one_mul_eqv r))

/-! ## Identity-started powers (`cpow`) and the link to `tpow` -/

/-- The identity matrix: `1` on the diagonal, `0` off it. -/
def ident : Mat := fun i j => if i = j then (1 : Q') else 0

theorem ident_diag (i : Nat) : ident i i = 1 := if_pos rfl

theorem ident_off {i j : Nat} (h : i ≠ j) : ident i j = 0 := if_neg h

/-- `C^k` with `C^0 = I` and `C^{k+1} = C · C^k` (left multiplication, as in `tpow`). -/
def cpow (n : Nat) (C : Mat) : Nat → Mat
  | 0 => ident
  | k + 1 => mmul n C (cpow n C k)

theorem cpow_zero (n : Nat) (C : Mat) : cpow n C 0 = ident := rfl

theorem cpow_succ (n : Nat) (C : Mat) (k : Nat) : cpow n C (k + 1) = mmul n C (cpow n C k) := rfl

/-- Pointwise `eqv` on the range of a finite sum. -/
theorem finSum_congr_on {f g : Nat → Q'} :
    ∀ n, (∀ i, i < n → f i ≈ g i) → finSum f n ≈ finSum g n
  | 0, _ => Q'.eqv_refl _
  | n + 1, h =>
      Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (finSum_congr_on n fun i hi => h i (Nat.lt_succ_of_lt hi)))
        (Q'.add_eqv_congr_left _ _ _ (h n (Nat.lt_succ_self n)))

/-- If no index `l < m` equals `j`, the pulse sum up to `m` is `0`. -/
theorem pulse_zero_of_lt (a : Q') (j : Nat) :
    ∀ m, (∀ l, l < m → l ≠ j) → finSum (fun l => if l = j then a else (0 : Q')) m = 0
  | 0, _ => rfl
  | m + 1, h => by
      have hm : m ≠ j := h m (Nat.lt_succ_self m)
      have ih := pulse_zero_of_lt a j m (fun l hl => h l (Nat.lt_succ_of_lt hl))
      show finSum (fun l => if l = j then a else (0 : Q')) m + (if m = j then a else 0) = 0
      rw [ih, if_neg hm, Q'.zero_add']

/-- The single-term sum: `Σ_{l<n} (if l = j then a else 0) ≈ a` when `j < n`. -/
theorem finSum_pulse (a : Q') : ∀ (n j : Nat), j < n →
    (finSum (fun l => if l = j then a else (0 : Q')) n).eqv a
  | n + 1, j, hj => by
      have hle : j ≤ n := Nat.lt_succ_iff.mp hj
      show (finSum (fun l => if l = j then a else (0 : Q')) n +
          (if n = j then a else 0)).eqv a
      rcases Nat.eq_or_lt_of_le hle with heq | hj'
      · have hz : finSum (fun l => if l = n then a else (0 : Q')) n = 0 := by
          have : j = n := heq
          rw [← this]
          exact pulse_zero_of_lt a j j (fun l hl => Nat.ne_of_lt hl)
        rw [heq, hz, if_pos rfl, Q'.zero_add']
        exact Q'.eqv_refl _
      · have ih := finSum_pulse a n j hj'
        have hne : n ≠ j := (Nat.ne_of_lt hj').symm
        rw [if_neg hne, Q'.add_zero']
        exact ih

/-- Right identity: `(C · I)_{ij} ≈ C_{ij}` for `j < n`. -/
theorem mmul_ident_right (n : Nat) (C : Mat) {i j : Nat} (hj : j < n) :
    mmul n C ident i j ≈ C i j := by
  have hterm : ∀ l, (C i l * ident l j).eqv (if l = j then C i j else 0) := fun l => by
    by_cases h : l = j
    · rw [h, ident_diag, if_pos rfl]; exact Q'.mul_one_eqv (C i j)
    · rw [ident_off h, if_neg h]; exact Q'.mul_zero_eqv (C i l)
  exact Q'.eqv_trans _ _ _ (finSum_congr hterm n) (finSum_pulse (C i j) n j hj)

/-- On the `n×n` block, `tpow k ≈ cpow (k+1)` (since `tpow 0 = C` and `cpow 1 = C·I`). -/
theorem tpow_eq_cpow (n : Nat) (C : Mat) {i j : Nat} (_hi : i < n) (hj : j < n) :
    ∀ k, tpow n C k i j ≈ cpow n C (k + 1) i j
  | 0 => Q'.eqv_symm (mmul_ident_right n C hj)
  | k + 1 =>
      finSum_congr_on n fun c hc =>
        Q'.mul_eqv_congr_left (C i c) _ _ (tpow_eq_cpow n C hc hj k)

variable (n : Nat) (C : Mat) (d : Nat → Nat → Nat) (ρ α : Q')
variable (hC : ∀ i j, (0 : Q') ≤ C i j)
variable (hdiag : ∀ i, d i i = 0)
variable (htri : ∀ i j l, d i j ≤ d i l + d l j)
variable (hρ : (1 : Q') ≤ ρ)
variable (hα : (0 : Q') ≤ α)
variable (hrow : ∀ i, i < n → finSum (fun l => C i l * ρ ^ (d i l)) n ≤ α)

include hC in
theorem cpow_nonneg : ∀ k i j, (0 : Q') ≤ cpow n C k i j
  | 0, i, j => by
      rw [cpow_zero]
      by_cases h : i = j
      · rw [h, ident_diag]; exact (by decide : (0 : Q') ≤ (1 : Q'))
      · rw [ident_off h]; exact Q'.le_refl' _
  | k + 1, i, j =>
      finSum_nonneg (fun c => C i c * cpow n C k c j)
        (fun c => Q'.mul_nonneg _ _ (hC i c) (cpow_nonneg k c j)) n

include hC hdiag htri hρ hα hrow in
/-- **Weighted Neumann bound, identity-started form:** `(C^k)_{ij} · ρ^{d i j} ≤ α^k`. -/
theorem cpow_weighted {i j : Nat} (hi : i < n) (hj : j < n) :
    ∀ k, cpow n C k i j * ρ ^ (d i j) ≤ α ^ k
  | 0 => by
      rw [cpow_zero]
      by_cases hij : i = j
      · rw [hij, ident_diag, hdiag j, Q'.pow_zero]
        exact Q'.le_of_eqv (Q'.one_mul_eqv (1 : Q'))
      · rw [ident_off hij]
        refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.zero_mul_eqv (ρ ^ (d i j))))
          (Q'.pow_nonneg α hα 0)
  | k + 1 => by
      let w : Nat → Q' := fun l => C i l * cpow n C k l j
      let ρij := ρ ^ (d i j)
      have hρ0 : (0 : Q') ≤ ρ := Q'.le_trans' _ _ _ (by decide) hρ
      have hρij : (0 : Q') ≤ ρij := Q'.pow_nonneg ρ hρ0 (d i j)
      have hs : (finSum w n * ρij).eqv (finSum (fun l => w l * ρij) n) := finSum_mul_const w ρij n
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hs) ?_
      -- Each summand ≤ (C_il ρ^{d i l}) · α^k, using triangle, IH, and nonnegativity.
      have hterm : ∀ l, l < n → w l * ρij ≤ (C i l * ρ ^ (d i l)) * (α ^ k) := fun l hl => by
        have hnn : (0 : Q') ≤ w l := Q'.mul_nonneg _ _ (hC i l) (cpow_nonneg n C hC k l j)
        have hρineq : ρij ≤ ρ ^ (d i l + d l j) := pow_mono_exp hρ (htri i j l)
        have h1 : w l * ρij ≤ w l * ρ ^ (d i l + d l j) :=
          Q'.mul_le_mul_of_nonneg_left _ _ _ hρineq hnn
        have h2 : (w l * ρ ^ (d i l + d l j)).eqv
            ((C i l * ρ ^ (d i l)) * (cpow n C k l j * ρ ^ (d l j))) :=
          Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (w l) _ _ (pow_add ρ (d i l) (d l j)))
            (poly_identity_of_normal_eq
              (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
              (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (by decide)
              (fun
                | 0 => C i l
                | 1 => cpow n C k l j
                | 2 => ρ ^ (d i l)
                | _ => ρ ^ (d l j)))
        have h3 : cpow n C k l j * ρ ^ (d l j) ≤ α ^ k := cpow_weighted hl hj k
        have hCρ : (0 : Q') ≤ C i l * ρ ^ (d i l) :=
          Q'.mul_nonneg _ _ (hC i l) (Q'.pow_nonneg ρ hρ0 (d i l))
        refine Q'.le_trans' _ _ _ h1
          (Q'.le_trans' _ _ _ (Q'.le_of_eqv h2)
            (Q'.mul_le_mul_of_nonneg_left _ _ _ h3 hCρ))
      refine Q'.le_trans' _ _ _ (finSum_le _ _ n hterm) ?_
      have hfactor : (finSum (fun l => (C i l * ρ ^ (d i l)) * (α ^ k)) n).eqv
          (finSum (fun l => C i l * ρ ^ (d i l)) n * (α ^ k)) :=
        Q'.eqv_symm (finSum_mul_const (fun l => C i l * ρ ^ (d i l)) (α ^ k) n)
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor) ?_
      exact Q'.mul_le_mul_of_nonneg_right _ _ _ (hrow i hi) (Q'.pow_nonneg α hα k)

include hC hdiag htri hρ hα hrow in
/-- Corrected `tpow` form: `(tpow k)_{ij} · ρ^{d i j} ≤ α^{k+1}` (since `tpow k = C^{k+1}`). -/
theorem tpow_weighted {i j : Nat} (hi : i < n) (hj : j < n) (k : Nat) :
    tpow n C k i j * ρ ^ (d i j) ≤ α ^ (k + 1) := by
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _
    (tpow_eq_cpow n C hi hj k))) ?_
  exact cpow_weighted n C d ρ α hC hdiag htri hρ hα hrow hi hj (k + 1)

include hC hdiag htri hρ hα hrow in
/-- **Resolvent bound:** for `α < 1`, `(Σ_{k<K} C^k)_{ij} · ρ^{d i j} ≤ 1/(1−α)`. -/
theorem cpow_resolvent {i j : Nat} (hi : i < n) (hj : j < n) (hα1 : α < (1 : Q')) (K : Nat) :
    finSum (fun k => cpow n C k i j) K * ρ ^ (d i j) ≤
      Q'.recipPos ((1 : Q') + -α) (one_sub_pos hα1) := by
  have hρ0 : (0 : Q') ≤ ρ := Q'.le_trans' _ _ _ (by decide) hρ
  have hρij : (0 : Q') ≤ ρ ^ (d i j) := Q'.pow_nonneg ρ hρ0 (d i j)
  have hs : (finSum (fun k => cpow n C k i j) K * ρ ^ (d i j)).eqv
      (finSum (fun k => cpow n C k i j * ρ ^ (d i j)) K) :=
    finSum_mul_const (fun k => cpow n C k i j) (ρ ^ (d i j)) K
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hs)
    (Q'.le_trans' _ _ _ (finSum_le _ _ K fun k _ =>
      cpow_weighted n C d ρ α hC hdiag htri hρ hα hrow hi hj k)
      (geom_le hα hα1 K))

end YMGap.Continuum.DobrushinNeumann

#print axioms YMGap.Continuum.DobrushinNeumann.finSum_le
#print axioms YMGap.Continuum.DobrushinNeumann.pow_add
#print axioms YMGap.Continuum.DobrushinNeumann.one_le_pow
#print axioms YMGap.Continuum.DobrushinNeumann.pow_mono_exp
#print axioms YMGap.Continuum.DobrushinNeumann.one_sub_pos
#print axioms YMGap.Continuum.DobrushinNeumann.pow_le_one
#print axioms YMGap.Continuum.DobrushinNeumann.geom_mul
#print axioms YMGap.Continuum.DobrushinNeumann.one_sub_pow_le_one
#print axioms YMGap.Continuum.DobrushinNeumann.geom_le
#print axioms YMGap.Continuum.DobrushinNeumann.ident
#print axioms YMGap.Continuum.DobrushinNeumann.ident_diag
#print axioms YMGap.Continuum.DobrushinNeumann.ident_off
#print axioms YMGap.Continuum.DobrushinNeumann.cpow
#print axioms YMGap.Continuum.DobrushinNeumann.cpow_zero
#print axioms YMGap.Continuum.DobrushinNeumann.cpow_succ
#print axioms YMGap.Continuum.DobrushinNeumann.finSum_congr_on
#print axioms YMGap.Continuum.DobrushinNeumann.pulse_zero_of_lt
#print axioms YMGap.Continuum.DobrushinNeumann.finSum_pulse
#print axioms YMGap.Continuum.DobrushinNeumann.mmul_ident_right
#print axioms YMGap.Continuum.DobrushinNeumann.tpow_eq_cpow
#print axioms YMGap.Continuum.DobrushinNeumann.cpow_nonneg
#print axioms YMGap.Continuum.DobrushinNeumann.cpow_weighted
#print axioms YMGap.Continuum.DobrushinNeumann.tpow_weighted
#print axioms YMGap.Continuum.DobrushinNeumann.cpow_resolvent
