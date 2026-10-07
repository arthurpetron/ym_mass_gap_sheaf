/-
# LogConvex route: the zero case (G ≥ 0 instead of G > 0)

ADDITIVE.  **Labels:** abstract rational arithmetic.  In the intended use: strong coupling, fixed K,
also true for U(1), not gap evidence.

Under `G ≥ 0` on `0..L` and `LogConvex G L` (`G(j+1)² ≤ G(j)·G(j+2)`), zeros propagate:

* `zero_fwd`: `G m ≈ 0`, `m+2 ≤ L` gives `G (m+1) ≈ 0`.
* `zero_bwd`: `G (m+1) ≈ 0`, `1 ≤ m`, `m+2 ≤ L` gives `G m ≈ 0`.
* `zero_all`: a zero at any index `m ≤ L−1` forces `G ≈ 0` on all of `1..L−1`.
  `G 0` and `G L` stay unconstrained.

* **`gap_nonneg`**: the conclusion of `gap_finite` with `Pos` replaced by `G ≥ 0`, `0 ≤ C`, `0 ≤ q`:
  `G(k+1)^d · G(k) ≤ C·q^(k+d) · G(k)^d` for `k+d ≤ L`.  Either `G > 0` on `1..L−1` (handled by
  `ratio_mono'`, which cancels only at interior indices), or `G` vanishes there and the bound is
  trivial.  At finite volume this is NOT `r_k ≤ q`.  The Archimedean lemma in Q′ and the
  `N_t → ∞` corollary remain OPEN (not attempted).
-/

import YMGap.Continuum.SU2LogConvexGap

namespace YMGap.Continuum.SU2LogConvexZero

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2LogConvexGap (le_e e_le sw rot LogConvex)

/-! ## Zeros in Q′ -/
theorem num_zero_of_eqv {x : Q'} (h : x.eqv 0) : x.num = 0 := by
  have h' : x.num * ((0 : Q').den : Int) = (0 : Q').num * (x.den : Int) := h
  have e1 : ((0 : Q').den : Int) = 1 := rfl
  have e2 : (0 : Q').num = 0 := rfl
  rw [e1, e2, Int.mul_one, Int.zero_mul] at h'
  exact h'
theorem eqv_zero_of_num {x : Q'} (h : x.num = 0) : x.eqv 0 := by
  show x.num * ((0 : Q').den : Int) = (0 : Q').num * (x.den : Int)
  rw [h, show (0 : Q').num = 0 from rfl, Int.zero_mul, Int.zero_mul]
theorem int_sq_nonneg (a : Int) : 0 ≤ a * a := by
  rcases Int.le_total 0 a with h | h
  · exact Int.mul_nonneg h h
  · rw [← Int.neg_mul_neg]; exact Int.mul_nonneg (Int.neg_nonneg_of_nonpos h) (Int.neg_nonneg_of_nonpos h)
theorem sq_nonpos {x : Q'} (h : x * x ≤ 0) : x.eqv 0 := by
  have h' : (x * x).num * ((0 : Q').den : Int) ≤ (0 : Q').num * ((x * x).den : Int) := h
  have e1 : ((0 : Q').den : Int) = 1 := rfl
  have e2 : (0 : Q').num = 0 := rfl
  have e3 : (x * x).num = x.num * x.num := rfl
  rw [e1, e2, e3, Int.mul_one, Int.zero_mul] at h'
  exact eqv_zero_of_num ((Int.mul_eq_zero.mp (Int.le_antisymm h' (int_sq_nonneg _))).elim id id)
theorem zero_of_not_pos {x : Q'} (h0 : (0 : Q') ≤ x) (h : ¬ (0 : Q') < x) : x.eqv 0 := by
  have a : (0 : Q').num * (x.den : Int) ≤ x.num * ((0 : Q').den : Int) := h0
  have b : ¬ ((0 : Q').num * (x.den : Int) < x.num * ((0 : Q').den : Int)) := h
  have e1 : ((0 : Q').den : Int) = 1 := rfl
  have e2 : (0 : Q').num = 0 := rfl
  rw [e1, e2, Int.mul_one, Int.zero_mul] at a b
  exact eqv_zero_of_num (Int.le_antisymm (Int.not_lt.mp b) a)
theorem mul_zero_left {a : Q'} (b : Q') (h : a.eqv 0) : (a * b).eqv 0 :=
  eqv_zero_of_num (show a.num * b.num = 0 by rw [num_zero_of_eqv h, Int.zero_mul])
theorem mul_zero_right (a : Q') {b : Q'} (h : b.eqv 0) : (a * b).eqv 0 :=
  eqv_zero_of_num (show a.num * b.num = 0 by rw [num_zero_of_eqv h, Int.mul_zero])

/-! ## Zero propagation -/

variable {G : Nat → Q'} {L : Nat}

def Nonneg (G : Nat → Q') (L : Nat) : Prop := ∀ j, j ≤ L → (0 : Q') ≤ G j

theorem zero_fwd (hc : LogConvex G L) {m : Nat} (hm : (G m).eqv 0) (h : m + 2 ≤ L) : (G (m + 1)).eqv 0 :=
  sq_nonpos (le_e (hc m h) (mul_zero_left _ hm))

theorem zero_bwd (hc : LogConvex G L) {m : Nat} (hm : (G (m + 1)).eqv 0) (h1 : 1 ≤ m) (h : m + 2 ≤ L) :
    (G m).eqv 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  exact sq_nonpos (le_e (hc j (by omega)) (mul_zero_right _ hm))

theorem zero_up (hc : LogConvex G L) {m : Nat} (hm : (G m).eqv 0) :
    ∀ e, m + e + 1 ≤ L → (G (m + e)).eqv 0
  | 0, _ => hm
  | e + 1, h => zero_fwd hc (zero_up hc hm e (by omega)) (by omega)

theorem zero_down (hc : LogConvex G L) {m : Nat} (hm : (G m).eqv 0) (hL : m + 1 ≤ L) :
    ∀ e, 1 ≤ m - e → (G (m - e)).eqv 0
  | 0, _ => hm
  | e + 1, h => by
    have ih := zero_down hc hm hL e (by omega)
    have e1 : m - e = (m - (e + 1)) + 1 := by omega
    rw [e1] at ih
    exact zero_bwd hc ih (by omega) (by omega)

/-- **Interior zeros spread (PROVED).** -/
theorem zero_all (hc : LogConvex G L) {m : Nat} (hm : (G m).eqv 0) (hL : m + 1 ≤ L) :
    ∀ j, 1 ≤ j → j + 1 ≤ L → (G j).eqv 0 := fun j hj hjL => by
  by_cases hjm : m ≤ j
  · have := zero_up hc hm (j - m) (by omega)
    rwa [show m + (j - m) = j by omega] at this
  · have := zero_down hc hm hL (m - j) (by omega)
    rwa [show m - (m - j) = j by omega] at this

/-! ## Interior positivity suffices for the ratio bounds -/

def PosI (G : Nat → Q') (L : Nat) : Prop := ∀ j, 1 ≤ j → j + 1 ≤ L → (0 : Q') < G j

theorem ratio_mono' (hn : Nonneg G L) (hp : PosI G L) (hc : LogConvex G L) (i : Nat) :
    ∀ d, i + d + 1 ≤ L → G (i + 1) * G (i + d) ≤ G i * G (i + d + 1)
  | 0, _ => Q'.le_of_eqv (Q'.mul_comm_eqv _ _)
  | d + 1, h => by
    have ih := ratio_mono' hn hp hc i d (by omega)
    have cs := hc (i + d) (by omega)
    have hcp := hp (i + d + 1) (by omega) (by omega)
    apply Q'.le_of_mul_le_mul_left _ hcp
    refine e_le (sw _ _) ?_
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ cs (hn _ (by omega))) ?_
    refine e_le (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    refine le_e (Q'.mul_le_mul_of_nonneg_right _ _ _ ih (hn _ (by omega))) ?_
    exact Q'.eqv_trans _ _ _ (rot _ _ _) (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_refl _))

theorem ratio_pow' (hn : Nonneg G L) (hp : PosI G L) (hc : LogConvex G L) (k : Nat) :
    ∀ d, k + d ≤ L → G (k + 1) ^ d * G k ≤ G (k + d) * G k ^ d
  | 0, _ => e_le (Q'.one_mul_eqv _) (Q'.ge_of_eqv (Q'.mul_one_eqv _))
  | d + 1, h => by
    have ih := ratio_pow' hn hp hc k d (by omega)
    have hm := ratio_mono' hn hp hc k d (by omega)
    show G (k + 1) * G (k + 1) ^ d * G k ≤ G (k + d + 1) * (G k * G k ^ d)
    refine e_le (Q'.mul_assoc_eqv _ _ _) ?_
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ ih (hn _ (by omega))) ?_
    refine e_le (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    refine le_e (Q'.mul_le_mul_of_nonneg_right _ _ _ hm (Q'.pow_nonneg _ (hn _ (by omega)) d)) ?_
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) (Q'.mul_assoc_eqv _ _ _)

/-- Either `G > 0` on the interior below `n`, or some interior index below `n` is not positive. -/
theorem split (G : Nat → Q') : ∀ n : Nat,
    (∀ j, 1 ≤ j → j < n → (0 : Q') < G j) ∨ ∃ j, 1 ≤ j ∧ j < n ∧ ¬ (0 : Q') < G j
  | 0 => Or.inl fun _ _ h => absurd h (Nat.not_lt_zero _)
  | n + 1 => by
    rcases split G n with h | ⟨j, h1, h2, h3⟩
    · by_cases hn : 1 ≤ n
      · by_cases hp : (0 : Q') < G n
        · exact Or.inl fun j h1 h2 => by
            by_cases e : j = n
            · exact e ▸ hp
            · exact h j h1 (by omega)
        · exact Or.inr ⟨n, hn, by omega, hp⟩
      · exact Or.inl fun j h1 h2 => h j h1 (by omega)
    · exact Or.inr ⟨j, h1, by omega, h3⟩

theorem zero_le_of_eqv {x y : Q'} (h : x.eqv 0) (hy : (0 : Q') ≤ y) : x ≤ y :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv h) hy

/-- **Finite-volume ratio bound under `G ≥ 0` (PROVED).** -/
theorem gap_nonneg (hn : Nonneg G L) (hc : LogConvex G L) {C q : Q'} (hC : (0 : Q') ≤ C) (hq : (0 : Q') ≤ q)
    (hcl : ∀ n, n ≤ L → G n ≤ C * q ^ n) (k d : Nat) (h : k + d ≤ L) :
    G (k + 1) ^ d * G k ≤ C * q ^ (k + d) * G k ^ d := by
  rcases split G L with hp | ⟨m, h1, h2, h3⟩
  · have hp' : PosI G L := fun j h1 h2 => hp j h1 (by omega)
    exact Q'.le_trans' _ _ _ (ratio_pow' hn hp' hc k d h)
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (hcl (k + d) h) (Q'.pow_nonneg _ (hn k (by omega)) d))
  · have hz := zero_all hc (zero_of_not_pos (hn m (by omega)) h3) (by omega)
    have hR : (0 : Q') ≤ C * q ^ (k + d) * G k ^ d :=
      Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hC (Q'.pow_nonneg _ hq _)) (Q'.pow_nonneg _ (hn k (by omega)) d)
    cases d with
    | zero =>
      exact e_le (Q'.one_mul_eqv _) (le_e (hcl k (by omega)) (Q'.eqv_symm (Q'.mul_one_eqv _)))
    | succ d =>
      by_cases hk : k + 2 ≤ L
      · exact zero_le_of_eqv (mul_zero_left _ (mul_zero_left _ (hz (k + 1) (by omega) (by omega)))) hR
      · exact zero_le_of_eqv (mul_zero_right _ (hz k (by omega) (by omega))) hR

end YMGap.Continuum.SU2LogConvexZero
