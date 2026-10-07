/-
# Transfer-free gap bound: log-convexity plus clustering (rational, cross-multiplied)

ADDITIVE.  **Labels:** abstract rational arithmetic.  In the intended use: strong coupling, fixed K,
also true for U(1), not gap evidence.

Let `G : Nat → Q'` be positive on `0..L` and log-convex there, in the cross-multiplied form
`G(j+1)² ≤ G(j)·G(j+2)` for `j+2 ≤ L`.  In the intended use, this is the RP Cauchy–Schwarz inequality
for the truncated correlator across the reflection plane, with `L ≤ N_t/2`.  Proved here:

* `ratio_mono`: `G(i+1)·G(j) ≤ G(i)·G(j+1)` for `i ≤ j`, `j+1 ≤ L` (the ratios r_i do not decrease).
* `ratio_pow`: `G(k+1)^d · G(k) ≤ G(k+d) · G(k)^d` for `k+d ≤ L`, i.e. `r_k^d ≤ G(k+d)/G(k)`.
* `gap_finite`: if also `G(n) ≤ C·q^n` for `n ≤ L` (clustering), then
  `G(k+1)^d · G(k) ≤ C·q^(k+d) · G(k)^d`, i.e. `r_k ≤ q·(C q^k / G(k))^{1/d}` for `k+d ≤ L`.
  At finite volume this is NOT `r_k ≤ q`.

No real roots, logarithms or limits.  The `N_t → ∞` corollary `r_k ≤ q` is NOT proved here.
-/

import YMGap.Constructive.Sqrt
import YMGap.Constructive.Geometric

namespace YMGap.Continuum.SU2LogConvexGap

set_option autoImplicit false

open YMGap.Constructive

/-- `a ≤ b`, `b ≈ c` gives `a ≤ c`. -/
theorem le_e {a b c : Q'} (h : a ≤ b) (e : b.eqv c) : a ≤ c := Q'.le_trans' a b c h (Q'.le_of_eqv e)
/-- `a ≈ b`, `b ≤ c` gives `a ≤ c`. -/
theorem e_le {a b c : Q'} (e : a.eqv b) (h : b ≤ c) : a ≤ c := Q'.le_trans' a b c (Q'.le_of_eqv e) h

/-- `c·(a·c) ≈ a·(c·c)`. -/
theorem sw (a c : Q') : (c * (a * c)).eqv (a * (c * c)) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv c a c))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ c (Q'.mul_comm_eqv c a)) (Q'.mul_assoc_eqv a c c))

/-- `(x·y)·z ≈ y·(x·z)`. -/
theorem rot (x y z : Q') : ((x * y) * z).eqv (y * (x * z)) :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ z (Q'.mul_comm_eqv x y)) (Q'.mul_assoc_eqv y x z)

variable (G : Nat → Q') (L : Nat)

/-- Cross-multiplied log-convexity on `0..L`. -/
def LogConvex : Prop := ∀ j, j + 2 ≤ L → G (j + 1) * G (j + 1) ≤ G j * G (j + 2)

def Pos : Prop := ∀ j, j ≤ L → (0 : Q') < G j

variable {G L}

theorem nn (hp : Pos G L) {j : Nat} (h : j ≤ L) : (0 : Q') ≤ G j := Q'.le_of_lt (hp j h)

/-- **Ratios do not decrease (PROVED).** -/
theorem ratio_mono (hp : Pos G L) (hc : LogConvex G L) (i : Nat) :
    ∀ d, i + d + 1 ≤ L → G (i + 1) * G (i + d) ≤ G i * G (i + d + 1)
  | 0, _ => Q'.le_of_eqv (Q'.mul_comm_eqv _ _)
  | d + 1, h => by
    have ih := ratio_mono hp hc i d (by omega)
    have cs := hc (i + d) (by omega)
    have hcp := hp (i + d + 1) (by omega)
    apply Q'.le_of_mul_le_mul_left _ hcp
    -- c·(a·c) ≈ a·(c·c) ≤ a·(G(i+d)·G(i+d+2)) ≈ (a·G(i+d))·G(i+d+2) ≤ (G i·c)·G(i+d+2) ≈ c·(G i·G(i+d+2))
    refine e_le (sw _ _) ?_
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ cs (nn hp (by omega))) ?_
    refine e_le (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    refine le_e (Q'.mul_le_mul_of_nonneg_right _ _ _ ih (nn hp (by omega))) ?_
    exact Q'.eqv_trans _ _ _ (rot _ _ _) (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_refl _))

/-- **Power form (PROVED).**  `G(k+1)^d · G(k) ≤ G(k+d) · G(k)^d`. -/
theorem ratio_pow (hp : Pos G L) (hc : LogConvex G L) (k : Nat) :
    ∀ d, k + d ≤ L → G (k + 1) ^ d * G k ≤ G (k + d) * G k ^ d
  | 0, _ => e_le (Q'.one_mul_eqv _) (Q'.ge_of_eqv (Q'.mul_one_eqv _))
  | d + 1, h => by
    have ih := ratio_pow hp hc k d (by omega)
    have hm := ratio_mono hp hc k d (by omega)
    show G (k + 1) * G (k + 1) ^ d * G k ≤ G (k + d + 1) * (G k * G k ^ d)
    refine e_le (Q'.mul_assoc_eqv _ _ _) ?_
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ ih (nn hp (by omega))) ?_
    refine e_le (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    refine le_e (Q'.mul_le_mul_of_nonneg_right _ _ _ hm
      (Q'.pow_nonneg _ (nn hp (by omega)) d)) ?_
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) (Q'.mul_assoc_eqv _ _ _)

/-- **Finite-volume gap bound (PROVED).**  Under log-convexity and clustering `G n ≤ C q^n` on `0..L`:
`G(k+1)^d · G(k) ≤ C·q^(k+d) · G(k)^d` for `k+d ≤ L`. -/
theorem gap_finite (hp : Pos G L) (hc : LogConvex G L) {C q : Q'}
    (hcl : ∀ n, n ≤ L → G n ≤ C * q ^ n) (k d : Nat) (h : k + d ≤ L) :
    G (k + 1) ^ d * G k ≤ C * q ^ (k + d) * G k ^ d :=
  Q'.le_trans' _ _ _ (ratio_pow hp hc k d h)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (hcl (k + d) h) (Q'.pow_nonneg _ (nn hp (by omega)) d))

end YMGap.Continuum.SU2LogConvexGap
