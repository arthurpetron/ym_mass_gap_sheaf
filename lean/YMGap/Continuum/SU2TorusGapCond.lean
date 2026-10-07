/-
# Conditional finite-volume ratio bound on the actual torus T_K measure (LogConvex from torus_cs_poly)

ADDITIVE.  **Labels:** STRONG COUPLING, fixed K; also true for U(1), not gap evidence.  SU(2), truncated
`T_K` weight.

Input proved by Realizer: `torus_rp_poly`, `torus_cs_poly` (`SU2TorusRPPolyCS`).  Hypotheses carried here:

* `hsup`: `PtSup (τ x)` for `x ≤ X` (time translates of the truncated observable stay on the positive half).
* `hshift`: `rpB (τ x) (τ y) ≈ G (x + y)` for `x, y ≤ X`.  This is Realizer's coming `Θ∘τ_x = τ_{−x}∘Θ` plus
  time-shift invariance of `rpB`.
* `hcl`: clustering in the same normalisation, `G n ≤ C·q^n` for `n ≤ 2X`.  The bridge from
  `SU2WilsonTrunc.wilson_trunc_ratio` (a ratio `|⟨χ_pχ_q⟩ − ⟨χ_p⟩⟨χ_q⟩| ≤ C_w λ^{d(p,q)}` in the polymer
  normalisation `ZW`) to this `rpB` form is OPEN.  It needs `ZW ≈ Haar integral`, `Z > 0`, `Θχ_p = χ_{mirror p}`,
  equal one-point means, and `d(θp, τ_n p)` in terms of `n`.

Using only the CS pairs `(τ_m, τ_{m+2})`, the even subsequence `E m := G (2m)` is log-convex.  This avoids the
odd-`j` convention.  `0 ≤ E m` follows from `torus_rp_poly`.  Proved:

* `logConvex_E`: `LogConvex E X`.
* **`torus_gap_cond`**: `E(k+1)^d · E(k) ≤ C·(q·q)^(k+d) · E(k)^d` for `k + d ≤ X`.  This is a per-two-step ratio
  bound at finite volume: NOT `r ≤ q²`.  The range `X` must keep `τ_x` on the positive half, so `X ≲ N_t/4`.
-/

import YMGap.Continuum.SU2TorusRPPolyCS
import YMGap.Continuum.SU2LogConvexZero

namespace YMGap.Continuum.SU2TorusGapCond

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2TorusRPCSShape (rpB PtSup)
open YMGap.Continuum.SU2LogConvexGap (LogConvex le_e e_le)
open YMGap.Continuum.SU2LogConvexZero (Nonneg gap_nonneg)

variable {M : Nat} (hM : 1 ≤ M) {β : Q'} (hβ : (0 : Q') ≤ β) (K : Nat)
  (τ : Nat → RatPoly) (G : Nat → Q') (X : Nat)

/-- Even subsequence. -/
def E (m : Nat) : Q' := G (2 * m)

include hβ in
theorem nonneg_E (hsup : ∀ x, x ≤ X → PtSup (M := M) (τ x))
    (hshift : ∀ x y, x ≤ X → y ≤ X → (rpB hM β K (τ x) (τ y)).eqv (G (x + y))) : Nonneg (E G) X := fun m hm => by
  have h := hshift m m hm hm
  rw [show m + m = 2 * m by omega] at h
  exact Q'.le_trans' _ _ _ (YMGap.Continuum.SU2TorusRPPolyCS.torus_rp_poly hM K hβ _ (hsup m hm)) (Q'.le_of_eqv h)

include hβ in
/-- **LogConvex from RP Cauchy–Schwarz (PROVED, conditional on `hsup`, `hshift`).** -/
theorem logConvex_E (hsup : ∀ x, x ≤ X → PtSup (M := M) (τ x))
    (hshift : ∀ x y, x ≤ X → y ≤ X → (rpB hM β K (τ x) (τ y)).eqv (G (x + y))) : LogConvex (E G) X := by
  intro j hj
  have cs := YMGap.Continuum.SU2TorusRPPolyCS.torus_cs_poly hM K hβ _ _ (hsup j (by omega)) (hsup (j + 2) hj)
  have h1 := hshift j (j + 2) (by omega) hj
  have h2 := hshift j j (by omega) (by omega)
  have h3 := hshift (j + 2) (j + 2) hj hj
  rw [show j + (j + 2) = 2 * (j + 1) by omega] at h1
  rw [show j + j = 2 * j by omega] at h2
  rw [show j + 2 + (j + 2) = 2 * (j + 2) by omega] at h3
  show G (2 * (j + 1)) * G (2 * (j + 1)) ≤ G (2 * j) * G (2 * (j + 2))
  refine e_le (Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h1) (Q'.mul_eqv_congr_left _ _ _ h1))) ?_
  exact le_e cs (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h2) (Q'.mul_eqv_congr_left _ _ _ h3))

theorem pow_two_mul (q : Q') : ∀ m : Nat, (q ^ (2 * m)).eqv ((q * q) ^ m)
  | 0 => Q'.eqv_refl _
  | m + 1 => by
    show (q * (q * q ^ (2 * m))).eqv ((q * q) * (q * q) ^ m)
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) (Q'.mul_eqv_congr_left _ _ _ (pow_two_mul q m))

include hβ in
/-- **Conditional finite-volume ratio bound on the actual torus `T_K` measure (PROVED, conditional).**
STRONG COUPLING, fixed K; also true for U(1), not gap evidence. -/
theorem torus_gap_cond (hsup : ∀ x, x ≤ X → PtSup (M := M) (τ x))
    (hshift : ∀ x y, x ≤ X → y ≤ X → (rpB hM β K (τ x) (τ y)).eqv (G (x + y)))
    {C q : Q'} (hC : (0 : Q') ≤ C) (hq : (0 : Q') ≤ q) (hcl : ∀ n, n ≤ 2 * X → G n ≤ C * q ^ n)
    (k d : Nat) (h : k + d ≤ X) :
    E G (k + 1) ^ d * E G k ≤ C * (q * q) ^ (k + d) * E G k ^ d :=
  gap_nonneg (nonneg_E hM hβ K τ G X hsup hshift) (logConvex_E hM hβ K τ G X hsup hshift) hC
    (Q'.mul_nonneg _ _ hq hq)
    (fun m hm => le_e (hcl (2 * m) (by omega)) (Q'.mul_eqv_congr_left _ _ _ (pow_two_mul q m))) k d h

end YMGap.Continuum.SU2TorusGapCond
