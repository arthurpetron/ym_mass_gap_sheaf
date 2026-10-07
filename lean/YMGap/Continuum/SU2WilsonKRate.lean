/-
# Wilson action, commit 6: rate in the Taylor order `K` (coefficient level, including `c_0`)

**STRONG COUPLING ONLY (β ≲ 1e-4).** This is a volume-uniform strong-coupling cluster expansion for the
actual Wilson action. It is equally true for U(1). It is NOT mass-gap or continuum evidence.

For `0 ≤ β`, `2β ≤ 1`, every `s` and every `K ≤ K' = K + j`:

  `c_s^{(K)} ≤ c_s^{(K')} ≤ c_s^{(K)} + 2 β^{K+1}`        (`wCoeff_cauchy`)

In particular, `c_0^{(K)}` (the normalisation carried in `Z_W ≈ c_0^{|P|} Ξ`) is nondecreasing and Cauchy
in `K` at the explicit rate `2β^{K+1}`. Together with the K-uniform statements already proved
(`envelope_le`: `B_K ≤ 2β`; `c0_ge_one`; `zn_abs_le`; `su2_link_decay_wilson`), every K-dependence of the
Wilson gas is either uniform or Cauchy with this rate.
-/

import YMGap.Continuum.SU2WilsonActivity

namespace YMGap.Continuum.SU2WilsonKRate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.SU2WilsonCharacterPower (wCoeff mult up down)
open YMGap.Continuum.SU2WilsonCoeffBounds (pow2 mult_nonneg add_nonneg')
open YMGap.Continuum.SU2WilsonActivity

local infix:50 " ≈ " => Q'.eqv
local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩

theorem pow2_nonneg : ∀ k, (0 : Q') ≤ pow2 k
  | 0 => by decide
  | k + 1 => Q'.mul_nonneg _ _ (by decide) (pow2_nonneg k)

theorem two_mul_eqv (x : Q') : 2 * x ≈ x + x :=
  let V := PolyExpr.var
  poly_identity_of_normal_eq (.const 2 * V 0) (V 0 + V 0) (by decide) (fun _ => x)

/-- `mult k s ≤ 2^k`. -/
theorem mult_le_pow2 : ∀ k s, mult k s ≤ pow2 k
  | 0, 0 => by decide
  | 0, _ + 1 => show (0 : Q') ≤ 1 by decide
  | k + 1, s => by
    have hu : up (mult k) s ≤ pow2 k := by
      cases s with
      | zero => exact pow2_nonneg k
      | succ s => exact mult_le_pow2 k s
    exact Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ hu)
      (Q'.add_le_add_left _ _ _ (mult_le_pow2 k (s + 1)))) (Q'.le_of_eqv (Q'.eqv_symm (two_mul_eqv _)))

/-- One step: `c_s^{(K)} ≤ c_s^{(K+1)} ≤ c_s^{(K)} + β^{K+1}`. -/
theorem wCoeff_step {β : Q'} (hβ : (0 : Q') ≤ β) (K s : Nat) :
    wCoeff (wilsonA β) K s ≤ wCoeff (wilsonA β) (K + 1) s ∧
      wCoeff (wilsonA β) (K + 1) s ≤ wCoeff (wilsonA β) K s + β ^ (K + 1) := by
  have ha := wilsonA_nonneg hβ (K + 1)
  refine ⟨?_, Q'.add_le_add_left _ _ _ (Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (mult_le_pow2 (K + 1) s) ha) (wilsonA_pow2_le hβ (K + 1)))⟩
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (YMGap.Constructive.QPoly.q_add_zero_eqv _)))
    (Q'.add_le_add_left _ _ _ (Q'.mul_nonneg _ _ ha (mult_nonneg _ s)))

theorem cauchy_aux {β : Q'} (hβ : (0 : Q') ≤ β) (h2 : 2 * β ≤ 1) (K s : Nat) : ∀ j,
    wCoeff (wilsonA β) (K + j) s + 2 * β ^ (K + j + 1) ≤ wCoeff (wilsonA β) K s + 2 * β ^ (K + 1)
  | 0 => Q'.le_refl' _
  | j + 1 => by
    let V := PolyExpr.var
    let t := β ^ (K + j + 1)
    have ht : (0 : Q') ≤ t := Q'.pow_nonneg β hβ _
    have hs := (wCoeff_step hβ (K + j) s).2
    have e1 : (wCoeff (wilsonA β) (K + j) s + t) + 2 * β ^ (K + j + 1 + 1) ≈
        wCoeff (wilsonA β) (K + j) s + (t + (2 * β) * t) :=
      poly_identity_of_normal_eq (V 0 + V 1 + V 3 * (V 2 * V 1)) (V 0 + (V 1 + V 3 * V 2 * V 1)) (by decide)
        (fun | 0 => wCoeff (wilsonA β) (K + j) s | 1 => t | 2 => β | _ => 2)
    have e2 : wCoeff (wilsonA β) (K + j) s + (t + 1 * t) ≈ wCoeff (wilsonA β) (K + j) s + 2 * t :=
      poly_identity_of_normal_eq (V 0 + (V 1 + .const 1 * V 1)) (V 0 + .const 2 * V 1) (by decide)
        (fun | 0 => wCoeff (wilsonA β) (K + j) s | _ => t)
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ hs) ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv e1) ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ (Q'.add_le_add_left _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ h2 ht))) ?_
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e2) (cauchy_aux hβ h2 K s j)

/-- **Rate in K** (STRONG COUPLING ONLY): for `0 ≤ β`, `2β ≤ 1`, all `s`, `K`, `j`:
`c_s^{(K)} ≤ c_s^{(K+j)} ≤ c_s^{(K)} + 2β^{K+1}`. With `s = 0` this is the K-rate of the normalisation `c_0`. -/
theorem wCoeff_cauchy {β : Q'} (hβ : (0 : Q') ≤ β) (h2 : 2 * β ≤ 1) (K s j : Nat) :
    wCoeff (wilsonA β) K s ≤ wCoeff (wilsonA β) (K + j) s ∧
      wCoeff (wilsonA β) (K + j) s ≤ wCoeff (wilsonA β) K s + 2 * β ^ (K + 1) := by
  refine ⟨?_, ?_⟩
  · induction j with
    | zero => exact Q'.le_refl' _
    | succ j ih => exact Q'.le_trans' _ _ _ ih (wCoeff_step hβ (K + j) s).1
  · refine Q'.le_trans' _ _ _ ?_ (cauchy_aux hβ h2 K s j)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (YMGap.Constructive.QPoly.q_add_zero_eqv _)))
      (Q'.add_le_add_left _ _ _ (Q'.mul_nonneg _ _ (by decide) (Q'.pow_nonneg β hβ _)))

end YMGap.Continuum.SU2WilsonKRate

#print axioms YMGap.Continuum.SU2WilsonKRate.mult_le_pow2
#print axioms YMGap.Continuum.SU2WilsonKRate.wCoeff_cauchy
