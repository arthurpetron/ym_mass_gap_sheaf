/-
# Torus RP, K → ∞ step 1: the Taylor tail `T_{K+j} − T_K` at one plaquette, with an explicit ℓ¹ rate

* `wilsonPoly_add`: `wilsonPoly x a (K+j) = wilsonPoly x a K ++ wtail x a K j`, a literal list identity, so no PE is needed.
* `l1_chiPow`: `l1 (U x 1) ≤ 2·Lw` gives `l1 (χ_1^k) ≤ 2^k · Lw^k`.
* `tsum_le`: `Σ_{i<j} r^{K+1+i} ≤ 2 r^{K+1}` for `0 ≤ r`, `2r ≤ 1`.
* `l1_wtail_le`: for the Wilson coefficients (`wilsonA β`), `l1 (wtail) ≤ tsum (β·Lw) K j ≤ 2 (β·Lw)^{K+1}`, uniform in `j`.

STRONG COUPLING (`2·β·Lw ≤ 1`; for a plaquette scalar `Lw = 256`). This is the monomial (ℓ¹) tail. Per-`s` character
rates (`wCoeff_cauchy`) are not summable uniformly in `j` in ℓ¹, so this route uses `wilsonA_pow2_le` from
`SU2WilsonActivity` instead. Nothing about a limit object is claimed.
-/

import YMGap.Continuum.SU2TorusRPKLimit
import YMGap.Continuum.SU2WilsonKRate

namespace YMGap.Continuum.SU2TorusRPKTail

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2WilsonCharacterPower (wilsonPoly chiPow)
open YMGap.Continuum.SU2WilsonCoeffBounds (pow2)
open YMGap.Continuum.SU2WilsonActivity (wilsonA wilsonA_nonneg wilsonA_pow2_le)
open YMGap.Continuum.SU2HaarL1Activity (l1 l1_nonneg l1_mul l1_add_le l1_smul)

local infix:50 " ≈ " => Q'.eqv
local instance : Add PolyExpr := ⟨PolyExpr.add⟩
local instance : Mul PolyExpr := ⟨PolyExpr.mul⟩

/-- Tail `Σ_{i<j} a_{K+1+i} χ_1^{K+1+i}`. -/
def wtail (x : RatPoly) (a : Nat → Q') (K : Nat) : Nat → RatPoly
  | 0 => []
  | j + 1 => polyAdd (wtail x a K j) (polySmul (a (K + j + 1)) (chiPow x (K + j + 1)))

theorem wilsonPoly_add (x : RatPoly) (a : Nat → Q') (K : Nat) :
    ∀ j, wilsonPoly x a (K + j) = polyAdd (wilsonPoly x a K) (wtail x a K j)
  | 0 => (List.append_nil _).symm
  | j + 1 => by
    show polyAdd (wilsonPoly x a (K + j)) _ = _
    rw [wilsonPoly_add x a K j]
    exact List.append_assoc _ _ _

theorem l1_one : l1 polyOne ≤ 1 := by decide

theorem l1_chiPow (x : RatPoly) {Lw : Q'} (hL : (0 : Q') ≤ Lw)
    (hU : l1 (YMGap.Continuum.SU2CharacterSquareIdentity.U x 1) ≤ 2 * Lw) :
    ∀ k, l1 (chiPow x k) ≤ pow2 k * Lw ^ k
  | 0 => (by decide : l1 polyOne ≤ (1 : Q') * 1)
  | k + 1 => by
    let V := PolyExpr.var
    have e : (2 * Lw) * (pow2 k * Lw ^ k) ≈ pow2 (k + 1) * Lw ^ (k + 1) :=
      poly_identity_of_normal_eq (.const 2 * V 0 * (V 1 * V 2)) (.const 2 * V 1 * (V 0 * V 2)) (by decide)
        (fun | 0 => Lw | 1 => pow2 k | _ => Lw ^ k)
    refine Q'.le_trans' _ _ _ (l1_mul _ _) (Q'.le_trans' _ _ _ ?_ (Q'.le_of_eqv e))
    exact Q'.mul_le_mul_of_nonneg hU (l1_chiPow x hL hU k) (Q'.mul_nonneg _ _ (by decide) hL) (l1_nonneg _)

theorem mul_pow (a b : Q') : ∀ k : Nat, a ^ k * b ^ k ≈ (a * b) ^ k
  | 0 => Q'.mul_one_eqv 1
  | k + 1 => by
    let V := PolyExpr.var
    have e : (a * a ^ k) * (b * b ^ k) ≈ (a * b) * (a ^ k * b ^ k) :=
      poly_identity_of_normal_eq (V 0 * V 1 * (V 2 * V 3)) (V 0 * V 2 * (V 1 * V 3)) (by decide)
        (fun | 0 => a | 1 => a ^ k | 2 => b | _ => b ^ k)
    exact Q'.eqv_trans _ _ _ e (Q'.mul_eqv_congr_left _ _ _ (mul_pow a b k))

/-- `Σ_{i<j} r^{K+1+i}`. -/
def tsum (r : Q') (K : Nat) : Nat → Q'
  | 0 => 0
  | j + 1 => tsum r K j + r ^ (K + j + 1)

theorem tsum_geo {r : Q'} (hr : (0 : Q') ≤ r) (h2 : 2 * r ≤ 1) (K : Nat) :
    ∀ j, tsum r K j + 2 * r ^ (K + j + 1) ≤ 2 * r ^ (K + 1)
  | 0 => by
      show 0 + 2 * r ^ (K + 0 + 1) ≤ 2 * r ^ (K + 1)
      rw [Q'.zero_add']; exact Q'.le_refl' _
  | j + 1 => by
    let V := PolyExpr.var
    let t := r ^ (K + j + 1)
    have ht : (0 : Q') ≤ t := Q'.pow_nonneg r hr _
    have e1 : tsum r K (j + 1) + 2 * r ^ (K + (j + 1) + 1) ≈ tsum r K j + (t + (2 * r) * t) :=
      poly_identity_of_normal_eq (V 0 + V 1 + .const 2 * (V 2 * V 1)) (V 0 + (V 1 + .const 2 * V 2 * V 1)) (by decide)
        (fun | 0 => tsum r K j | 1 => t | _ => r)
    have e2 : tsum r K j + (t + 1 * t) ≈ tsum r K j + 2 * t :=
      poly_identity_of_normal_eq (V 0 + (V 1 + .const 1 * V 1)) (V 0 + .const 2 * V 1) (by decide)
        (fun | 0 => tsum r K j | _ => t)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv e1) ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ (Q'.add_le_add_left _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ h2 ht))) ?_
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e2) (tsum_geo hr h2 K j)

theorem tsum_le {r : Q'} (hr : (0 : Q') ≤ r) (h2 : 2 * r ≤ 1) (K j : Nat) : tsum r K j ≤ 2 * r ^ (K + 1) :=
  Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) (Q'.pow_nonneg r hr _)))
    (tsum_geo hr h2 K j)

theorem l1_wtail_le (x : RatPoly) {β Lw : Q'} (hβ : (0 : Q') ≤ β) (hL : (0 : Q') ≤ Lw)
    (hU : l1 (YMGap.Continuum.SU2CharacterSquareIdentity.U x 1) ≤ 2 * Lw) (K : Nat) :
    ∀ j, l1 (wtail x (wilsonA β) K j) ≤ tsum (β * Lw) K j
  | 0 => Q'.le_refl' 0
  | j + 1 => by
    let k := K + j + 1
    have ha := wilsonA_nonneg hβ k
    have hterm : l1 (polySmul (wilsonA β k) (chiPow x k)) ≤ (β * Lw) ^ k := by
      refine Q'.le_trans' _ _ _ (l1_smul _ _) ?_
      rw [YMGap.Constructive.ExpNeg.abs_of_nonneg ha]
      refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (l1_chiPow x hL hU k) ha) ?_
      let V := PolyExpr.var
      have e : wilsonA β k * (pow2 k * Lw ^ k) ≈ (wilsonA β k * pow2 k) * Lw ^ k :=
        poly_identity_of_normal_eq (V 0 * (V 1 * V 2)) (V 0 * V 1 * V 2) (by decide)
          (fun | 0 => wilsonA β k | 1 => pow2 k | _ => Lw ^ k)
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv e) ?_
      refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ (wilsonA_pow2_le hβ k) (Q'.pow_nonneg _ hL _)) ?_
      exact Q'.le_of_eqv (mul_pow β Lw k)
    exact Q'.le_trans' _ _ _ (l1_add_le _ _) (YMGap.Constructive.ExpNeg.add_le_add2 (l1_wtail_le x hβ hL hU K j) hterm)

/-- Plaquette instance: `l1 (U x_p 1) ≤ 2·256` for the plaquette scalar `x_p`. -/
theorem l1_U_plaq (links : List YMGap.Continuum.ClusterCount4DProgress.Z4Link) (N : Nat)
    (p : YMGap.Continuum.ClusterCount4DProgress.Z4Plaq) :
    l1 (YMGap.Continuum.SU2CharacterSquareIdentity.U (YMGap.Continuum.SU2TorusMultiLinkPolyGibbs.plaqWord links N p).scalar 1)
      ≤ 2 * Q'.ofNat 256 := by
  refine Q'.le_trans' _ _ _ (l1_smul 2 _) ?_
  rw [YMGap.Constructive.ExpNeg.abs_of_nonneg (by decide)]
  exact Q'.mul_le_mul_of_nonneg_left _ _ _ (YMGap.Continuum.SU2HaarL1Activity.word_l1 links N p) (by decide)

end YMGap.Continuum.SU2TorusRPKTail

#print axioms YMGap.Continuum.SU2TorusRPKTail.wilsonPoly_add
#print axioms YMGap.Continuum.SU2TorusRPKTail.l1_wtail_le
#print axioms YMGap.Continuum.SU2TorusRPKTail.tsum_le
