/-
# The `hafδ` allowance is small at every step, in particular at the `⌊log₂(j+1)⌋` jumps

**Label: PROVED bounds plus a PROVED scalar necessary condition. NOT gap evidence; NOT a refutation
of `hafδ` (that needs spectral data, which is numerical only).**
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs).
Convention: repo nome `w` matches the Numerics `t = -4 ln w`; U(1) is confined only for
w ≤ 1/8 and already Coulomb (massless) at w = 1/2 and 0.5145 (YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved).

`hafδ_OPEN` (`RelativeDissipationScaleChain.lean:259`) is `∀ k, δ_k ≤ C·afGap(j0+k)²`, where step `k`
goes from coarse scale `j0+k` to fine scale `j0+k+1`. Results:
* `allowance_le_inv`: under the r49 budget `C·afA²·inv(j0+2) < seed ≤ 1`, EVERY allowance obeys
  `C·afGap(j0+k)² ≤ inv(j0+k+3) = 1/(j0+k+4)`, whatever `C` is.
* `allowance_le_inv17` / `allowance_le_inv5`: at coarse index `≥ 14` (resp. `≥ 2`), `≤ 1/18` (resp. `1/6`).
* `allowance_tenth_jumps`: for `C = 1/10`, at `j = 2,3,6,7,14,15,30,31,62,63`, `C·afGap(j)² < 1/100`.
* `rho_le_of_relative` (scalar shadow of `twoStepFactor_of_relative_comparison`): if a test vector
  has `‖T_F(2)y‖² = ρF·a`, `‖T_C(1)Φy‖² ≤ ρC·‖Φy‖² ≤ ρC·a` and the relative comparison holds with
  `δ ≤ ε`, then `ρF ≤ ε + (1-ε)ρC`, i.e. `1-ρF ≥ (1-ε)(1-ρC)`.
* `hafδ_forces_near_halving`: combining, `hafδ` at step `k` under the budget forces
  `1 - ρF ≥ (1 - 1/(j0+k+4))(1 - ρC)`. With `ρF = e^{-4m_F}`, `ρC = e^{-2m_C}` this is near-halving
  `m_F ≳ (1 - 1/(j+4))·m_C/2` for small masses (analysis, not proved).

Constructive, no external library; axioms within `propext`, `Quot.sound`.
-/

import YMGap.RG.RelativeDissipationScaleChain

namespace YMGap.RG.AfDeltaJumpAllowance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory (afGap afGap_pos afA)
open YMGap.RG.RelativeDissipationScaleChain (inv inv_nonneg afGap_le)

/-- `inv` is antitone (`inv m = 1/(m+1)`).
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem inv_anti {n m : Nat} (h : n ≤ m) : inv m ≤ inv n := by
  show (1 : Int) * ((inv n).den : Int) ≤ 1 * ((inv m).den : Int)
  rw [Int.one_mul, Int.one_mul]
  exact Int.ofNat_le.mpr (Nat.succ_le_succ h)

/-- **Every `hafδ` allowance is at most `1/(j0+k+4)` under the r49 budget (PROVED).**
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem allowance_le_inv (C seed : Q') (j0 k : Nat) (hC : (0 : Q') ≤ C) (hseed : seed ≤ (1 : Q'))
    (hbudget : C * (afA * afA) * inv (j0+2) < seed) :
    C * (afGap (j0+k) * afGap (j0+k)) ≤ inv (j0+k+3) := by
  have hA : (0 : Q') ≤ afA := by decide
  have hi : (0 : Q') ≤ inv (j0+k+3) := inv_nonneg _
  have hg := afGap_le (j0+k)
  have hsq : afGap (j0+k) * afGap (j0+k) ≤ (afA * inv (j0+k+3)) * (afA * inv (j0+k+3)) :=
    Q'.mul_le_mul_of_nonneg hg hg (Q'.mul_nonneg _ _ hA hi) (Q'.le_of_lt (afGap_pos _))
  have h1 := Q'.mul_le_mul_of_nonneg_left _ _ C hsq hC
  have hid : Q'.eqv (C * ((afA * inv (j0+k+3)) * (afA * inv (j0+k+3))))
      ((C * (afA * afA) * inv (j0+k+3)) * inv (j0+k+3)) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
      (.mul (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 2)) (.var 2)) (by decide)
      (fun | 0 => C | 1 => afA | _ => inv (j0+k+3))
  have hcA : (0 : Q') ≤ C * (afA * afA) := Q'.mul_nonneg _ _ hC (Q'.mul_nonneg _ _ hA hA)
  have hanti : inv (j0+k+3) ≤ inv (j0+2) :=
    inv_anti (Nat.add_le_add (Nat.le_add_right j0 k) (by decide : 2 ≤ 3))
  have h2 : C * (afA * afA) * inv (j0+k+3) ≤ C * (afA * afA) * inv (j0+2) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hanti hcA
  have h3 : C * (afA * afA) * inv (j0+2) ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ (Q'.le_of_lt hbudget) hseed
  have h4 : C * (afA * afA) * inv (j0+k+3) * inv (j0+k+3) ≤ (1 : Q') * inv (j0+k+3) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.le_trans' _ _ _ h2 h3) hi
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv hid)
    (Q'.le_trans' _ _ _ h4 (Q'.le_of_eqv (Q'.one_mul_eqv _))))

/-- **At coarse index `j0+k ≥ 14` (the jumps `14→15`, `30→31`, `62→63`, …) every allowance is
`≤ 1/18` under the budget (PROVED).**
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem allowance_le_inv17 (C seed : Q') (j0 k : Nat) (hC : (0 : Q') ≤ C) (hseed : seed ≤ (1 : Q'))
    (hbudget : C * (afA * afA) * inv (j0+2) < seed) (hj : 14 ≤ j0 + k) :
    C * (afGap (j0+k) * afGap (j0+k)) ≤ inv 17 :=
  Q'.le_trans' _ _ _ (allowance_le_inv C seed j0 k hC hseed hbudget)
    (inv_anti (Nat.add_le_add_right hj 3))

/-- **At coarse index `j0+k ≥ 2` (all jumps `2^m-2 → 2^m-1`, `m ≥ 2`) every allowance is `≤ 1/6`.**
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem allowance_le_inv5 (C seed : Q') (j0 k : Nat) (hC : (0 : Q') ≤ C) (hseed : seed ≤ (1 : Q'))
    (hbudget : C * (afA * afA) * inv (j0+2) < seed) (hj : 2 ≤ j0 + k) :
    C * (afGap (j0+k) * afGap (j0+k)) ≤ inv 5 :=
  Q'.le_trans' _ _ _ (allowance_le_inv C seed j0 k hC hseed hbudget)
    (inv_anti (Nat.add_le_add_right hj 3))

/-- `1/18 < 1/6 < 1/5` (decidable). -/
theorem inv17_lt_inv5_lt_fifth : inv 17 < inv 5 ∧ inv 5 < Q'.mkPos 1 5 (by decide) := by decide

/-- **`C = 1/10` allowances at the jump indices (decidable):** `< 1/100` at
`j = 2,3,6,7,14,15,30,31,62,63` (`afGap(2)² /10 ≈ 0.0091` is the largest).
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem allowance_tenth_jumps :
    ∀ j, j ∈ [2, 3, 6, 7, 14, 15, 30, 31, 62, 63] →
      Q'.mkPos 1 10 (by decide) * (afGap j * afGap j) < Q'.mkPos 1 100 (by decide) := by
  decide

/-- **Scalar necessary condition (PROVED):** `a·ρF ≤ a·(δ + (1-δ)ρC)`, `a > 0`, `δ ≤ ε`, `ρC ≤ 1`
give `ρF ≤ ε + (1-ε)ρC`. (Scalar shadow of the relative comparison on a test vector.)
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem rho_le_of_relative (a rhoF rhoC delta eps : Q') (ha : (0 : Q') < a) (hde : delta ≤ eps)
    (hC1 : rhoC ≤ (1 : Q'))
    (hrel : a * rhoF ≤ a * (delta + ((1 : Q') - delta) * rhoC)) :
    rhoF ≤ eps + ((1 : Q') - eps) * rhoC := by
  have h0 := Q'.le_of_mul_le_mul_left hrel ha
  have hm := Q'.mul_le_mul_of_nonneg_right _ _ ((1 : Q') - rhoC) hde (Q'.sub_nonneg_of_le hC1)
  have hs := Q'.add_le_add_left rhoC _ _ hm
  have e1 : Q'.eqv (delta + ((1 : Q') - delta) * rhoC) (rhoC + delta * ((1 : Q') - rhoC)) :=
    poly_identity_of_normal_eq
      (.add (.var 0) (.mul (.add (.const 1) (.neg (.var 0))) (.var 1)))
      (.add (.var 1) (.mul (.var 0) (.add (.const 1) (.neg (.var 1))))) (by decide)
      (fun | 0 => delta | _ => rhoC)
  have e2 : Q'.eqv (rhoC + eps * ((1 : Q') - rhoC)) (eps + ((1 : Q') - eps) * rhoC) :=
    poly_identity_of_normal_eq
      (.add (.var 1) (.mul (.var 0) (.add (.const 1) (.neg (.var 1)))))
      (.add (.var 0) (.mul (.add (.const 1) (.neg (.var 0))) (.var 1))) (by decide)
      (fun | 0 => eps | _ => rhoC)
  exact Q'.le_trans' _ _ _ h0 (Q'.le_trans' _ _ _ (Q'.le_of_eqv e1)
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv e2)))

/-- **`hafδ` under the budget forces near-halving at every step (PROVED):** if step `k` satisfies
`hafδ` and the scalar relative comparison holds for a test vector, then
`ρF ≤ inv(j0+k+3) + (1 - inv(j0+k+3))·ρC`.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem hafδ_forces_near_halving (C seed a rhoF rhoC delta : Q') (j0 k : Nat)
    (hC : (0 : Q') ≤ C) (hseed : seed ≤ (1 : Q'))
    (hbudget : C * (afA * afA) * inv (j0+2) < seed)
    (hafδ : delta ≤ C * (afGap (j0+k) * afGap (j0+k)))
    (ha : (0 : Q') < a) (hC1 : rhoC ≤ (1 : Q'))
    (hrel : a * rhoF ≤ a * (delta + ((1 : Q') - delta) * rhoC)) :
    rhoF ≤ inv (j0+k+3) + ((1 : Q') - inv (j0+k+3)) * rhoC :=
  rho_le_of_relative a rhoF rhoC delta _ ha
    (Q'.le_trans' _ _ _ hafδ (allowance_le_inv C seed j0 k hC hseed hbudget)) hC1 hrel

end YMGap.RG.AfDeltaJumpAllowance
