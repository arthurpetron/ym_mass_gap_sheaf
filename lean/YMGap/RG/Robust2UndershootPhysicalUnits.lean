/-
# Physical units for the matched+c-held robust schedule: `2ⁿ·a_n ≤ P₂·a_0`, `P₂ ≈ 81.92`

**Label: PROVED rational reduction. The spacing hypothesis `hspacing_OPEN` is OPEN (physics input,
numerical support only). NOT gap evidence. `δ_min = 0` for `ℓ ≤ 1` is only a NECESSARY condition: it
removes the obstruction but does not prove `hafδ`.**

U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it
would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). Per the
numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover.

Spacing: `a_{i+1} = 2^{-ℓ_i} a_i`, so `hspacing_OPEN : 2·a_{i+1} ≤ ρ_i·a_i` is EXACTLY `ρ_i ≥ 2^{1-ℓ_i}`
(no convexity step). The `ρ_i` below are chosen as `ρ_i ≥ 2^{1-ℓ_lo,i}`, where `ℓ_lo,i` is the minimum over the
Numerics §9/§10 (15) models of `ℓ − 2σ` on the `Robust2` schedule (audit; numerical, NOT proved).
* crossover `i < 6`: 101/100, 41/40, 6/5, 3/2, 5/3, 9/5 (unchanged; `≥ 2^{1-ℓ_TM}`, Numerics §7);
* data window `6 ≤ i ≤ 10`: 36/25, 33/25, 63/50, 61/50, 59/50;
* tail `i ≥ 11`, `m = i - 7`: `ρ_i = (m+13)(m+1)/(m(m+14))`, i.e. `u_i = 13/(m(m+14))`; telescoping weight
  `(m+13)/m` (weight step holds with equality).

Reuses the generic `spacing_bound` from `UndershootPhysicalUnits` (imported, unchanged).
`r2P = r2Omega 0 = 127996107199191/1562500000000 ≈ 81.918` (`U₂ = log₂ P₂ ≈ 6.356`): crossover 5.590,
data window 3.454, tail 17/4.

Constructive, no external library; axioms within `propext`, `Quot.sound`.
-/

import YMGap.RG.UndershootPhysicalUnits
import YMGap.RG.Robust2UndershootAfSchedule

namespace YMGap.RG.Robust2UndershootPhysicalUnits

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RG.UndershootPhysicalUnits (spacing_bound)

/-- Head `ρ_i`, `i < 11`. -/
def r2RhoTab : Nat → Q'
  | 0 => Q'.mkPos 101 100 (by decide)
  | 1 => Q'.mkPos 41 40 (by decide)
  | 2 => Q'.mkPos 6 5 (by decide)
  | 3 => Q'.mkPos 3 2 (by decide)
  | 4 => Q'.mkPos 5 3 (by decide)
  | 5 => Q'.mkPos 9 5 (by decide)
  | 6 => Q'.mkPos 36 25 (by decide)
  | 7 => Q'.mkPos 33 25 (by decide)
  | 8 => Q'.mkPos 63 50 (by decide)
  | 9 => Q'.mkPos 61 50 (by decide)
  | _ => Q'.mkPos 59 50 (by decide)

/-- Head weights (exact backward products from `ω_11 = 17/4`). -/
def r2OmegaTab : Nat → Q'
  | 0 => Q'.mkPos 127996107199191 1562500000000 (by decide)
  | 1 => Q'.mkPos 1267288190091 15625000000 (by decide)
  | 2 => Q'.mkPos 30909468051 390625000 (by decide)
  | 3 => Q'.mkPos 10303156017 156250000 (by decide)
  | 4 => Q'.mkPos 3434385339 78125000 (by decide)
  | 5 => Q'.mkPos 10303156017 390625000 (by decide)
  | 6 => Q'.mkPos 1144795113 78125000 (by decide)
  | 7 => Q'.mkPos 127199457 12500000 (by decide)
  | 8 => Q'.mkPos 3854529 500000 (by decide)
  | 9 => Q'.mkPos 61183 10000 (by decide)
  | _ => Q'.mkPos 1003 200 (by decide)

private theorem pos4 (k : Nat) : 0 < k + 4 := Nat.lt_of_lt_of_le (by decide) (Nat.le_add_left 4 k)

/-- Tail `ρ` with `m = k + 4`: `(m+13)(m+1)/(m(m+14))`. -/
def r2RhoTail (k : Nat) : Q' :=
  Q'.mkPos (((k+17) * (k+5) : Nat) : Int) ((k+4) * (k+18))
    (Nat.mul_pos (pos4 k) (Nat.lt_of_lt_of_le (by decide) (Nat.le_add_left 18 k)))

/-- Tail weight `(m+13)/m`, `m = k + 4`. -/
def r2OmegaTail (k : Nat) : Q' := Q'.mkPos (((k+17) : Nat) : Int) (k+4) (pos4 k)

def r2Rho (i : Nat) : Q' := if i < 11 then r2RhoTab i else r2RhoTail (i - 11)
def r2Omega (i : Nat) : Q' := if i < 11 then r2OmegaTab i else r2OmegaTail (i - 11)

theorem r2_tail_weight (k : Nat) : r2RhoTail k * r2OmegaTail (k+1) ≤ r2OmegaTail k := by
  show (r2RhoTail k * r2OmegaTail (k+1)).num * ((r2OmegaTail k).den : Int)
    ≤ (r2OmegaTail k).num * ((r2RhoTail k * r2OmegaTail (k+1)).den : Int)
  rw [Q'.mul_den_cast]
  unfold r2RhoTail r2OmegaTail
  rw [Q'.mkPos_den, Q'.mkPos_den, Q'.mkPos_den]
  show ((((k+17) * (k+5) : Nat) : Int) * (((k+18) : Nat) : Int)) * (((k+4) : Nat) : Int)
    ≤ (((k+17) : Nat) : Int) * ((((k+4) * (k+18) : Nat) : Int) * (((k+5) : Nat) : Int))
  rw [← Int.natCast_mul, ← Int.natCast_mul, ← Int.natCast_mul, ← Int.natCast_mul]
  exact Int.ofNat_le.mpr (Nat.le_of_eq (by ac_rfl))

theorem r2OmegaTail_ge_one (k : Nat) : (1 : Q') ≤ r2OmegaTail k := by
  show (1 : Int) * ((r2OmegaTail k).den : Int) ≤ (r2OmegaTail k).num * 1
  unfold r2OmegaTail
  rw [Q'.mkPos_den, Int.one_mul, Int.mul_one]
  exact Int.ofNat_le.mpr (Nat.add_le_add_left (by decide : 4 ≤ 17) k)

private theorem not_lt_of_le' {a b : Nat} (h : b ≤ a) : ¬ a < b := fun h' =>
  Nat.lt_irrefl a (Nat.lt_of_lt_of_le h' h)

private theorem head_w : ∀ i, i < 11 → r2Rho i * r2Omega (i+1) ≤ r2Omega i := by decide
private theorem head_ge_one : ∀ i, i < 11 → (1 : Q') ≤ r2Omega i := by decide

theorem r2_weight (i : Nat) : r2Rho i * r2Omega (i+1) ≤ r2Omega i := by
  by_cases h : i < 11
  · exact head_w i h
  · have hi : 11 ≤ i := Nat.not_lt.mp h
    have e : i + 1 - 11 = (i - 11) + 1 := Nat.succ_sub hi
    unfold r2Rho r2Omega
    rw [if_neg h, if_neg (not_lt_of_le' (Nat.le_succ_of_le hi)), if_neg h, e]
    exact r2_tail_weight (i - 11)

theorem r2_omega_ge_one (i : Nat) : (1 : Q') ≤ r2Omega i := by
  by_cases h : i < 11
  · exact head_ge_one i h
  · unfold r2Omega; rw [if_neg h]; exact r2OmegaTail_ge_one _

/-- `P₂ = ω_0 = 127996107199191/1562500000000`, and `81 < P₂ < 82` (decidable). -/
def r2P : Q' := Q'.mkPos 127996107199191 1562500000000 (by decide)

theorem r2P_value : r2Omega 0 = r2P ∧ Q'.ofNat 81 < r2P ∧ r2P < Q'.ofNat 82 := by decide

/-- **Physical-units spacing bound for the Robust2 schedule (PROVED reduction):** under
`hspacing_OPEN : 2·a_{i+1} ≤ ρ_i·a_i` (exactly `ℓ_i ≥ 1 − log₂ ρ_i`), `2ⁿ·a_n ≤ P₂·a_0` with
`P₂ = 127996107199191/1562500000000 ≈ 81.92` for every `n`.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it
would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). Per the
numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover. -/
theorem robust2_spacing_bound (a : Nat → Q') (ha : ∀ i, (0 : Q') ≤ a i)
    (hspacing_OPEN : ∀ i, Q'.ofNat 2 * a (i+1) ≤ r2Rho i * a i) (n : Nat) :
    Q'.ofNat (2 ^ n) * a n ≤ r2P * a 0 := by
  have h := spacing_bound a r2Rho r2Omega ha r2_omega_ge_one hspacing_OPEN r2_weight n
  rw [r2P_value.1] at h
  exact h

end YMGap.RG.Robust2UndershootPhysicalUnits
