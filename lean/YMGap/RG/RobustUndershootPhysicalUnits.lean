/-
# Physical units for the map-robust undershooting schedule: `2ⁿ·a_n ≤ P'·a_0`, `P' ≈ 55.07`

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
Numerics §9 models of `ℓ − 2σ` on the robust schedule (audit; numerical, NOT proved).
* crossover `i < 6`: 101/100, 41/40, 6/5, 3/2, 5/3, 9/5 (unchanged; `≥ 2^{1-ℓ_TM}`, Numerics §7);
* data window `6 ≤ i ≤ 10`: 36/25, 33/25, 63/50, 61/50, 59/50;
* tail `i ≥ 11`, `m = i - 4`: `ρ_i = (m+13)(m+1)/(m(m+14))`, i.e. `u_i = 13/(m(m+14))`; telescoping weight
  `(m+13)/m` (weight step holds with equality).

Reuses the generic `spacing_bound` from `UndershootPhysicalUnits` (imported, unchanged).
`ruP = ruOmega 0 = 1075597539489/19531250000 ≈ 55.071` (`U' = log₂ P' ≈ 5.783`): crossover 5.590,
data window 3.454, tail 20/7.

Constructive, no external library; axioms within `propext`, `Quot.sound`.
-/

import YMGap.RG.UndershootPhysicalUnits
import YMGap.RG.RobustUndershootAfSchedule

namespace YMGap.RG.RobustUndershootPhysicalUnits

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RG.UndershootPhysicalUnits (spacing_bound)

/-- Head `ρ_i`, `i < 11`. -/
def ruRhoTab : Nat → Q'
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

/-- Head weights (exact backward products from `ω_11 = 20/7`). -/
def ruOmegaTab : Nat → Q'
  | 0 => Q'.mkPos 1075597539489 19531250000 (by decide)
  | 1 => Q'.mkPos 10649480589 195312500 (by decide)
  | 2 => Q'.mkPos 519486858 9765625 (by decide)
  | 3 => Q'.mkPos 86581143 1953125 (by decide)
  | 4 => Q'.mkPos 57720762 1953125 (by decide)
  | 5 => Q'.mkPos 173162286 9765625 (by decide)
  | 6 => Q'.mkPos 19240254 1953125 (by decide)
  | 7 => Q'.mkPos 1068903 156250 (by decide)
  | 8 => Q'.mkPos 32391 6250 (by decide)
  | 9 => Q'.mkPos 3599 875 (by decide)
  | _ => Q'.mkPos 118 35 (by decide)

private theorem pos7 (k : Nat) : 0 < k + 7 := Nat.lt_of_lt_of_le (by decide) (Nat.le_add_left 7 k)

/-- Tail `ρ` with `m = k + 7`: `(m+13)(m+1)/(m(m+14))`. -/
def ruRhoTail (k : Nat) : Q' :=
  Q'.mkPos (((k+20) * (k+8) : Nat) : Int) ((k+7) * (k+21))
    (Nat.mul_pos (pos7 k) (Nat.lt_of_lt_of_le (by decide) (Nat.le_add_left 21 k)))

/-- Tail weight `(m+13)/m`, `m = k + 7`. -/
def ruOmegaTail (k : Nat) : Q' := Q'.mkPos (((k+20) : Nat) : Int) (k+7) (pos7 k)

def ruRho (i : Nat) : Q' := if i < 11 then ruRhoTab i else ruRhoTail (i - 11)
def ruOmega (i : Nat) : Q' := if i < 11 then ruOmegaTab i else ruOmegaTail (i - 11)

theorem ru_tail_weight (k : Nat) : ruRhoTail k * ruOmegaTail (k+1) ≤ ruOmegaTail k := by
  show (ruRhoTail k * ruOmegaTail (k+1)).num * ((ruOmegaTail k).den : Int)
    ≤ (ruOmegaTail k).num * ((ruRhoTail k * ruOmegaTail (k+1)).den : Int)
  rw [Q'.mul_den_cast]
  unfold ruRhoTail ruOmegaTail
  rw [Q'.mkPos_den, Q'.mkPos_den, Q'.mkPos_den]
  show ((((k+20) * (k+8) : Nat) : Int) * (((k+21) : Nat) : Int)) * (((k+7) : Nat) : Int)
    ≤ (((k+20) : Nat) : Int) * ((((k+7) * (k+21) : Nat) : Int) * (((k+8) : Nat) : Int))
  rw [← Int.natCast_mul, ← Int.natCast_mul, ← Int.natCast_mul, ← Int.natCast_mul]
  exact Int.ofNat_le.mpr (Nat.le_of_eq (by ac_rfl))

theorem ruOmegaTail_ge_one (k : Nat) : (1 : Q') ≤ ruOmegaTail k := by
  show (1 : Int) * ((ruOmegaTail k).den : Int) ≤ (ruOmegaTail k).num * 1
  unfold ruOmegaTail
  rw [Q'.mkPos_den, Int.one_mul, Int.mul_one]
  exact Int.ofNat_le.mpr (Nat.add_le_add_left (by decide : 7 ≤ 20) k)

private theorem not_lt_of_le' {a b : Nat} (h : b ≤ a) : ¬ a < b := fun h' =>
  Nat.lt_irrefl a (Nat.lt_of_lt_of_le h' h)

private theorem head_w : ∀ i, i < 11 → ruRho i * ruOmega (i+1) ≤ ruOmega i := by decide
private theorem head_ge_one : ∀ i, i < 11 → (1 : Q') ≤ ruOmega i := by decide

theorem ru_weight (i : Nat) : ruRho i * ruOmega (i+1) ≤ ruOmega i := by
  by_cases h : i < 11
  · exact head_w i h
  · have hi : 11 ≤ i := Nat.not_lt.mp h
    have e : i + 1 - 11 = (i - 11) + 1 := Nat.succ_sub hi
    unfold ruRho ruOmega
    rw [if_neg h, if_neg (not_lt_of_le' (Nat.le_succ_of_le hi)), if_neg h, e]
    exact ru_tail_weight (i - 11)

theorem ru_omega_ge_one (i : Nat) : (1 : Q') ≤ ruOmega i := by
  by_cases h : i < 11
  · exact head_ge_one i h
  · unfold ruOmega; rw [if_neg h]; exact ruOmegaTail_ge_one _

/-- `P' = ω_0 = 1075597539489/19531250000`, and `55 < P' < 56` (decidable). -/
def ruP : Q' := Q'.mkPos 1075597539489 19531250000 (by decide)

theorem ruP_value : ruOmega 0 = ruP ∧ Q'.ofNat 55 < ruP ∧ ruP < Q'.ofNat 56 := by decide

/-- **Physical-units spacing bound for the robust schedule (PROVED reduction):** under
`hspacing_OPEN : 2·a_{i+1} ≤ ρ_i·a_i` (exactly `ℓ_i ≥ 1 − log₂ ρ_i`), `2ⁿ·a_n ≤ P'·a_0` with
`P' = 1075597539489/19531250000 ≈ 55.07` for every `n`.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it
would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). Per the
numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover. -/
theorem robust_spacing_bound (a : Nat → Q') (ha : ∀ i, (0 : Q') ≤ a i)
    (hspacing_OPEN : ∀ i, Q'.ofNat 2 * a (i+1) ≤ ruRho i * a i) (n : Nat) :
    Q'.ofNat (2 ^ n) * a n ≤ ruP * a 0 := by
  have h := spacing_bound a ruRho ruOmega ha ru_omega_ge_one hspacing_OPEN ru_weight n
  rw [ruP_value.1] at h
  exact h

end YMGap.RG.RobustUndershootPhysicalUnits
