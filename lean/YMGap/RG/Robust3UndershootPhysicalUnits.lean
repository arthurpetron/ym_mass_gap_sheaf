/-
# Physical units for the exact-rational schedule `Robust3`: `2ⁿ·a_n ≤ P₃·a_0`, `P₃ ≈ 81.92`

**Label: PROVED rational reduction. The spacing hypothesis `hspacing_OPEN` is OPEN (physics input,
numerical and asymptotic support only). NOT gap evidence. `δ_min = 0` for `ℓ ≤ 1` is only a NECESSARY
condition: it removes the obstruction but does not prove `hafδ`.**

U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it
would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). Per the
numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover.

The undershoot allowances are the same rational family as `Robust2`:
* head `ρ_i`: 101/100, 41/40, 6/5, 3/2, 5/3, 9/5, 36/25, 33/25, 63/50, 61/50, 59/50;
* tail `ρ_i = (m+13)(m+1)/(m(m+14))`, `m = i − 7`, with telescoping weight `(m+13)/m`.

On the `Robust3` schedule the spacing ratio `(ρ−1)/(2^{1−ℓ_lo}−1)` tends to
`(13/(64A²))/(ln 2·L)` with `L = 0.07295` (naive 3L(−q), the worst model), i.e. ≈ 1.0655. The minimum over the
sampled `j ≤ 10⁷` is 1.0655 (audit; numerical/asymptotic, NOT proved). So `P₃ = ω_0 = 127996107199191/1562500000000` (`U₃ ≈ 6.356`),
recomputed by `decide` below; the weight lemmas are those of `Robust2UndershootPhysicalUnits` (imported, unchanged).

Constructive, no external library; axioms within `propext`, `Quot.sound`.
-/

import YMGap.RG.Robust2UndershootPhysicalUnits
import YMGap.RG.Robust3UndershootAfSchedule

namespace YMGap.RG.Robust3UndershootPhysicalUnits

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RG.UndershootPhysicalUnits (spacing_bound)
open YMGap.RG.Robust2UndershootPhysicalUnits (r2Rho r2Omega r2_weight r2_omega_ge_one)

/-- `ρ_i` for `Robust3` (same rational family as `Robust2`). -/
def r3Rho (i : Nat) : Q' := r2Rho i

/-- Telescoping weights for `Robust3`. -/
def r3Omega (i : Nat) : Q' := r2Omega i

theorem r3_weight (i : Nat) : r3Rho i * r3Omega (i+1) ≤ r3Omega i := r2_weight i

theorem r3_omega_ge_one (i : Nat) : (1 : Q') ≤ r3Omega i := r2_omega_ge_one i

/-- `P₃ = ω_0 = 127996107199191/1562500000000`. -/
def r3P : Q' := Q'.mkPos 127996107199191 1562500000000 (by decide)

/-- `P₃` recomputed exactly from the weight chain, and `81 < P₃ < 82` (decidable). -/
theorem r3P_value : r3Omega 0 = r3P ∧ Q'.ofNat 81 < r3P ∧ r3P < Q'.ofNat 82 := by decide

/-- **Physical-units spacing bound for `Robust3` (PROVED reduction):** under
`hspacing_OPEN : 2·a_{i+1} ≤ ρ_i·a_i` (exactly `ρ_i ≥ 2^{1−ℓ_i}`), `2ⁿ·a_n ≤ P₃·a_0` for every `n`.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it
would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). Per the
numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover. -/
theorem robust3_spacing_bound (a : Nat → Q') (ha : ∀ i, (0 : Q') ≤ a i)
    (hspacing_OPEN : ∀ i, Q'.ofNat 2 * a (i+1) ≤ r3Rho i * a i) (n : Nat) :
    Q'.ofNat (2 ^ n) * a n ≤ r3P * a 0 := by
  have h := spacing_bound a r3Rho r3Omega ha r3_omega_ge_one hspacing_OPEN r3_weight n
  rw [r3P_value.1] at h
  exact h

end YMGap.RG.Robust3UndershootPhysicalUnits
