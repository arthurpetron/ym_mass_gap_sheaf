/-
# Physical units for the undershooting schedule: `2ⁿ·a_n ≤ P·a_0` with an explicit rational `P`

**Label: PROVED rational reduction. The spacing hypothesis `hspacing_OPEN` is OPEN (physics input,
numerical support only). NOT gap evidence. `δ_min = 0` for `ℓ ≤ 1` is only a NECESSARY condition: it
removes the obstruction but does not prove `hafδ`.**

U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it
would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). Per the
numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover.

With undershoot, the true spacing satisfies `a_{i+1} = 2^{-ℓ_i} a_i` with `ℓ_i ≥ 1 - u_i` (OPEN), so
`2ⁿ·a_n/a_0 = ∏ 2^{1-ℓ_i} ≤ ∏ 2^{u_i}`. Rational surrogate: for `0 ≤ u ≤ 1`, `2^u ≤ 1 + u`, because `2^u` is
**convex** (not concave) and so lies below its chord `1 + u` on `[0,1]` (real-analysis fact, NOT formalised).
Hence `ℓ_i ≥ 1 - u_i` implies the rational hypothesis `hspacing_OPEN : 2·a_{i+1} ≤ (1+u_i)·a_i`, and that
hypothesis is all that is used here.

* `spacing_weighted` (generic): if `2·a_{i+1} ≤ ρ_i·a_i` and `ρ_i·ω_{i+1} ≤ ω_i` (telescoping weights), then
  `2ⁿ·a_n·ω_n ≤ a_0·ω_0`. With `ω ≥ 1` this gives `2ⁿ·a_n ≤ ω_0·a_0`, and with a floor
  `floor ≤ 2ⁿ·M_n` it gives `floor·a_n ≤ (ω_0·a_0)·M_n`.
* `usRho` (`ρ_i = 1 + u_i`):
  * crossover `i < 6`: 101/100, 41/40, 6/5, 3/2, 5/3, 9/5 (from the TM ℓ, Numerics §7);
  * data window `6 ≤ i ≤ 10`: 36/25, 123/100, 117/100, 119/100, 23/20;
  * tail `i ≥ 11`, `m = i - 4`: `ρ_i = (m+10)(m+1)/(m(m+11))`, i.e. `u_i = 10/(m(m+11)) ≈ 0.041–0.044·g⁴`.
* `usOmega`: tail weight `(m+10)/m`, decreasing to 1 (the weight step holds with equality); head weights are
  exact backward products.
* `usP = usOmega 0 = 96256076646951/2500000000000 ≈ 38.502` (`U = log₂ P ≈ 5.27`). Of this, the crossover gives
  5.590, the data window 2.836, and the tail 17/7.

Constructive, no external library; axioms within `propext`, `Quot.sound`.
-/

import YMGap.RG.UndershootAfSchedule

namespace YMGap.RG.UndershootPhysicalUnits

set_option autoImplicit false

open YMGap.Constructive

private theorem ofNat_den (m : Nat) : ((Q'.ofNat m).den : Int) = 1 := rfl

theorem pow2_succ_eqv (n : Nat) :
    (Q'.ofNat (2 ^ (n+1))).eqv (Q'.ofNat (2 ^ n) * Q'.ofNat 2) := by
  show ((2 ^ (n+1) : Nat) : Int) * ((Q'.ofNat (2 ^ n) * Q'.ofNat 2).den : Int)
    = (((2 ^ n : Nat) : Int) * ((2 : Nat) : Int)) * ((Q'.ofNat (2 ^ (n+1))).den : Int)
  rw [Q'.mul_den_cast, ofNat_den, ofNat_den, ofNat_den, Int.mul_one, Int.mul_one, Int.mul_one,
    Nat.pow_succ, Int.natCast_mul]

theorem ofNat_nonneg (m : Nat) : (0 : Q') ≤ Q'.ofNat m := by
  show (0 : Int) * ((Q'.ofNat m).den : Int) ≤ ((m : Nat) : Int) * ((0 : Q').den : Int)
  rw [Int.zero_mul]
  exact Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)

/-- **Generic telescoping-weight bound (PROVED):** `2ⁿ·a_n·ω_n ≤ a_0·ω_0`. -/
theorem spacing_weighted (a rho om : Nat → Q') (ha : ∀ i, (0 : Q') ≤ a i)
    (hom : ∀ i, (0 : Q') ≤ om i)
    (hspacing : ∀ i, Q'.ofNat 2 * a (i+1) ≤ rho i * a i)
    (hw : ∀ i, rho i * om (i+1) ≤ om i) :
    ∀ n, Q'.ofNat (2 ^ n) * a n * om n ≤ a 0 * om 0
  | 0 => Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv (a 0)))
  | n+1 => by
    have hp := ofNat_nonneg (2 ^ n)
    have e1 : (Q'.ofNat (2 ^ (n+1)) * a (n+1) * om (n+1)).eqv
        (Q'.ofNat (2 ^ n) * ((Q'.ofNat 2 * a (n+1)) * om (n+1))) :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (pow2_succ_eqv n))
            (Q'.mul_assoc_eqv _ _ _)))
        (Q'.mul_assoc_eqv _ _ _)
    have l1 : Q'.ofNat (2 ^ n) * ((Q'.ofNat 2 * a (n+1)) * om (n+1)) ≤
        Q'.ofNat (2 ^ n) * ((rho n * a n) * om (n+1)) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ (hspacing n) (hom (n+1))) hp
    have e2 : (Q'.ofNat (2 ^ n) * ((rho n * a n) * om (n+1))).eqv
        (Q'.ofNat (2 ^ n) * (a n * (rho n * om (n+1)))) :=
      Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _))
          (Q'.mul_assoc_eqv _ _ _))
    have l2 : Q'.ofNat (2 ^ n) * (a n * (rho n * om (n+1))) ≤
        Q'.ofNat (2 ^ n) * (a n * om n) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (hw n) (ha n)) hp
    have e3 : Q'.ofNat (2 ^ n) * (a n * om n) ≤ Q'.ofNat (2 ^ n) * a n * om n :=
      Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e1) (Q'.le_trans' _ _ _ l1
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv e2) (Q'.le_trans' _ _ _ l2
        (Q'.le_trans' _ _ _ e3 (spacing_weighted a rho om ha hom hspacing hw n)))))

/-- **Spacing bound (PROVED):** with weights `ω ≥ 1`, `2ⁿ·a_n ≤ ω_0·a_0`. -/
theorem spacing_bound (a rho om : Nat → Q') (ha : ∀ i, (0 : Q') ≤ a i)
    (hom1 : ∀ i, (1 : Q') ≤ om i)
    (hspacing : ∀ i, Q'.ofNat 2 * a (i+1) ≤ rho i * a i)
    (hw : ∀ i, rho i * om (i+1) ≤ om i) (n : Nat) :
    Q'.ofNat (2 ^ n) * a n ≤ om 0 * a 0 := by
  have hom : ∀ i, (0 : Q') ≤ om i := fun i => Q'.le_trans' _ _ _ (by decide) (hom1 i)
  have hx : (0 : Q') ≤ Q'.ofNat (2 ^ n) * a n :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (YMGap.Constructive.QPoly.q_mul_zero _))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (ha n) (ofNat_nonneg _))
  have s1 : Q'.ofNat (2 ^ n) * a n ≤ Q'.ofNat (2 ^ n) * a n * om n :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.one_mul_eqv _)))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (hom1 n) hx)
  exact Q'.le_trans' _ _ _ s1 (Q'.le_trans' _ _ _
    (spacing_weighted a rho om ha hom hspacing hw n) (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))

/-- **Floor in physical units (PROVED):** `floor ≤ 2ⁿ·M_n` gives `floor·a_n ≤ (ω_0·a_0)·M_n`, i.e.
`M_n/a_n ≥ floor/(ω_0·a_0)`. -/
theorem floor_physical (a rho om M : Nat → Q') (fl : Q') (ha : ∀ i, (0 : Q') ≤ a i)
    (hom1 : ∀ i, (1 : Q') ≤ om i)
    (hspacing : ∀ i, Q'.ofNat 2 * a (i+1) ≤ rho i * a i)
    (hw : ∀ i, rho i * om (i+1) ≤ om i) (n : Nat) (hM : (0 : Q') ≤ M n)
    (hfl : fl ≤ Q'.ofNat (2 ^ n) * M n) :
    fl * a n ≤ (om 0 * a 0) * M n := by
  have s1 : fl * a n ≤ (Q'.ofNat (2 ^ n) * M n) * a n :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hfl (ha n)
  have e1 : ((Q'.ofNat (2 ^ n) * M n) * a n).eqv (M n * (Q'.ofNat (2 ^ n) * a n)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) (Q'.mul_assoc_eqv _ _ _)
  have s2 : M n * (Q'.ofNat (2 ^ n) * a n) ≤ M n * (om 0 * a 0) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (spacing_bound a rho om ha hom1 hspacing hw n) hM
  exact Q'.le_trans' _ _ _ s1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv e1)
    (Q'.le_trans' _ _ _ s2 (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))))

/-! ## The schedule's undershoot allowances and weights -/

/-- Head `ρ_i = 1 + u_i`, `i < 11`. -/
def rhoTab : Nat → Q'
  | 0 => Q'.mkPos 101 100 (by decide)
  | 1 => Q'.mkPos 41 40 (by decide)
  | 2 => Q'.mkPos 6 5 (by decide)
  | 3 => Q'.mkPos 3 2 (by decide)
  | 4 => Q'.mkPos 5 3 (by decide)
  | 5 => Q'.mkPos 9 5 (by decide)
  | 6 => Q'.mkPos 36 25 (by decide)
  | 7 => Q'.mkPos 123 100 (by decide)
  | 8 => Q'.mkPos 117 100 (by decide)
  | 9 => Q'.mkPos 119 100 (by decide)
  | _ => Q'.mkPos 23 20 (by decide)

/-- Head weights (exact backward products from `ω_11 = 17/7`). -/
def omegaTab : Nat → Q'
  | 0 => Q'.mkPos 96256076646951 2500000000000 (by decide)
  | 1 => Q'.mkPos 953030461851 25000000000 (by decide)
  | 2 => Q'.mkPos 23244645411 625000000 (by decide)
  | 3 => Q'.mkPos 7748215137 250000000 (by decide)
  | 4 => Q'.mkPos 2582738379 125000000 (by decide)
  | 5 => Q'.mkPos 7748215137 625000000 (by decide)
  | 6 => Q'.mkPos 860912793 125000000 (by decide)
  | 7 => Q'.mkPos 95656977 20000000 (by decide)
  | 8 => Q'.mkPos 777699 200000 (by decide)
  | 9 => Q'.mkPos 6647 2000 (by decide)
  | _ => Q'.mkPos 391 140 (by decide)

private theorem pos7 (k : Nat) : 0 < k + 7 := Nat.lt_of_lt_of_le (by decide) (Nat.le_add_left 7 k)

/-- Tail `ρ` with `m = k + 7`: `(m+10)(m+1)/(m(m+11))`. -/
def rhoTail (k : Nat) : Q' :=
  Q'.mkPos (((k+17) * (k+8) : Nat) : Int) ((k+7) * (k+18))
    (Nat.mul_pos (pos7 k) (Nat.lt_of_lt_of_le (by decide) (Nat.le_add_left 18 k)))

/-- Tail weight `(m+10)/m`, `m = k + 7`. -/
def omegaTail (k : Nat) : Q' := Q'.mkPos (((k+17) : Nat) : Int) (k+7) (pos7 k)

def usRho (i : Nat) : Q' := if i < 11 then rhoTab i else rhoTail (i - 11)
def usOmega (i : Nat) : Q' := if i < 11 then omegaTab i else omegaTail (i - 11)

theorem tail_weight (k : Nat) : rhoTail k * omegaTail (k+1) ≤ omegaTail k := by
  show (rhoTail k * omegaTail (k+1)).num * ((omegaTail k).den : Int)
    ≤ (omegaTail k).num * ((rhoTail k * omegaTail (k+1)).den : Int)
  rw [Q'.mul_den_cast]
  unfold rhoTail omegaTail
  rw [Q'.mkPos_den, Q'.mkPos_den, Q'.mkPos_den]
  show ((((k+17) * (k+8) : Nat) : Int) * (((k+18) : Nat) : Int)) * (((k+7) : Nat) : Int)
    ≤ (((k+17) : Nat) : Int) * ((((k+7) * (k+18) : Nat) : Int) * (((k+8) : Nat) : Int))
  rw [← Int.natCast_mul, ← Int.natCast_mul, ← Int.natCast_mul, ← Int.natCast_mul]
  exact Int.ofNat_le.mpr (Nat.le_of_eq (by ac_rfl))

theorem omegaTail_ge_one (k : Nat) : (1 : Q') ≤ omegaTail k := by
  show (1 : Int) * ((omegaTail k).den : Int) ≤ (omegaTail k).num * 1
  unfold omegaTail
  rw [Q'.mkPos_den, Int.one_mul, Int.mul_one]
  exact Int.ofNat_le.mpr (Nat.add_le_add_left (by decide : 7 ≤ 17) k)

private theorem not_lt_of_le' {a b : Nat} (h : b ≤ a) : ¬ a < b := fun h' =>
  Nat.lt_irrefl a (Nat.lt_of_lt_of_le h' h)

private theorem head_w : ∀ i, i < 11 → usRho i * usOmega (i+1) ≤ usOmega i := by decide
private theorem head_ge_one : ∀ i, i < 11 → (1 : Q') ≤ usOmega i := by decide

theorem us_weight (i : Nat) : usRho i * usOmega (i+1) ≤ usOmega i := by
  by_cases h : i < 11
  · exact head_w i h
  · have hi : 11 ≤ i := Nat.not_lt.mp h
    have e : i + 1 - 11 = (i - 11) + 1 := Nat.succ_sub hi
    unfold usRho usOmega
    rw [if_neg h, if_neg (not_lt_of_le' (Nat.le_succ_of_le hi)), if_neg h, e]
    exact tail_weight (i - 11)

theorem us_omega_ge_one (i : Nat) : (1 : Q') ≤ usOmega i := by
  by_cases h : i < 11
  · exact head_ge_one i h
  · unfold usOmega; rw [if_neg h]; exact omegaTail_ge_one _

/-- `P = ω_0 = 96256076646951/2500000000000`, and `38 < P < 39` (decidable). -/
def usP : Q' := Q'.mkPos 96256076646951 2500000000000 (by decide)

theorem usP_value : usOmega 0 = usP ∧ Q'.ofNat 38 < usP ∧ usP < Q'.ofNat 39 := by decide

/-- **Physical-units spacing bound for the undershooting schedule (PROVED reduction):** under
`hspacing_OPEN : 2·a_{i+1} ≤ ρ_i·a_i` (equivalently, by `2^u ≤ 1+u`, implied by `ℓ_i ≥ 1 - u_i`),
`2ⁿ·a_n ≤ P·a_0` with `P = 96256076646951/2500000000000 ≈ 38.50` for every `n`.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it
would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). Per the
numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover. -/
theorem undershoot_spacing_bound (a : Nat → Q') (ha : ∀ i, (0 : Q') ≤ a i)
    (hspacing_OPEN : ∀ i, Q'.ofNat 2 * a (i+1) ≤ usRho i * a i) (n : Nat) :
    Q'.ofNat (2 ^ n) * a n ≤ usP * a 0 := by
  have h := spacing_bound a usRho usOmega ha us_omega_ge_one hspacing_OPEN us_weight n
  rw [usP_value.1] at h
  exact h

end YMGap.RG.UndershootPhysicalUnits
