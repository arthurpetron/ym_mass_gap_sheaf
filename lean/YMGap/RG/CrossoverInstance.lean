/-
# Non-vacuity of `scaleChain_crossover_floor` and why the relaxation is needed

**Label: PROVED decidable instance + PROVED converse. NOT gap evidence.**
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs).
Convention: repo nome `w` matches the Numerics `t = -4 ln w`; U(1) is confined only for
w ≤ 1/8 and already Coulomb (massless) at w = 1/2 and 0.5145 (YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved).

Instance: `smoothAfNomeSchedule 8 4` (`w0 = 1/64`, `j0 = 8`, `k = 4` crossover steps), seed
`s = timeRate = 1/4` (the witness inside `seeded_uniformSeedGap`, here taken directly from
`uniformRate_of_guards` at `w_8 = 1/64 ≤ 1/55`), `C = 1/10`.
* `η_n = 1/16` FAILS: `E = 4·(1/16) = 1/4 = s`, so `E + B < s` is false (`budget_eta16_fails`).
* `η_n = 1/32` WORKS: `E = 1/8`, `B = (1/10)·afA²/11 = 942841/27500000 ≈ 0.0343`,
  floor `(3/4)(1/4 - 1/8 - B) = 7483977/110000000 ≈ 0.068 > 0`.
* Converse: the old single-step budget `hafδ` at `n = 0` forces
  `δ_0 ≤ (1/10)·afGap(8)² = 13804135081/6440062500000 ≈ 0.00214 < 1/32`.

Constructive, no external library; axioms within `propext`, `Quot.sound`.
-/

import YMGap.RG.CrossoverScaleChain

namespace YMGap.RG.CrossoverInstance

set_option autoImplicit false

open YMGap.Constructive YMGap.Constructive.CReal
open YMGap.Constructive.RationalTail (finSum)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (VacuumComplement)
open YMGap.Continuum.BF4WilsonAllNomeExprMixRateContraction (WilsonVacuumSqContraction)
open YMGap.Continuum.BF4WilsonAllNomeRGDissipationBudget (relativeRate)
open YMGap.Continuum.BF4WilsonAllNomeRGStepComposition (latticeMarginOf)
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory (afGap afA)
open YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay (timeRate timeRate_positive timeRate_lt_one)
open YMGap.RG.RelativeDissipationScaleChain (SchurDecomposition inv)
open YMGap.RG.StrongCouplingNomeThreshold (uniformRate_of_guards scGuards_of_le_inv55)
open YMGap.RG.SmoothSeededAfNomeSchedule (smoothAfNomeSchedule smooth_nome_le_inv55)
open YMGap.RG.CrossoverScaleChain (crossPart scaleChain_crossover_floor crossover_floor_pos)

/-- Constant crossover budget `η_n = 1/32`. -/
def eta32 : Nat → Q' := fun _ => Q'.mkPos 1 32 (by decide)

private theorem tail : ∀ m, finSum (crossPart 4 eta32) (m+4) ≤ Q'.mkPos 1 8 (by decide)
  | 0 => by decide
  | m+1 => by
    have hz : crossPart 4 eta32 (m+4) = 0 := by
      unfold crossPart
      rw [if_neg (Nat.not_lt.mpr (Nat.le_add_left 4 m))]
    show finSum (crossPart 4 eta32) (m+4) + crossPart 4 eta32 (m+4) ≤ _
    rw [hz]
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (QPoly.q_add_zero_eqv _)) (tail m)

/-- **Crossover budget `∑_{n<4} 1/32 ≤ 1/8` for every prefix (PROVED).**
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem eta32_budget : ∀ n, finSum (crossPart 4 eta32) n ≤ Q'.mkPos 1 8 (by decide)
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | 3 => by decide
  | m+4 => tail m

/-- **`η = 1/16` does not fit (decidable):** `1/4 + B < 1/4` is false.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem budget_eta16_fails :
    ¬ (Q'.mkPos 1 4 (by decide) + Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (8+2) < timeRate) := by
  decide

/-- **`η = 1/32` fits (decidable):** `1/8 + B < 1/4`.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem budget_eta32_ok :
    Q'.mkPos 1 8 (by decide) + Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (8+2) < timeRate := by
  decide

/-- **The instance floor is `7483977/110000000 > 0` (decidable).**
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem floor_eta32_value :
    Q'.eqv (((1 : Q') - timeRate) * (timeRate -
        (Q'.mkPos 1 8 (by decide) + Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (8+2))))
      (Q'.mkPos 7483977 110000000 (by decide)) ∧
    (0 : Q') < ((1 : Q') - timeRate) * (timeRate -
        (Q'.mkPos 1 8 (by decide) + Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (8+2))) :=
  ⟨by decide, crossover_floor_pos _ _ timeRate_lt_one budget_eta32_ok⟩

/-- **The seed at `w_8 = 1/64` (PROVED):** width-uniform contraction at `timeRate`.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem smooth_seed (width : Nat) :
    WilsonVacuumSqContraction ((smoothAfNomeSchedule 8 4).nome_pos 8)
      ((smoothAfNomeSchedule 8 4).nome_lt_one 8) width timeRate :=
  uniformRate_of_guards _ _
    (scGuards_of_le_inv55 (Q'.le_of_lt ((smoothAfNomeSchedule 8 4).nome_pos 8))
      (smooth_nome_le_inv55 8 4 8 (Nat.le_refl 8))) width

/-- **Non-vacuous instance of `scaleChain_crossover_floor` (PROVED reduction):** `k = 4`, `η = 1/32`,
`s = 1/4`, `C = 1/10`, `E = 1/8`; floor `> 0` by `floor_eta32_value`. What remains is exactly
`hcross_OPEN` (crossover; per the YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved,
the 4D U(1) transition lies between w = 1/8 and w = 1/2, inside the crossover), `hafδ_OPEN`, `hupper_OPEN`, `hschur_OPEN`.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem crossover_instance :
    let ns := smoothAfNomeSchedule 8 4
    ∀ (width : Nat → Nat) (delta : Nat → Q')
      (_hd0 : ∀ n, (0 : Q') ≤ delta n) (_hd1 : ∀ n, delta n ≤ (1 : Q'))
      (_hcross_OPEN : ∀ n, n < 4 → delta n ≤ eta32 n)
      (_hafδ_OPEN : ∀ n, 4 ≤ n →
        delta n ≤ Q'.mkPos 1 10 (by decide) * (afGap (8+n) * afGap (8+n)))
      (Phi : ∀ n, VacuumComplement (ns.nome_pos (8+n+1)) (ns.nome_lt_one (8+n+1))
          (width := width (8+n+1)) →
        VacuumComplement (ns.nome_pos (8+n)) (ns.nome_lt_one (8+n)) (width := width (8+n)))
      (D : ∀ n, VacuumComplement (ns.nome_pos (8+n+1)) (ns.nome_lt_one (8+n+1))
          (width := width (8+n+1)) → RC)
      (_hupper_OPEN : ∀ n y, RCle
        (completedInner (ns.nome_pos (8+n)) (ns.nome_lt_one (8+n)) (Phi n y).val (Phi n y).val)
        (completedInner (ns.nome_pos (8+n+1)) (ns.nome_lt_one (8+n+1)) y.val y.val))
      (_hschur_OPEN : ∀ n, SchurDecomposition (ns.nome_pos (8+n+1)) (ns.nome_lt_one (8+n+1))
        (ns.nome_pos (8+n)) (ns.nome_lt_one (8+n)) (width (8+n+1)) (width (8+n))
        (delta n) (Phi n) (D n))
      (n : Nat),
      WilsonVacuumSqContraction (ns.nome_pos (8+n)) (ns.nome_lt_one (8+n)) (width (8+n))
          (relativeRate timeRate delta n) ∧
        ((1 : Q') - timeRate) * (timeRate -
            (Q'.mkPos 1 8 (by decide) + Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (8+2))) ≤
          Q'.ofNat (2 ^ n) * latticeMarginOf (relativeRate timeRate delta) n :=
  fun width delta hd0 hd1 hcross hafδ Phi D hupper hschur n =>
    scaleChain_crossover_floor (smoothAfNomeSchedule 8 4) width 8 4 timeRate _ _ delta eta32
      (Q'.le_of_lt timeRate_positive) timeRate_lt_one (by decide) (by decide) hd0 hd1 hcross hafδ
      eta32_budget budget_eta32_ok Phi D hupper hschur (smooth_seed (width 8)) n

/-- **Converse: the old single-step budget at `n = 0` (exact, decidable):**
`(1/10)·afGap(8)² = 13804135081/6440062500000 ≈ 0.00214`, strictly below `η_0 = 1/32`.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem old_first_step_bound :
    Q'.eqv (Q'.mkPos 1 10 (by decide) * (afGap 8 * afGap 8))
      (Q'.mkPos 13804135081 6440062500000 (by decide)) ∧
    Q'.mkPos 1 10 (by decide) * (afGap 8 * afGap 8) < Q'.mkPos 1 32 (by decide) :=
  ⟨by decide, by decide⟩

/-- **Why the relaxation is needed (PROVED):** under the old r49 budget (`hafδ` from `n = 0`,
`j0 = 8`, `C = 1/10`), the first crossover defect must be `< 1/32`; the crossover budget allows `1/32`.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem old_budget_forces_small_first_step (delta : Nat → Q')
    (hafδ_old : ∀ k, delta k ≤ Q'.mkPos 1 10 (by decide) * (afGap (8+k) * afGap (8+k))) :
    delta 0 < Q'.mkPos 1 32 (by decide) :=
  Q'.lt_of_le_of_lt (hafδ_old 0) old_first_step_bound.2

end YMGap.RG.CrossoverInstance
