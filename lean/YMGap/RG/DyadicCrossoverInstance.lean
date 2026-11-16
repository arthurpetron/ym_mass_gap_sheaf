/-
# Crossover instance on the dyadic schedule (no scale-skipping step)

**Label: PROVED decidable instance of `scaleChain_crossover_floor`. NOT gap evidence.**
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs).
Convention: repo nome `w` matches the Numerics `t = -4 ln w`; U(1) is confined only for
w ≤ 1/8 and already Coulomb (massless) at w = 1/2 and 0.5145 (YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved).

Instance: `dyadicCrossoverSchedule` (`j0 = 0`, `k = 12`, every step one dyadic RG step), seed
`s = timeRate = 1/4` at `w_0 = 1/64 ≤ 1/55`, `C = 1/10`, per-step `η_n = 1/128` (`n < 12`).
* `E = Σ_{n<12} η_n = 3/32`; `B = (1/10)·afA²·inv 2 = (1/10)·afA²/3 = 942841/7500000 ≈ 0.12571`
  (`inv m = 1/(m+1)`).
* `E + B < s` (`budget_dy_ok`); floor `(3/4)(1/4 - 3/32 - B) = 114517/5000000 ≈ 0.0229 > 0`.
* `η_n = 1/96` does NOT fit (`budget_dy96_fails`): `1/8 + B ≥ 1/4`.

Constructive, no external library; axioms within `propext`, `Quot.sound`.
-/

import YMGap.RG.DyadicCrossoverSchedule
import YMGap.RG.CrossoverScaleChain

namespace YMGap.RG.DyadicCrossoverInstance

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
open YMGap.RG.DyadicCrossoverSchedule (dyadicCrossoverSchedule dy_nome_zero_le_inv55)
open YMGap.RG.CrossoverScaleChain (crossPart scaleChain_crossover_floor crossover_floor_pos)

/-- Per-step crossover budget: `η_n = 1/128` for each of the 12 steps `n < 12` (masked to `0` beyond
by `crossPart`). -/
def etaDy : Nat → Q' := fun _ => Q'.mkPos 1 128 (by decide)

/-- `E = 3/32`. -/
def eDy : Q' := Q'.mkPos 3 32 (by decide)

private theorem tail : ∀ m, finSum (crossPart 12 etaDy) (m+12) ≤ eDy
  | 0 => by decide
  | m+1 => by
    have hz : crossPart 12 etaDy (m+12) = 0 := by
      unfold crossPart
      rw [if_neg (Nat.not_lt.mpr (Nat.le_add_left 12 m))]
    show finSum (crossPart 12 etaDy) (m+12) + crossPart 12 etaDy (m+12) ≤ _
    rw [hz]
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (QPoly.q_add_zero_eqv _)) (tail m)

private theorem head : ∀ n, n < 12 → finSum (crossPart 12 etaDy) n ≤ eDy := by decide

/-- **Crossover budget `Σ_{n<12} 1/128 ≤ 3/32` for every prefix (PROVED).**
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem etaDy_budget (n : Nat) : finSum (crossPart 12 etaDy) n ≤ eDy := by
  by_cases h : n < 12
  · exact head n h
  · have e : n = (n - 12) + 12 := (Nat.sub_add_cancel (Nat.not_lt.mp h)).symm
    rw [e]; exact tail (n - 12)

/-- **`E + B < s` (decidable):** `3/32 + (1/10)·afA²·inv 2 < 1/4`.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem budget_dy_ok :
    eDy + Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (0+2) < timeRate := by
  decide

/-- **`η_n = 1/96` does not fit (decidable):** `1/8 + B < 1/4` is false.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem budget_dy96_fails :
    ¬ (Q'.mkPos 1 8 (by decide) + Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (0+2) < timeRate) := by
  decide

/-- **The floor is `114517/5000000 > 0` (decidable value, PROVED positivity).**
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem floor_dy_value :
    Q'.eqv (((1 : Q') - timeRate) * (timeRate -
        (eDy + Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (0+2))))
      (Q'.mkPos 114517 5000000 (by decide)) ∧
    (0 : Q') < ((1 : Q') - timeRate) * (timeRate -
        (eDy + Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (0+2))) :=
  ⟨by decide, crossover_floor_pos _ _ timeRate_lt_one budget_dy_ok⟩

/-- **Side check (decidable):** at the join (`n = 12`, `w = afNome 12 ≈ 0.8875`) the conclusion only
forces `1 - r_12 ≥ floor/2^12 ≈ 5.6·10⁻⁶`, below the literature estimate `0.0024` (Numerics).
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem forced_margin_below_literature :
    Q'.mkPos 114517 5000000 (by decide) < Q'.ofNat (2 ^ 12) * Q'.mkPos 24 10000 (by decide) := by
  decide

/-- **The seed at `w_0 = 1/64` (PROVED):** width-uniform contraction at `timeRate`.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem dy_seed (width : Nat) :
    WilsonVacuumSqContraction (dyadicCrossoverSchedule.nome_pos 0)
      (dyadicCrossoverSchedule.nome_lt_one 0) width timeRate :=
  uniformRate_of_guards _ _
    (scGuards_of_le_inv55 (Q'.le_of_lt (dyadicCrossoverSchedule.nome_pos 0)) dy_nome_zero_le_inv55)
    width

/-- **Non-vacuous instance on the dyadic schedule (PROVED reduction):** `j0 = 0`, `k = 12`,
`η_n = 1/128`, `s = 1/4`, `C = 1/10`, `E = 3/32`; floor `114517/5000000 > 0`. What remains is
exactly `hcross_OPEN` (12 dyadic crossover steps; per the numerics, the U(1) transition lies
between 1/8 and 1/2, inside the crossover), `hafδ_OPEN`, `hupper_OPEN`, `hschur_OPEN`.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem dyadic_crossover_instance :
    let ns := dyadicCrossoverSchedule
    ∀ (width : Nat → Nat) (delta : Nat → Q')
      (_hd0 : ∀ n, (0 : Q') ≤ delta n) (_hd1 : ∀ n, delta n ≤ (1 : Q'))
      (_hcross_OPEN : ∀ n, n < 12 → delta n ≤ etaDy n)
      (_hafδ_OPEN : ∀ n, 12 ≤ n →
        delta n ≤ Q'.mkPos 1 10 (by decide) * (afGap (0+n) * afGap (0+n)))
      (Phi : ∀ n, VacuumComplement (ns.nome_pos (0+n+1)) (ns.nome_lt_one (0+n+1))
          (width := width (0+n+1)) →
        VacuumComplement (ns.nome_pos (0+n)) (ns.nome_lt_one (0+n)) (width := width (0+n)))
      (D : ∀ n, VacuumComplement (ns.nome_pos (0+n+1)) (ns.nome_lt_one (0+n+1))
          (width := width (0+n+1)) → RC)
      (_hupper_OPEN : ∀ n y, RCle
        (completedInner (ns.nome_pos (0+n)) (ns.nome_lt_one (0+n)) (Phi n y).val (Phi n y).val)
        (completedInner (ns.nome_pos (0+n+1)) (ns.nome_lt_one (0+n+1)) y.val y.val))
      (_hschur_OPEN : ∀ n, SchurDecomposition (ns.nome_pos (0+n+1)) (ns.nome_lt_one (0+n+1))
        (ns.nome_pos (0+n)) (ns.nome_lt_one (0+n)) (width (0+n+1)) (width (0+n))
        (delta n) (Phi n) (D n))
      (n : Nat),
      WilsonVacuumSqContraction (ns.nome_pos (0+n)) (ns.nome_lt_one (0+n)) (width (0+n))
          (relativeRate timeRate delta n) ∧
        ((1 : Q') - timeRate) * (timeRate -
            (eDy + Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (0+2))) ≤
          Q'.ofNat (2 ^ n) * latticeMarginOf (relativeRate timeRate delta) n :=
  fun width delta hd0 hd1 hcross hafδ Phi D hupper hschur n =>
    scaleChain_crossover_floor dyadicCrossoverSchedule width 0 12 timeRate _ _ delta etaDy
      (Q'.le_of_lt timeRate_positive) timeRate_lt_one (by decide) (by decide) hd0 hd1 hcross hafδ
      etaDy_budget budget_dy_ok Phi D hupper hschur (dy_seed (width 0)) n

end YMGap.RG.DyadicCrossoverInstance
