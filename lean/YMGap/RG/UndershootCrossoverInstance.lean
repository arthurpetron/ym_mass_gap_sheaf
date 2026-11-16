/-
# Crossover instance on the undershooting schedule, and the floor in physical units

**Label: PROVED reduction (decidable budget). NOT gap evidence. `δ_min = 0` for `ℓ ≤ 1` is only a
NECESSARY condition: it removes the obstruction but does not prove `hafδ`.**

U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it
would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs).

Instance: `undershootSchedule`, `j0 = 0`, `k = 6` crossover steps (`1/64 → … → 779/1000`; per the numerics,
the U(1) transition lies between 1/8 and 1/2, inside the crossover), `s = timeRate = 1/4`, `C = 1/10`,
`η_n = 1/64`, `E = 3/32`. The floor `114517/5000000` is unchanged (`DyadicCrossoverInstance.floor_dy_value`).

Physical units (`undershoot_physical_floor`): with the OPEN spacing hypothesis
`hspacing_OPEN : 2·a_{i+1} ≤ (1+u_i)·a_i`, every `n` has
`floor·a_n ≤ (P·a_0)·latticeMargin_n`, `P = 96256076646951/2500000000000 ≈ 38.50`, i.e.
`latticeMargin_n/a_n ≥ (114517/5000000)/(P·a_0) ≈ 5.95·10⁻⁴/a_0`.

Constructive, no external library; axioms within `propext`, `Quot.sound`.
-/

import YMGap.RG.UndershootPhysicalUnits
import YMGap.RG.DyadicCrossoverInstance

namespace YMGap.RG.UndershootCrossoverInstance

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
open YMGap.RG.CrossoverScaleChain (crossPart scaleChain_crossover_floor)
open YMGap.RG.DyadicCrossoverInstance (eDy budget_dy_ok)
open YMGap.RG.UndershootAfSchedule (undershootSchedule undershoot_join)
open YMGap.RG.UndershootPhysicalUnits (usRho usP floor_physical usOmega us_omega_ge_one us_weight usP_value)

/-- Per-step crossover budget `η_n = 1/64` (masked to `0` for `n ≥ 6` by `crossPart`). -/
def etaUS : Nat → Q' := fun _ => Q'.mkPos 1 64 (by decide)

private theorem tail : ∀ m, finSum (crossPart 6 etaUS) (m+6) ≤ eDy
  | 0 => by decide
  | m+1 => by
    have hz : crossPart 6 etaUS (m+6) = 0 := by
      unfold crossPart
      rw [if_neg (Nat.not_lt.mpr (Nat.le_add_left 6 m))]
    show finSum (crossPart 6 etaUS) (m+6) + crossPart 6 etaUS (m+6) ≤ _
    rw [hz]
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (QPoly.q_add_zero_eqv _)) (tail m)

private theorem head : ∀ n, n < 6 → finSum (crossPart 6 etaUS) n ≤ eDy := by decide

/-- **Crossover budget `Σ_{n<6} 1/64 ≤ 3/32` for every prefix (PROVED).**
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it
would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem etaUS_budget (n : Nat) : finSum (crossPart 6 etaUS) n ≤ eDy := by
  by_cases h : n < 6
  · exact head n h
  · have e : n = (n - 6) + 6 := (Nat.sub_add_cancel (Nat.not_lt.mp h)).symm
    rw [e]; exact tail (n - 6)

/-- **The seed at `w_0 = 1/64` (PROVED):** width-uniform contraction at `timeRate`.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it
would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem us_seed (width : Nat) :
    WilsonVacuumSqContraction (undershootSchedule.nome_pos 0)
      (undershootSchedule.nome_lt_one 0) width timeRate :=
  uniformRate_of_guards _ _
    (scGuards_of_le_inv55 (Q'.le_of_lt (undershootSchedule.nome_pos 0)) undershoot_join.1)
    width

/-- **Non-vacuous instance on the undershooting schedule (PROVED reduction):** `j0 = 0`, `k = 6`,
`η_n = 1/64`, `s = 1/4`, `C = 1/10`, `E = 3/32`. The floor is `114517/5000000 > 0`
(`DyadicCrossoverInstance.floor_dy_value`). What remains is exactly `hcross_OPEN` (6 dyadic crossover
steps), `hafδ_OPEN`, `hupper_OPEN` and `hschur_OPEN`.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it
would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem undershoot_crossover_instance :
    let ns := undershootSchedule
    ∀ (width : Nat → Nat) (delta : Nat → Q')
      (_hd0 : ∀ n, (0 : Q') ≤ delta n) (_hd1 : ∀ n, delta n ≤ (1 : Q'))
      (_hcross_OPEN : ∀ n, n < 6 → delta n ≤ etaUS n)
      (_hafδ_OPEN : ∀ n, 6 ≤ n →
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
    scaleChain_crossover_floor undershootSchedule width 0 6 timeRate _ _ delta etaUS
      (Q'.le_of_lt timeRate_positive) timeRate_lt_one (by decide) (by decide) hd0 hd1 hcross hafδ
      etaUS_budget budget_dy_ok Phi D hupper hschur (us_seed (width 0)) n


/-- **Floor in physical units on the undershooting schedule (PROVED reduction).** All OPEN hypotheses are
named: `hcross_OPEN`, `hafδ_OPEN`, `hupper_OPEN`, `hschur_OPEN` (the crossover instance), plus
`hspacing_OPEN` (`2·a_{i+1} ≤ (1+u_i)·a_i`; by convexity `2^u ≤ 1+u`, implied by `ℓ_i ≥ 1 − u_i`) and
`hmargin_OPEN` (`latticeMargin_n ≥ 0`; it follows from `floor > 0` and the instance, but that step is not
formalised here). Conclusion: `floor·a_n ≤ (P·a_0)·latticeMargin_n` with `P ≈ 38.50`.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it
would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem undershoot_physical_floor :
    let ns := undershootSchedule
    ∀ (width : Nat → Nat) (delta : Nat → Q')
      (_hd0 : ∀ n, (0 : Q') ≤ delta n) (_hd1 : ∀ n, delta n ≤ (1 : Q'))
      (_hcross_OPEN : ∀ n, n < 6 → delta n ≤ etaUS n)
      (_hafδ_OPEN : ∀ n, 6 ≤ n →
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
      (a : Nat → Q') (_ha : ∀ i, (0 : Q') ≤ a i)
      (_hspacing_OPEN : ∀ i, Q'.ofNat 2 * a (i+1) ≤ usRho i * a i)
      (_hmargin_OPEN : ∀ n, (0 : Q') ≤ latticeMarginOf (relativeRate timeRate delta) n)
      (n : Nat),
      ((1 : Q') - timeRate) * (timeRate -
          (eDy + Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (0+2))) * a n ≤
        (usP * a 0) * latticeMarginOf (relativeRate timeRate delta) n :=
  fun width delta hd0 hd1 hcross hafδ Phi D hupper hschur a ha hsp hM n => by
    have h := floor_physical a usRho usOmega (latticeMarginOf (relativeRate timeRate delta)) _ ha
      us_omega_ge_one hsp us_weight n (hM n)
      (undershoot_crossover_instance width delta hd0 hd1 hcross hafδ Phi D hupper hschur n).2
    rw [usP_value.1] at h
    exact h

end YMGap.RG.UndershootCrossoverInstance
