/-
# Crossover instance on the two-loop schedule (join at index 6, no offset)

**Label: PROVED decidable instance of `scaleChain_crossover_floor`. NOT gap evidence.**

U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it
would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs).

Instance: `twoLoopSchedule` (`TwoLoopAfSchedule.lean`), `j0 = 0`, `k = 6` crossover steps
(`1/64 → … → 147/200 → 779/1000`; per the numerics, the U(1) transition lies between 1/8 and 1/2,
inside the crossover), then `hafδ_OPEN` from index 6 on the two-loop part. Seed `s = timeRate = 1/4`
at `w_0 = 1/64 ≤ 1/55`, `C = 1/10`, `η_n = 1/64` (`n < 6`).
* `E = 6/64 = 3/32 = eDy`; `B = (1/10)·afA²·inv 2 ≈ 0.12571`. `E + B < s` reuses `budget_dy_ok`.
  The floor `114517/5000000` is unchanged (`floor_dy_value`). `η_n = 1/48` (`E = 1/8`) does not fit
  (`budget_dy96_fails`, the same inequality).
* The `hafδ_OPEN` budget `C·afGap(n)²` uses the `afGap` index, not the schedule nome. Numerically
  `afGap n / (1 - w_n)` is 0.81 at n = 6, 0.89 at n = 14, 0.94 at n = 30 and 0.98 at n = 100, tending
  to 1. So the budget is somewhat tighter than `C·(1 - w_n)²` measured on the actual two-loop nome.
  It remains an OPEN hypothesis (cf. `AfDeltaJumpAllowance.lean`).

Constructive, no external library; axioms within `propext`, `Quot.sound`.
-/

import YMGap.RG.TwoLoopAfSchedule
import YMGap.RG.DyadicCrossoverInstance

namespace YMGap.RG.TwoLoopCrossoverInstance

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
open YMGap.RG.TwoLoopAfSchedule (twoLoopSchedule twoLoop_join)

/-- Per-step crossover budget `η_n = 1/64` (masked to `0` for `n ≥ 6` by `crossPart`). -/
def etaTL : Nat → Q' := fun _ => Q'.mkPos 1 64 (by decide)

private theorem tail : ∀ m, finSum (crossPart 6 etaTL) (m+6) ≤ eDy
  | 0 => by decide
  | m+1 => by
    have hz : crossPart 6 etaTL (m+6) = 0 := by
      unfold crossPart
      rw [if_neg (Nat.not_lt.mpr (Nat.le_add_left 6 m))]
    show finSum (crossPart 6 etaTL) (m+6) + crossPart 6 etaTL (m+6) ≤ _
    rw [hz]
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (QPoly.q_add_zero_eqv _)) (tail m)

private theorem head : ∀ n, n < 6 → finSum (crossPart 6 etaTL) n ≤ eDy := by decide

/-- **Crossover budget `Σ_{n<6} 1/64 ≤ 3/32` for every prefix (PROVED).**
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it
would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem etaTL_budget (n : Nat) : finSum (crossPart 6 etaTL) n ≤ eDy := by
  by_cases h : n < 6
  · exact head n h
  · have e : n = (n - 6) + 6 := (Nat.sub_add_cancel (Nat.not_lt.mp h)).symm
    rw [e]; exact tail (n - 6)

/-- **The seed at `w_0 = 1/64` (PROVED):** width-uniform contraction at `timeRate`.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it
would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem tl_seed (width : Nat) :
    WilsonVacuumSqContraction (twoLoopSchedule.nome_pos 0)
      (twoLoopSchedule.nome_lt_one 0) width timeRate :=
  uniformRate_of_guards _ _
    (scGuards_of_le_inv55 (Q'.le_of_lt (twoLoopSchedule.nome_pos 0)) twoLoop_join.1)
    width

/-- **Non-vacuous instance on the two-loop schedule (PROVED reduction):** `j0 = 0`, `k = 6`,
`η_n = 1/64`, `s = 1/4`, `C = 1/10`, `E = 3/32`. The floor is `114517/5000000 > 0`
(`DyadicCrossoverInstance.floor_dy_value`). What remains is exactly `hcross_OPEN` (6 dyadic crossover
steps), `hafδ_OPEN`, `hupper_OPEN` and `hschur_OPEN`.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it
would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem twoLoop_crossover_instance :
    let ns := twoLoopSchedule
    ∀ (width : Nat → Nat) (delta : Nat → Q')
      (_hd0 : ∀ n, (0 : Q') ≤ delta n) (_hd1 : ∀ n, delta n ≤ (1 : Q'))
      (_hcross_OPEN : ∀ n, n < 6 → delta n ≤ etaTL n)
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
    scaleChain_crossover_floor twoLoopSchedule width 0 6 timeRate _ _ delta etaTL
      (Q'.le_of_lt timeRate_positive) timeRate_lt_one (by decide) (by decide) hd0 hd1 hcross hafδ
      etaTL_budget budget_dy_ok Phi D hupper hschur (tl_seed (width 0)) n

end YMGap.RG.TwoLoopCrossoverInstance
