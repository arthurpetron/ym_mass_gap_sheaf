import YMGap.RG.Robust3UndershootCrossoverInstance

/-!
# Robust3: discharging `hmargin_OPEN`

`robust3_physical_floor` (c2ad3d15) carried `hmargin_OPEN : ∀ n, 0 ≤ latticeMargin_n`. Its docstring notes it
follows from `floor > 0` and the crossover instance (`floor ≤ 2^n·latticeMargin_n`). This file formalises that
step (`margin_nonneg_of_floor`, `robust3_margin_nonneg`) and restates the physical floor without
`hmargin_OPEN` (`robust3_physical_floor_noMargin`). The remaining OPEN hypotheses are unchanged:
`hcross_OPEN`, `hafδ_OPEN`, `hupper_OPEN`, `hschur_OPEN`, `hspacing_OPEN`. No chart closure is claimed.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it
would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). Per the
numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover.
-/

namespace YMGap.RG.Robust3MarginDischarge

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
open YMGap.RG.Robust3UndershootAfSchedule (robust3UndershootSchedule robust3_join)
open YMGap.RG.UndershootPhysicalUnits (floor_physical)
open YMGap.RG.Robust3UndershootPhysicalUnits (r3Rho r3P)
open YMGap.RG.Robust3UndershootCrossoverInstance (etaR3 robust3_crossover_instance robust3_physical_floor)
open YMGap.RG.DyadicCrossoverInstance (floor_dy_value)

/-- `0 < f` and `f ≤ 2^k·M` give `0 ≤ M`. -/
theorem margin_nonneg_of_floor (f M : Q') (k : Nat) (hf : (0 : Q') < f)
    (h : f ≤ Q'.ofNat (2 ^ k) * M) : (0 : Q') ≤ M := by
  have hfn : (0 : Int) < f.num := by
    have h0 : (0 : Int) * (f.den : Int) < f.num * ((0 : Q').den : Int) := hf
    rw [Int.zero_mul] at h0
    have h1 : ((0 : Q').den : Int) = 1 := rfl
    rw [h1, Int.mul_one] at h0
    exact h0
  have h' : f.num * ((Q'.ofNat (2 ^ k) * M).den : Int)
      ≤ ((2 ^ k : Nat) * M.num) * (f.den : Int) := h
  rw [Q'.mul_den_cast] at h'
  have hpos : (0 : Int) < f.num * (((Q'.ofNat (2 ^ k)).den : Int) * (M.den : Int)) :=
    Int.mul_pos hfn (Int.mul_pos (by exact_mod_cast Q'.den_pos _) (by exact_mod_cast Q'.den_pos _))
  have hA : (0 : Int) < ((2 ^ k : Nat) : Int) * (f.den : Int) :=
    Int.mul_pos (by exact_mod_cast Nat.two_pow_pos k) (by exact_mod_cast Q'.den_pos _)
  refine (Q'.zero_le_iff_num_nonneg M).mpr (Int.le_of_mul_le_mul_left ?_ hA)
  rw [Int.mul_zero]
  have e : ((2 ^ k : Nat) * M.num) * (f.den : Int) = ((2 ^ k : Nat) : Int) * (f.den : Int) * M.num := by
    ac_rfl
  rw [← e]
  exact Int.le_of_lt (Int.lt_of_lt_of_le hpos h')

/-- **`hmargin` discharged (PROVED from the instance)**: under the instance's hypotheses,
`0 ≤ latticeMargin_n` for every `n`. U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it
would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). Per the
numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover. -/
theorem robust3_margin_nonneg :
    let ns := robust3UndershootSchedule
    ∀ (width : Nat → Nat) (delta : Nat → Q')
      (_hd0 : ∀ n, (0 : Q') ≤ delta n) (_hd1 : ∀ n, delta n ≤ (1 : Q'))
      (_hcross_OPEN : ∀ n, n < 6 → delta n ≤ etaR3 n)
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
      (0 : Q') ≤ latticeMarginOf (relativeRate timeRate delta) n :=
  fun width delta hd0 hd1 hcross hafδ Phi D hupper hschur n =>
    margin_nonneg_of_floor _ _ n floor_dy_value.2
      (robust3_crossover_instance width delta hd0 hd1 hcross hafδ Phi D hupper hschur n).2

/-- **Physical floor on Robust3 without `hmargin_OPEN` (PROVED reduction).** Same conclusion as
`robust3_physical_floor`; OPEN: `hcross_OPEN`, `hafδ_OPEN`, `hupper_OPEN`, `hschur_OPEN`,
`hspacing_OPEN`. U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it
would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). Per the
numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover. -/
theorem robust3_physical_floor_noMargin :
    let ns := robust3UndershootSchedule
    ∀ (width : Nat → Nat) (delta : Nat → Q')
      (_hd0 : ∀ n, (0 : Q') ≤ delta n) (_hd1 : ∀ n, delta n ≤ (1 : Q'))
      (_hcross_OPEN : ∀ n, n < 6 → delta n ≤ etaR3 n)
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
      (_hspacing_OPEN : ∀ i, Q'.ofNat 2 * a (i+1) ≤ r3Rho i * a i)
      (n : Nat),
      ((1 : Q') - timeRate) * (timeRate -
          (eDy + Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (0+2))) * a n ≤
        (r3P * a 0) * latticeMarginOf (relativeRate timeRate delta) n :=
  fun width delta hd0 hd1 hcross hafδ Phi D hupper hschur a ha hsp n =>
    robust3_physical_floor width delta hd0 hd1 hcross hafδ Phi D hupper hschur a ha hsp
      (robust3_margin_nonneg width delta hd0 hd1 hcross hafδ Phi D hupper hschur) n

end YMGap.RG.Robust3MarginDischarge
