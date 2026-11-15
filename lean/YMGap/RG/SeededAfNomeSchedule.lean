/-
# `seededAfNomeSchedule`: a `NomeSchedule` that starts inside the proved strong-coupling region

**Label: PROVED construction + PROVED seed + OPEN crossover inputs. NOT gap evidence.**
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs).
Convention: repo nome `w` matches the Numerics `t = -4 ln w`; U(1) is confined only for
w ≤ 1/8 and already Coulomb (massless) at w = 1/2 and 0.5145 (YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved).

What `NomeSchedule` requires (`BF4WilsonAllNomeDyadicSmoothedTrajectory.lean:266`): `nome`, `0 < w_j`,
`w_j < 1`, `w_j ≤ w_{j+1}`, and `w_j → 1` with an explicit `limitModulus`. Nothing else: no step
relation `w_{j+1} = f(w_j)`, no AF growth rate and no lower bound on `w_0`. So `w_0 ≥ 1/2` is a
property of the three concrete schedules, not of the structure (`seeded_nome_zero_lt_half`).
The r49 capstone `scaleChain_afBudget_floor` takes an arbitrary `NomeSchedule`; its AF content is the
FIXED function `afGap (j0+k)` in `hafδ_OPEN` and the budget `C·afA²/(j0+2)`, both independent of the
schedule.

`seededNome w0 j0 j := if j ≤ j0 then w0 else afNomeSchedule.nome j`: constant `w0 ≤ 1/55` up to the
seed index `j0`, then the AF schedule at the SAME index (so for `j > j0` its gap is `afGap j`, the
gap `hafδ_OPEN` refers to). The jump at `j0 → j0+1` goes from `w0` to `w_{j0+1}^{AF} ≥ 0.5145`. The
structure allows such a jump. All the physics of the crossover sits in the OPEN inputs `hupper_OPEN`,
`hschur_OPEN`, `hafδ_OPEN` at `n = 0, 1, …` (`seeded_r49_floor`). In this intermediate-coupling crossover,
per the YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved,
the 4D U(1) transition lies between w = 1/8 and w = 1/2, inside the crossover; a uniform gap past w ≈ 1/8 needs NON-ABELIAN input, and nothing here supplies it.

Constructive, no external library; axioms within `propext`, `Quot.sound`.
-/

import YMGap.RG.StrongCouplingNomeThreshold

namespace YMGap.RG.SeededAfNomeSchedule

set_option autoImplicit false

open YMGap.Constructive YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (VacuumComplement)
open YMGap.Continuum.BF4WilsonAllNomeExprMixRateContraction (WilsonVacuumSqContraction)
open YMGap.Continuum.BF4WilsonAllNomeRGDissipationBudget (relativeRate)
open YMGap.Continuum.BF4WilsonAllNomeRGStepComposition (latticeMarginOf)
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory (afGap afA afNomeSchedule)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory (NomeSchedule)
open YMGap.RG.RelativeDissipationScaleChain (SchurDecomposition inv)
open YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay (timeRate)
open YMGap.RG.UniformSeedGap (UniformSeedGap scaleChain_afBudget_floor_of_uniformSeedGap)
open YMGap.RG.StrongCouplingNomeThreshold (inv55 uniformSeedGap_of_le_inv55)

/-- Seed region constant up to `j0`, then the AF schedule at the same index. -/
def seededNome (w0 : Q') (j0 j : Nat) : Q' := if j ≤ j0 then w0 else afNomeSchedule.nome j

private theorem le_af_of_le_inv55 {w0 : Q'} (h : w0 ≤ inv55) : ∀ k, w0 ≤ afNomeSchedule.nome k
  | 0 => Q'.le_trans' _ _ _ h (by decide)
  | k+1 => Q'.le_trans' _ _ _ (le_af_of_le_inv55 h k) (afNomeSchedule.nome_mono k)

private theorem seeded_mono {w0 : Q'} (h : w0 ≤ inv55) (j0 j : Nat) :
    seededNome w0 j0 j ≤ seededNome w0 j0 (j+1) := by
  unfold seededNome
  by_cases h1 : j+1 ≤ j0
  · rw [if_pos (Nat.le_trans (Nat.le_succ j) h1), if_pos h1]
    exact Q'.le_refl' _
  · rw [if_neg h1]
    by_cases h0 : j ≤ j0
    · rw [if_pos h0]
      exact le_af_of_le_inv55 h (j+1)
    · rw [if_neg h0]
      exact afNomeSchedule.nome_mono j

/-- **The seeded schedule is a `NomeSchedule` (PROVED)** for any `0 < w0 ≤ 1/55`.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
def seededSchedule (w0 : Q') (hw0 : (0 : Q') < w0) (h55 : w0 ≤ inv55) (j0 : Nat) : NomeSchedule where
  nome := seededNome w0 j0
  nome_pos := fun j => by
    unfold seededNome
    by_cases h : j ≤ j0
    · rw [if_pos h]; exact hw0
    · rw [if_neg h]; exact afNomeSchedule.nome_pos j
  nome_lt_one := fun j => by
    unfold seededNome
    by_cases h : j ≤ j0
    · rw [if_pos h]; exact Q'.lt_of_le_of_lt h55 (by decide)
    · rw [if_neg h]; exact afNomeSchedule.nome_lt_one j
  nome_mono := seeded_mono h55 j0
  limitModulus := fun eps => (j0+1) + afNomeSchedule.limitModulus eps
  nome_limit := fun eps he j hj => by
    unfold seededNome
    have hj0 : ¬ j ≤ j0 := fun h =>
      Nat.not_succ_le_self j0 (Nat.le_trans (Nat.le_trans (Nat.le_add_right _ _) hj) h)
    rw [if_neg hj0]
    exact afNomeSchedule.nome_limit eps he j (Nat.le_trans (Nat.le_add_left _ _) hj)

/-- `w0 = 1/64`. -/
def inv64 : Q' := Q'.mkPos 1 64 (by decide)

/-- **`seededAfNomeSchedule j0`: start at `1/64`, join `afNomeSchedule` after `j0` (PROVED).**
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
def seededAfNomeSchedule (j0 : Nat) : NomeSchedule :=
  seededSchedule inv64 (by decide) (by decide) j0

/-- **`w_0 ≥ 1/2` is NOT forced by `NomeSchedule` (PROVED):** `w_0 = 1/64`.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem seeded_nome_zero_lt_half (j0 : Nat) :
    (seededAfNomeSchedule j0).nome 0 < HalfPow.half := by
  change seededNome inv64 j0 0 < HalfPow.half
  unfold seededNome
  rw [if_pos (Nat.zero_le j0)]
  decide

/-- Every index up to `j0` lies in the proved region `w ≤ 1/55`.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem seeded_nome_le_inv55 (j0 j : Nat) (hj : j ≤ j0) :
    (seededAfNomeSchedule j0).nome j ≤ inv55 := by
  change seededNome inv64 j0 j ≤ inv55
  unfold seededNome
  rw [if_pos hj]
  decide

/-- For `j > j0` the schedule IS the AF schedule (gap `afGap j`).
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem seeded_nome_af (j0 j : Nat) (hj : ¬ j ≤ j0) :
    (seededAfNomeSchedule j0).nome j = afNomeSchedule.nome j := by
  change seededNome inv64 j0 j = _
  unfold seededNome
  rw [if_neg hj]

/-- **`UniformSeedGap` at the seed index `j0` for every `budget < timeRate = 1/4` (PROVED).**
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem seeded_uniformSeedGap (j0 : Nat) (budget : Q') (hb : budget < timeRate) :
    UniformSeedGap ((seededAfNomeSchedule j0).nome_pos j0)
      ((seededAfNomeSchedule j0).nome_lt_one j0) budget :=
  uniformSeedGap_of_le_inv55 _ _ (seeded_nome_le_inv55 j0 j0 (Nat.le_refl j0)) budget hb

/-- **r49 budget below `timeRate` (decidable):** `C = 1/10`, `j0 = 8`: `0.1·afA²/10 ≈ 0.038 < 1/4`.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem seeded_budget_example :
    Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (8+2) < timeRate := by decide

/-- **What is left (PROVED reduction).** On `seededAfNomeSchedule j0`, with the budget condition, the r49
floor holds once `hafδ_OPEN`, `hupper_OPEN`, `hschur_OPEN` are supplied at every `n`; at `n = 0` they
cross from `w = 1/64` to `w ≥ 0.5145` (the crossover; per the YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved,
the 4D U(1) transition lies between w = 1/8 and w = 1/2, inside the crossover). U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem seeded_r49_floor (j0 : Nat) (C : Q') (hC : (0 : Q') ≤ C)
    (hbudget : C * (afA * afA) * inv (j0+2) < timeRate) :
    let ns := seededAfNomeSchedule j0
    ∃ s : Q', (0 : Q') < ((1 : Q') - s) * (s - C * (afA * afA) * inv (j0+2)) ∧
      ∀ (width : Nat → Nat) (delta : Nat → Q')
        (_hd0 : ∀ n, (0 : Q') ≤ delta n) (_hd1 : ∀ n, delta n ≤ (1 : Q'))
        (_hafδ_OPEN : ∀ k, delta k ≤ C * (afGap (j0+k) * afGap (j0+k)))
        (Phi : ∀ n, VacuumComplement (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1))
            (width := width (j0+n+1)) →
          VacuumComplement (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (width := width (j0+n)))
        (D : ∀ n, VacuumComplement (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1))
            (width := width (j0+n+1)) → RC)
        (_hupper_OPEN : ∀ n y, RCle
          (completedInner (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (Phi n y).val (Phi n y).val)
          (completedInner (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1)) y.val y.val))
        (_hschur_OPEN : ∀ n, SchurDecomposition (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1))
          (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (width (j0+n+1)) (width (j0+n))
          (delta n) (Phi n) (D n))
        (n : Nat),
        WilsonVacuumSqContraction (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (width (j0+n))
            (relativeRate s delta n) ∧
          ((1 : Q') - s) * (s - C * (afA * afA) * inv (j0+2)) ≤
            Q'.ofNat (2 ^ n) * latticeMarginOf (relativeRate s delta) n :=
  scaleChain_afBudget_floor_of_uniformSeedGap (seededAfNomeSchedule j0) j0 C hC
    (seeded_uniformSeedGap j0 _ hbudget)

end YMGap.RG.SeededAfNomeSchedule
