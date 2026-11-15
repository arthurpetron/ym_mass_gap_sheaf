/-
# `UniformSeedGap`: the honest (OPEN) width-uniform seed input of the r49 scale chain

**Label: OPEN hypothesis interface. NOT gap evidence; NOT a proof of the hypothesis.**

`MixRateSeedWidthNoGo` shows the only PROVED seed (`mixRate`) gives a floor
`(1 - seed)(seed - Dq)` that tends to `0` with the width. The replacement is an explicit
OPEN hypothesis: one rate `s` with `budget < s < 1` and the all-vector vacuum contraction
`WilsonVacuumSqContraction hw0 hw1 width s` at EVERY width.

* `UniformSeedGap hw0 hw1 budget`: OPEN at the nomes `w_j → 1` of AF schedules.
* `uniformSeedGap_existingNome`: PROVED at the strong-coupling pilot nome `w = 1/1024` for every
  `budget < timeRate` (from `existingNome_allNome_strongCoupling`, width-independent `timeRate`);
  `uniformSeedGap_existingNome_afBudget`: the decidable r49 budget `C = 1/10`, `j0 = 8` fits;
  `uniformSeedGap_of_eq_pilot`: any nome equal to `1/1024` inherits it.
* `uniformSeedGap_iff_chainSeedSlot`: it is exactly the seed slot of
  `scaleChain_afBudget_floor` (`hs0`, `hs1`, `hbudget`, `hseed`), quantified uniformly in width.
* `scaleChain_afBudget_floor_of_uniformSeedGap`: from it, ONE width-independent `s` with a
  strictly positive floor `(1-s)(s-Dq) > 0` feeds the r49 capstone for EVERY width function,
  still conditional on `hupper_OPEN`, `hschur_OPEN`, `hafδ_OPEN`.
* `mixRate_cannot_witness_uniformSeed`: the mixRate route cannot supply such an `s`.

SCOPE NOTE (honest): the r49 output is a LOWER margin `2^n (1 - r_n) ≥ floor`. The r44 interface
`ScaleDependentShiftedH1Conjecture` asks for retention `r_j·R_j(side_j) ≤ R_j(side_j+1)` and an
UPPER bound `side_j (1 - r_j) ≤ c0`. No theorem here derives r44's input; `UniformSeedGap`
is what the r49 chain's seed slot needs.

Constructive, no external library; axioms within `propext`, `Quot.sound`.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs).
Convention: repo nome `w` matches the Numerics `t = -4 ln w`; U(1) is confined only for
w ≤ 1/8 and already Coulomb (massless) at w = 1/2 and 0.5145 (YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved).
-/

import YMGap.RG.MixRateSeedWidthNoGo

namespace YMGap.RG.UniformSeedGap

set_option autoImplicit false

open YMGap.Constructive YMGap.Constructive.CReal
open YMGap.Constructive.RationalTail (finSum)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (VacuumComplement)
open YMGap.Continuum.BF4WilsonAllNomeExprMixRateContraction (WilsonVacuumSqContraction)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (mixRate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialRateWidthObstruction (no_width_uniform_computed_rate)
open YMGap.Continuum.BF4WilsonAllNomeRGDissipationBudget (relativeRate)
open YMGap.Continuum.BF4WilsonAllNomeRGStepComposition (latticeMarginOf)
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory (afGap afA)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory (NomeSchedule)
open YMGap.RG.RelativeDissipationScaleChain
  (SchurDecomposition scaleChain_afBudget_floor inv inv_nonneg)
open YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay (timeRate)
open YMGap.Continuum.BF4WilsonStrongCouplingUniformRate (existingPilotNome)

/-- **OPEN.** One seed rate `s ∈ (budget, 1)` with the vacuum contraction at every width.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
def UniformSeedGap {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (budget : Q') : Prop :=
  ∃ s : Q', budget < s ∧ s < (1 : Q') ∧ ∀ width : Nat, WilsonVacuumSqContraction hw0 hw1 width s

/-- **Exactly the r49 seed slot, uniform in width (PROVED, for `budget ≥ 0`).**
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem uniformSeedGap_iff_chainSeedSlot {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (budget : Q') (hb : (0 : Q') ≤ budget) :
    UniformSeedGap hw0 hw1 budget ↔
      ∃ s : Q', (0 : Q') ≤ s ∧ s < (1 : Q') ∧ budget < s ∧
        ∀ width : Nat, WilsonVacuumSqContraction hw0 hw1 width s :=
  ⟨fun ⟨s, hbs, hs1, hc⟩ => ⟨s, Q'.le_of_lt (Q'.lt_of_le_of_lt hb hbs), hs1, hbs, hc⟩,
   fun ⟨s, _, hs1, hbs, hc⟩ => ⟨s, hbs, hs1, hc⟩⟩

/-- **`UniformSeedGap` ⇒ one width-independent seed with positive floor for the r49 capstone
(PROVED; still conditional on `hupper_OPEN`, `hschur_OPEN`, `hafδ_OPEN`).**
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem scaleChain_afBudget_floor_of_uniformSeedGap (ns : NomeSchedule) (j0 : Nat) (C : Q')
    (hC : (0 : Q') ≤ C)
    (hU : UniformSeedGap (ns.nome_pos j0) (ns.nome_lt_one j0) (C * (afA * afA) * inv (j0+2))) :
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
            Q'.ofNat (2 ^ n) * latticeMarginOf (relativeRate s delta) n := by
  obtain ⟨s, hbs, hs1, hc⟩ := hU
  have hb : (0 : Q') ≤ C * (afA * afA) * inv (j0+2) :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hC (Q'.mul_nonneg _ _ (by decide) (by decide)))
      (inv_nonneg _)
  have hs0 : (0 : Q') ≤ s := Q'.le_of_lt (Q'.lt_of_le_of_lt hb hbs)
  refine ⟨s, Q'.mul_pos (YMGap.Continuum.HKPos.one_sub_pos hs1)
    (YMGap.Continuum.DefectRecursionPrimary.sub_pos_of_lt hbs), ?_⟩
  intro width delta hd0 hd1 hafδ_OPEN Phi D hupper_OPEN hschur_OPEN n
  exact scaleChain_afBudget_floor ns width j0 s C delta hs0 hs1 hC hd0 hd1 hafδ_OPEN hbs
    Phi D hupper_OPEN hschur_OPEN (hc (width j0)) n

/-- **The proved mixRate route cannot witness a width-uniform seed (PROVED).** No `s < 1`
dominates `mixRate(width)` at every positive width, so monotonicity of the contraction in the
rate cannot lift `wilsonVacuumSqContraction_mixRate` to `UniformSeedGap`.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem mixRate_cannot_witness_uniformSeed {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    ¬ ∃ s : Q', s < (1 : Q') ∧ ∀ width : Nat, 0 < width → mixRate hw0 hw1 width ≤ s :=
  fun ⟨s, hs1, h⟩ => no_width_uniform_computed_rate hw0 hw1 s hs1 h

/-- **PROVED at strong coupling only.** At the pilot nome `w = 1/1024`, `UniformSeedGap` holds for
every `budget < timeRate`. Not an AF statement: every `NomeSchedule` has `w_j → 1`.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem uniformSeedGap_existingNome (budget : Q') (hb : budget < timeRate) :
    ∃ (hw0 : (0 : Q') < existingPilotNome) (hw1 : existingPilotNome < (1 : Q')),
      UniformSeedGap hw0 hw1 budget := by
  obtain ⟨hw0, hw1, _, h1, hc⟩ :=
    YMGap.Continuum.BF4WilsonAllNomeStrongCouplingUniformRate.existingNome_allNome_strongCoupling
  exact ⟨hw0, hw1, timeRate, hb, h1, hc⟩

/-- The r49 example budget `C = 1/10`, `j0 = 8` lies below `timeRate` (decidable).
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem uniformSeedGap_existingNome_afBudget :
    ∃ (hw0 : (0 : Q') < existingPilotNome) (hw1 : existingPilotNome < (1 : Q')),
      UniformSeedGap hw0 hw1 (Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (8+2)) :=
  uniformSeedGap_existingNome _ (by decide)

/-- Any nome literally equal to the pilot nome inherits the strong-coupling witness (e.g. a
`NomeSchedule` whose IR seed index `j0` sits at `w_{j0} = 1/1024`).
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem uniformSeedGap_of_eq_pilot {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (h : w = existingPilotNome) (budget : Q') (hb : budget < timeRate) :
    UniformSeedGap hw0 hw1 budget := by
  subst h
  obtain ⟨_, _, hU⟩ := uniformSeedGap_existingNome budget hb
  exact hU

end YMGap.RG.UniformSeedGap
