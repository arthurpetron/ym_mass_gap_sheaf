import YMGap.RG.Robust2UndershootCrossoverInstance
import YMGap.RG.Robust3CrossUniform
import YMGap.RG.Robust3CrossResplitB

/-!
# Corrected off-window spacing table `ρ₀..ρ₄ = 3/2, 3/2, 8/5, 7/4, 7/4` (additive)

**Label: PROVED rational reductions. The spacing hypotheses remain OPEN (physics input with numerical support only).
NOT gap evidence. NOT chart closure.**

`r2RhoTab` (`Robust2UndershootPhysicalUnits.lean`) has head entries `ρ₀..ρ₃ = 101/100, 41/40, 6/5, 3/2`. For the
heat-kernel `a√σ`, the Numerics recheck (`math_frontier_1126/spacing_recheck.md`, FINAL, numerical, NOT proved) needs
`ρ_j ≥ 2·a(w_{j+1})/a(w_j)` with these values:
* j0 `1/64 → 1/8`: 1.414; j1 `1/8 → 7/20`: 1.421; j2 `7/20 → 0.558`: 1.486 ± 0.013;
  j3 `0.558 → 0.67`: 1.633 ± 0.015.
  So `hspacing` with `r2RhoTab` is FALSE for `a√σ` at steps 0–3.
* j4 `0.67 → 0.735`: 1.659 ± 0.004 (χ22). The table value 5/3 holds, but only marginally.
* j5 `0.735 → 0.779`: 1.452. The table value 9/5 holds.

This file adds the approved corrected head `rhoC j = 3/2, 3/2, 8/5, 7/4, 7/4` for `j < 5`. For `j ≥ 5`,
`rhoC j = r2Rho j`, so `ρ₅`, the data window and the tail are unchanged. The tightened alternatives `9/5` and `11/10`
from the recheck's strong-tier section are NOT used here.
The weights `omegaC` are exact backward products: `omegaC j = r2Omega j` for `j ≥ 5`.
The constant changes as follows:
* `PC = omegaC 0 = 4543691803497/15625000000 ≈ 290.796`, replacing `r2P = r3P ≈ 81.918`;
* the head product goes from `12423/4000 = 3.10575` to `441/40 = 11.025`, a factor of ≈ 3.5499.
The rate floors (`floor_dy_value`, `floor_RS_value`) are unchanged: only the `P` constant moves.

The nome heads differ slightly. Robust2 and Robust3 (instance A) use `dyTable 3 = 14/25 = 0.56`; instance B uses
`279/500 = 0.558`. The recheck was measured at 0.558. The corrected values enter only as the `ρ` in OPEN hypotheses.

No existing statement is changed. Every theorem here is a NEW analogue (suffix `_C`) of an existing theorem that uses
`r2Rho`/`r3Rho`/`r2P`/`r3P`. Constructive, no external library; axioms within `propext`, `Quot.sound`.
-/

namespace YMGap.RG.Robust3SpacingCorrected

set_option autoImplicit false

open YMGap.Constructive YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (VacuumComplement completedTime)
open YMGap.Continuum.BF4WilsonAllNomeExprMixRateContraction (WilsonVacuumSqContraction)
open YMGap.Continuum.BF4WilsonAllNomeRGDissipationBudget (relativeRate)
open YMGap.Continuum.BF4WilsonAllNomeRGStepComposition (WilsonVacuumSqTwoStepFactor latticeMarginOf)
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory (afGap afA)
open YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay (timeRate timeRate_positive timeRate_lt_one)
open YMGap.RG.RelativeDissipationScaleChain (SchurDecomposition inv)
open YMGap.RG.DyadicCrossoverInstance (eDy)
open YMGap.RG.UndershootPhysicalUnits (floor_physical spacing_bound)
open YMGap.RG.Robust2UndershootPhysicalUnits (r2Rho r2Omega r2P r2P_value r2_weight r2_omega_ge_one)
open YMGap.RG.Robust2UndershootAfSchedule (robust2UndershootSchedule)
open YMGap.RG.Robust2UndershootCrossoverInstance (etaR2 robust2_crossover_instance)
open YMGap.RG.Robust3UndershootAfSchedule (robust3UndershootSchedule r3Nome)
open YMGap.RG.Robust3UndershootPhysicalUnits (r3Rho r3P r3P_value)
open YMGap.RG.Robust3UndershootCrossoverInstance (etaR3 robust3_crossover_instance)
open YMGap.RG.Robust3MarginDischarge (robust3_margin_nonneg margin_nonneg_of_floor)
open YMGap.RG.Robust3SpacingHeatKernel (hposHK nonneg_of_pos rho_ge_one aSeq spacing_nonvacuous)
open YMGap.RG.Robust3SchurRankOne
  (SchurBudget schurSlack schur_of_spectral capDelta capDelta_nonneg capDelta_le_one)
open YMGap.RG.Robust3CrossUniform (VC PhiFam hupper_unif hcross_unif hafδ_unif hschur_unif_of_spectral)
open YMGap.RG.Robust3UndershootAfScheduleW558 (robust3UndershootScheduleB r3NomeB)
open YMGap.RG.Robust3CrossUniformW558 (PhiFamB hupper_unifB hafδ_unifB fineAtB coarseAtB)
open YMGap.RG.Robust3CrossResplitB
  (hcross_unifRS etaRS eRS etaRS_budget budget_RS_ok floor_RS_pos scaleChain_crossover_floor_k
    capDeltaRS capDeltaRS_nonneg capDeltaRS_le_one hposHKB r3_seedB)

/-! ## The corrected table -/

/-- Corrected head `ρ₀..ρ₄ = 3/2, 3/2, 8/5, 7/4, 7/4` (approved values; `spacing_recheck.md`). -/
def rhoCHead : Nat → Q'
  | 0 => Q'.mkPos 3 2 (by decide)
  | 1 => Q'.mkPos 3 2 (by decide)
  | 2 => Q'.mkPos 8 5 (by decide)
  | 3 => Q'.mkPos 7 4 (by decide)
  | _ => Q'.mkPos 7 4 (by decide)

/-- Head weights: exact backward products `ω_j = ρ_j ⋯ ρ₄ · r2Omega 5`, with `r2Omega 5 = 10303156017/390625000`. -/
def omegaCHead : Nat → Q'
  | 0 => Q'.mkPos 4543691803497 15625000000 (by decide)
  | 1 => Q'.mkPos 1514563934499 7812500000 (by decide)
  | 2 => Q'.mkPos 504854644833 3906250000 (by decide)
  | 3 => Q'.mkPos 504854644833 6250000000 (by decide)
  | _ => Q'.mkPos 72122092119 1562500000 (by decide)

/-- Corrected spacing table: `rhoCHead` for `j < 5`, the unchanged `r2Rho j` (= `r3Rho j`) for `j ≥ 5`. -/
def rhoC (i : Nat) : Q' := if i < 5 then rhoCHead i else r2Rho i

/-- Corrected weights: `omegaCHead` for `j < 5`, the unchanged `r2Omega j` for `j ≥ 5`. -/
def omegaC (i : Nat) : Q' := if i < 5 then omegaCHead i else r2Omega i

private theorem not_lt_of_le' {a b : Nat} (h : b ≤ a) : ¬ a < b := fun h' =>
  Nat.lt_irrefl a (Nat.lt_of_lt_of_le h' h)

/-- The tail is unchanged: `rhoC j = r2Rho j` for `j ≥ 5`. -/
theorem rhoC_eq_of_ge (i : Nat) (h : 5 ≤ i) : rhoC i = r2Rho i := by
  unfold rhoC; rw [if_neg (not_lt_of_le' h)]

/-- The tail weights are unchanged: `omegaC j = r2Omega j` for `j ≥ 5`. -/
theorem omegaC_eq_of_ge (i : Nat) (h : 5 ≤ i) : omegaC i = r2Omega i := by
  unfold omegaC; rw [if_neg (not_lt_of_le' h)]

private theorem headC_w : ∀ i, i < 5 → rhoC i * omegaC (i+1) ≤ omegaC i := by decide
private theorem headC_ge_one : ∀ i, i < 5 → (1 : Q') ≤ omegaC i := by decide

theorem rhoC_weight (i : Nat) : rhoC i * omegaC (i+1) ≤ omegaC i := by
  by_cases h : i < 5
  · exact headC_w i h
  · have hi : 5 ≤ i := Nat.not_lt.mp h
    rw [rhoC_eq_of_ge i hi, omegaC_eq_of_ge i hi, omegaC_eq_of_ge (i+1) (Nat.le_succ_of_le hi)]
    exact r2_weight i

theorem omegaC_ge_one (i : Nat) : (1 : Q') ≤ omegaC i := by
  by_cases h : i < 5
  · exact headC_ge_one i h
  · rw [omegaC_eq_of_ge i (Nat.not_lt.mp h)]; exact r2_omega_ge_one i

/-- Every corrected entry is at least the old one: `r2Rho j ≤ rhoC j`. -/
theorem r2Rho_le_rhoC (i : Nat) : r2Rho i ≤ rhoC i := by
  by_cases h : i < 5
  · have hall : ∀ i, i < 5 → r2Rho i ≤ rhoC i := by decide
    exact hall i h
  · rw [rhoC_eq_of_ge i (Nat.not_lt.mp h)]; exact Q'.le_refl' _

theorem rhoC_ge_one (i : Nat) : (1 : Q') ≤ rhoC i :=
  Q'.le_trans' _ _ _ (rho_ge_one i) (r2Rho_le_rhoC i)

/-- `P_C = ω_C,0 = 4543691803497/15625000000 ≈ 290.796`. -/
def PC : Q' := Q'.mkPos 4543691803497 15625000000 (by decide)

/-- **Exact corrected constant (decide):** `omegaC 0 = PC` and `290 < PC < 291`. -/
theorem PC_value : omegaC 0 = PC ∧ Q'.ofNat 290 < PC ∧ PC < Q'.ofNat 291 := by decide

/-- **Head products (decide):** the corrected `ρ₀⋯ρ₄` equals `441/40 = 11.025`, and the old one equals
`12423/4000 = 3.10575`. Both `PC` and `r2P` are the head product times the unchanged `r2Omega 5`. -/
theorem head_products :
    Q'.eqv (rhoC 0 * rhoC 1 * rhoC 2 * rhoC 3 * rhoC 4) (Q'.mkPos 441 40 (by decide)) ∧
    Q'.eqv (r2Rho 0 * r2Rho 1 * r2Rho 2 * r2Rho 3 * r2Rho 4) (Q'.mkPos 12423 4000 (by decide)) ∧
    Q'.eqv PC (Q'.mkPos 441 40 (by decide) * r2Omega 5) ∧
    Q'.eqv r2P (Q'.mkPos 12423 4000 (by decide) * r2Omega 5) := by decide

/-- **Ratio (decide):** `PC · 12423/4000 = r2P · 441/40` exactly, and `3.549·r2P < PC < 3.550·r2P`. -/
theorem PC_ratio :
    Q'.eqv (PC * Q'.mkPos 12423 4000 (by decide)) (r2P * Q'.mkPos 441 40 (by decide)) ∧
    Q'.mkPos 3549 1000 (by decide) * r2P < PC ∧ PC < Q'.mkPos 3550 1000 (by decide) * r2P := by decide

/-- **Table vs recheck values (rational comparisons, decide).** The needed values are numerical
(`spacing_recheck.md`, NOT proved).
* The old entries `ρ₀..ρ₃` fall below the lower ends of the needed values: 1.4142, 1.4211, 1.473 (= 1.486 − 0.013)
  and 1.618 (= 1.633 − 0.015).
* The corrected entries `ρ₀..ρ₄` exceed the upper ends: 1.4142, 1.4211, 1.499, 1.648 and 1.663.
* The unchanged `ρ₅ = 9/5` exceeds 1.452. -/
theorem table_vs_needed :
    (r2Rho 0 < Q'.mkPos 14142 10000 (by decide) ∧ r2Rho 1 < Q'.mkPos 14211 10000 (by decide) ∧
      r2Rho 2 < Q'.mkPos 1473 1000 (by decide) ∧ r2Rho 3 < Q'.mkPos 1618 1000 (by decide)) ∧
    (Q'.mkPos 14142 10000 (by decide) ≤ rhoC 0 ∧ Q'.mkPos 14211 10000 (by decide) ≤ rhoC 1 ∧
      Q'.mkPos 1499 1000 (by decide) ≤ rhoC 2 ∧ Q'.mkPos 1648 1000 (by decide) ≤ rhoC 3 ∧
      Q'.mkPos 1663 1000 (by decide) ≤ rhoC 4 ∧ Q'.mkPos 1452 1000 (by decide) ≤ rhoC 5) := by decide

/-! ## Spacing bound and the generic floor step -/

/-- **Physical-units spacing bound, corrected table (PROVED reduction):** under
`hspacing_OPEN : 2·a_{i+1} ≤ ρ_C,i·a_i`, `2ⁿ·a_n ≤ P_C·a_0` with `P_C ≈ 290.80`. Analogue of
`robust2_spacing_bound` / `robust3_spacing_bound`. -/
theorem spacing_bound_C (a : Nat → Q') (ha : ∀ i, (0 : Q') ≤ a i)
    (hspacing_OPEN : ∀ i, Q'.ofNat 2 * a (i+1) ≤ rhoC i * a i) (n : Nat) :
    Q'.ofNat (2 ^ n) * a n ≤ PC * a 0 := by
  have h := spacing_bound a rhoC omegaC ha omegaC_ge_one hspacing_OPEN rhoC_weight n
  rw [PC_value.1] at h
  exact h

/-- The old (weaker) spacing hypothesis implies the corrected one (`r2Rho ≤ rhoC`, `a ≥ 0`). -/
theorem hspacing_C_of_old (a : Nat → Q') (ha : ∀ i, (0 : Q') ≤ a i)
    (h : ∀ i, Q'.ofNat 2 * a (i+1) ≤ r2Rho i * a i) :
    ∀ i, Q'.ofNat 2 * a (i+1) ≤ rhoC i * a i := fun i =>
  Q'.le_trans' _ _ _ (h i) (Q'.mul_le_mul_of_nonneg_right _ _ _ (r2Rho_le_rhoC i) (ha i))

/-- Generic floor step on the corrected table: from a rate floor `fl ≤ 2ⁿ·M n` and `M n ≥ 0`,
`fl·a_n ≤ (P_C·a_0)·M n`. -/
theorem floor_C (a : Nat → Q') (ha : ∀ i, (0 : Q') ≤ a i)
    (hspacing_OPEN : ∀ i, Q'.ofNat 2 * a (i+1) ≤ rhoC i * a i) (M : Nat → Q') (fl : Q') (n : Nat)
    (hM : (0 : Q') ≤ M n) (hfl : fl ≤ Q'.ofNat (2 ^ n) * M n) :
    fl * a n ≤ (PC * a 0) * M n := by
  have h := floor_physical a rhoC omegaC M fl ha omegaC_ge_one hspacing_OPEN rhoC_weight n hM hfl
  rw [PC_value.1] at h
  exact h

/-! ## Robust2 / Robust3 floors on the corrected table -/

/-- Analogue of `robust2_physical_floor` with `ρ := rhoC`, `P := PC ≈ 290.80`. Same OPEN inputs; the rate floor
is unchanged. -/
theorem robust2_physical_floor_C :
    let ns := robust2UndershootSchedule
    ∀ (width : Nat → Nat) (delta : Nat → Q')
      (_hd0 : ∀ n, (0 : Q') ≤ delta n) (_hd1 : ∀ n, delta n ≤ (1 : Q'))
      (_hcross_OPEN : ∀ n, n < 6 → delta n ≤ etaR2 n)
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
      (_hspacing_OPEN : ∀ i, Q'.ofNat 2 * a (i+1) ≤ rhoC i * a i)
      (_hmargin_OPEN : ∀ n, (0 : Q') ≤ latticeMarginOf (relativeRate timeRate delta) n)
      (n : Nat),
      ((1 : Q') - timeRate) * (timeRate -
          (eDy + Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (0+2))) * a n ≤
        (PC * a 0) * latticeMarginOf (relativeRate timeRate delta) n :=
  fun width delta hd0 hd1 hcross hafδ Phi D hupper hschur a ha hsp hM n =>
    floor_C a ha hsp (latticeMarginOf (relativeRate timeRate delta)) _ n (hM n)
      (robust2_crossover_instance width delta hd0 hd1 hcross hafδ Phi D hupper hschur n).2

/-- Analogue of `robust3_physical_floor` with `ρ := rhoC`, `P := PC`. -/
theorem robust3_physical_floor_C :
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
      (_hspacing_OPEN : ∀ i, Q'.ofNat 2 * a (i+1) ≤ rhoC i * a i)
      (_hmargin_OPEN : ∀ n, (0 : Q') ≤ latticeMarginOf (relativeRate timeRate delta) n)
      (n : Nat),
      ((1 : Q') - timeRate) * (timeRate -
          (eDy + Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (0+2))) * a n ≤
        (PC * a 0) * latticeMarginOf (relativeRate timeRate delta) n :=
  fun width delta hd0 hd1 hcross hafδ Phi D hupper hschur a ha hsp hM n =>
    floor_C a ha hsp (latticeMarginOf (relativeRate timeRate delta)) _ n (hM n)
      (robust3_crossover_instance width delta hd0 hd1 hcross hafδ Phi D hupper hschur n).2

/-- Analogue of `robust3_physical_floor_noMargin` with `ρ := rhoC`, `P := PC`. -/
theorem robust3_physical_floor_noMargin_C :
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
      (_hspacing_OPEN : ∀ i, Q'.ofNat 2 * a (i+1) ≤ rhoC i * a i)
      (n : Nat),
      ((1 : Q') - timeRate) * (timeRate -
          (eDy + Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (0+2))) * a n ≤
        (PC * a 0) * latticeMarginOf (relativeRate timeRate delta) n :=
  fun width delta hd0 hd1 hcross hafδ Phi D hupper hschur a ha hsp n =>
    robust3_physical_floor_C width delta hd0 hd1 hcross hafδ Phi D hupper hschur a ha hsp
      (robust3_margin_nonneg width delta hd0 hd1 hcross hafδ Phi D hupper hschur) n

/-! ## Heat-kernel form (schedule A nomes `r3Nome`) -/

/-- Analogue of `hspacingHK_win` on the corrected table. -/
def hspacingHK_winC (aHK : Q' → Q') (lo hi : Nat) : Prop :=
  ∀ j, lo ≤ j → j ≤ hi → Q'.ofNat 2 * aHK (r3Nome (j+1)) ≤ rhoC j * aHK (r3Nome j)

/-- Analogue of `hspacingHK_off` on the corrected table; OPEN. -/
def hspacingHK_offC (aHK : Q' → Q') (lo hi : Nat) : Prop :=
  ∀ j, (j < lo ∨ hi < j) → Q'.ofNat 2 * aHK (r3Nome (j+1)) ≤ rhoC j * aHK (r3Nome j)

theorem hspacingC_of_HK (aHK : Q' → Q') (lo hi : Nat) (hw : hspacingHK_winC aHK lo hi)
    (ho : hspacingHK_offC aHK lo hi) :
    ∀ i, Q'.ofNat 2 * (fun j => aHK (r3Nome j)) (i+1) ≤ rhoC i * (fun j => aHK (r3Nome j)) i := by
  intro i
  by_cases h1 : i < lo
  · exact ho i (Or.inl h1)
  · by_cases h2 : hi < i
    · exact ho i (Or.inr h2)
    · exact hw i (Nat.le_of_not_lt h1) (Nat.le_of_not_lt h2)

/-- Analogue of `robust3_spacing_bound_HK`: `2ⁿ·aHK(w_n) ≤ P_C·aHK(w_0)`. -/
theorem robust3_spacing_bound_HK_C (aHK : Q' → Q') (lo hi : Nat) (hp : hposHK aHK)
    (hw : hspacingHK_winC aHK lo hi) (ho : hspacingHK_offC aHK lo hi) (n : Nat) :
    Q'.ofNat (2 ^ n) * aHK (r3Nome n) ≤ PC * aHK (r3Nome 0) :=
  spacing_bound_C (fun j => aHK (r3Nome j)) (nonneg_of_pos aHK hp) (hspacingC_of_HK aHK lo hi hw ho) n

/-- Analogue of `robust3_physical_floor_noMargin_HK` with `ρ := rhoC`, `P := PC`. -/
theorem robust3_physical_floor_noMargin_HK_C :
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
      (aHK : Q' → Q') (lo hi : Nat) (_hpos : hposHK aHK)
      (_hwin_MC : hspacingHK_winC aHK lo hi) (_hoff_OPEN : hspacingHK_offC aHK lo hi)
      (n : Nat),
      ((1 : Q') - timeRate) * (timeRate -
          (eDy + Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (0+2))) * aHK (r3Nome n) ≤
        (PC * aHK (r3Nome 0)) * latticeMarginOf (relativeRate timeRate delta) n :=
  fun width delta hd0 hd1 hcross hafδ Phi D hupper hschur aHK lo hi hp hw ho n =>
    robust3_physical_floor_noMargin_C width delta hd0 hd1 hcross hafδ Phi D hupper hschur
      (fun j => aHK (r3Nome j)) (nonneg_of_pos aHK hp) (hspacingC_of_HK aHK lo hi hw ho) n

/-- Non-vacuity of the corrected spacing and positivity hypotheses: `a_j = 2^{-j}` (since `ρ_C ≥ 1`). -/
theorem spacing_nonvacuous_C :
    (∀ j, (0 : Q') < aSeq j) ∧ ∀ j, Q'.ofNat 2 * aSeq (j+1) ≤ rhoC j * aSeq j :=
  ⟨spacing_nonvacuous.1,
    hspacing_C_of_old aSeq (fun j => Q'.le_of_lt (spacing_nonvacuous.1 j)) spacing_nonvacuous.2⟩

/-- Analogue of `HK_hyps_of_seq`. With `Robust3NomeInjective.aHKw_nome` this gives the function-level witness
`aHKw` (`HK_hyps_of_seq_C aHKw aHKw_nome lo hi`). -/
theorem HK_hyps_of_seq_C (aHK : Q' → Q') (h : ∀ j, aHK (r3Nome j) = aSeq j) (lo hi : Nat) :
    hposHK aHK ∧ hspacingHK_winC aHK lo hi ∧ hspacingHK_offC aHK lo hi := by
  refine ⟨fun j => ?_, fun j _ _ => ?_, fun j _ => ?_⟩
  · rw [h j]; exact spacing_nonvacuous_C.1 j
  · rw [h j, h (j+1)]; exact spacing_nonvacuous_C.2 j
  · rw [h j, h (j+1)]; exact spacing_nonvacuous_C.2 j

/-- Analogue of `robust3_physical_floor_spectral_HK` with `ρ := rhoC`, `P := PC`. -/
theorem robust3_physical_floor_spectral_HK_C :
    let ns := robust3UndershootSchedule
    ∀ (width : Nat → Nat) (delta : Nat → Q')
      (_hd0 : ∀ n, (0 : Q') ≤ delta n) (_hd1 : ∀ n, delta n ≤ (1 : Q'))
      (_hcross_OPEN : ∀ n, n < 6 → delta n ≤ etaR3 n)
      (_hafδ_OPEN : ∀ n, 6 ≤ n →
        delta n ≤ Q'.mkPos 1 10 (by decide) * (afGap (0+n) * afGap (0+n)))
      (Phi : ∀ n, VacuumComplement (ns.nome_pos (0+n+1)) (ns.nome_lt_one (0+n+1))
          (width := width (0+n+1)) →
        VacuumComplement (ns.nome_pos (0+n)) (ns.nome_lt_one (0+n)) (width := width (0+n)))
      (_hupper_OPEN : ∀ n y, RCle
        (completedInner (ns.nome_pos (0+n)) (ns.nome_lt_one (0+n)) (Phi n y).val (Phi n y).val)
        (completedInner (ns.nome_pos (0+n+1)) (ns.nome_lt_one (0+n+1)) y.val y.val))
      (f c : Nat → Q')
      (_hfine_OPEN : ∀ n, WilsonVacuumSqTwoStepFactor (ns.nome_pos (0+n+1)) (ns.nome_lt_one (0+n+1))
        (width (0+n+1)) (f n))
      (_hcoarse_OPEN : ∀ n y, RCle
        (RCscale (c n) (completedInner (ns.nome_pos (0+n+1)) (ns.nome_lt_one (0+n+1)) y.val y.val))
        (completedInner (ns.nome_pos (0+n)) (ns.nome_lt_one (0+n))
          (completedTime (ns.nome_pos (0+n)) (ns.nome_lt_one (0+n)) 1 (Phi n y).val)
          (completedTime (ns.nome_pos (0+n)) (ns.nome_lt_one (0+n)) 1 (Phi n y).val)))
      (_hbudget_OPEN : ∀ n, SchurBudget (f n) (c n) (delta n))
      (aHK : Q' → Q') (lo hi : Nat) (_hpos : hposHK aHK)
      (_hwin_MC : hspacingHK_winC aHK lo hi) (_hoff_OPEN : hspacingHK_offC aHK lo hi)
      (n : Nat),
      ((1 : Q') - timeRate) * (timeRate -
          (eDy + Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (0+2))) * aHK (r3Nome n) ≤
        (PC * aHK (r3Nome 0)) * latticeMarginOf (relativeRate timeRate delta) n :=
  fun width delta hd0 hd1 hcross hafδ Phi hupper f c hfine hcoarse hbud aHK lo hi hp hw ho n =>
    robust3_physical_floor_noMargin_HK_C width delta hd0 hd1 hcross hafδ Phi
      (fun k => schurSlack _ _ _ _ (width (0+k+1)) (width (0+k)) (delta k) (Phi k)) hupper
      (fun k => schur_of_spectral _ _ _ _ _ _ (delta k) (f k) (c k) (Phi k) (hd1 k) (hfine k)
        (hcoarse k) (hbud k))
      aHK lo hi hp hw ho n

/-- Analogue of `robust3_physical_floor_lmax_HK` (`δ := capDelta`) with `ρ := rhoC`, `P := PC`. -/
theorem robust3_physical_floor_lmax_HK_C :
    let ns := robust3UndershootSchedule
    ∀ (width : Nat → Nat)
      (Phi : ∀ n, VacuumComplement (ns.nome_pos (0+n+1)) (ns.nome_lt_one (0+n+1))
          (width := width (0+n+1)) →
        VacuumComplement (ns.nome_pos (0+n)) (ns.nome_lt_one (0+n)) (width := width (0+n)))
      (_hupper_OPEN : ∀ n y, RCle
        (completedInner (ns.nome_pos (0+n)) (ns.nome_lt_one (0+n)) (Phi n y).val (Phi n y).val)
        (completedInner (ns.nome_pos (0+n+1)) (ns.nome_lt_one (0+n+1)) y.val y.val))
      (f c : Nat → Q')
      (_hfine_OPEN : ∀ n, WilsonVacuumSqTwoStepFactor (ns.nome_pos (0+n+1)) (ns.nome_lt_one (0+n+1))
        (width (0+n+1)) (f n))
      (_hcoarse_OPEN : ∀ n y, RCle
        (RCscale (c n) (completedInner (ns.nome_pos (0+n+1)) (ns.nome_lt_one (0+n+1)) y.val y.val))
        (completedInner (ns.nome_pos (0+n)) (ns.nome_lt_one (0+n))
          (completedTime (ns.nome_pos (0+n)) (ns.nome_lt_one (0+n)) 1 (Phi n y).val)
          (completedTime (ns.nome_pos (0+n)) (ns.nome_lt_one (0+n)) 1 (Phi n y).val)))
      (_hbudget_OPEN : ∀ n, SchurBudget (f n) (c n) (capDelta n))
      (aHK : Q' → Q') (lo hi : Nat) (_hpos : hposHK aHK)
      (_hwin_MC : hspacingHK_winC aHK lo hi) (_hoff_OPEN : hspacingHK_offC aHK lo hi)
      (n : Nat),
      ((1 : Q') - timeRate) * (timeRate -
          (eDy + Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (0+2))) * aHK (r3Nome n) ≤
        (PC * aHK (r3Nome 0)) * latticeMarginOf (relativeRate timeRate capDelta) n :=
  fun width Phi hupper f c hfine hcoarse hbud aHK lo hi hp hw ho n =>
    robust3_physical_floor_spectral_HK_C width capDelta capDelta_nonneg capDelta_le_one
      (fun k hk => by unfold capDelta; rw [if_pos hk]; exact Q'.le_refl' _)
      (fun k hk => by unfold capDelta; rw [if_neg (Nat.not_lt.mpr hk)]; exact Q'.le_refl' _)
      Phi hupper f c hfine hcoarse hbud aHK lo hi hp hw ho n

/-- Analogue of `robust3_floor_width_uniform_schur` with `ρ := rhoC`, `P := PC`. -/
theorem robust3_floor_width_uniform_schur_C (delta : Nat → Q')
    (hd0 : ∀ n, (0 : Q') ≤ delta n) (hd1 : ∀ n, delta n ≤ (1 : Q'))
    (hcross_OPEN : ∀ n, n < 6 → delta n ≤ etaR3 n)
    (hafδ_OPEN : ∀ n, 6 ≤ n → delta n ≤ Q'.mkPos 1 10 (by decide) * (afGap (0+n) * afGap (0+n)))
    (Phi : PhiFam) (D : ∀ (W : Nat → Nat) (n : Nat), VC W (0+n+1) → RC)
    (hupper : hupper_unif Phi)
    (hschur_unif_OPEN : ∀ (W : Nat → Nat) n, SchurDecomposition (robust3UndershootSchedule.nome_pos (0+n+1))
      (robust3UndershootSchedule.nome_lt_one (0+n+1)) (robust3UndershootSchedule.nome_pos (0+n))
      (robust3UndershootSchedule.nome_lt_one (0+n)) (W (0+n+1)) (W (0+n)) (delta n) (Phi W n) (D W n))
    (aHK : Q' → Q') (lo hi : Nat) (hpos : hposHK aHK)
    (hwin_MC : hspacingHK_winC aHK lo hi) (hoff_OPEN : hspacingHK_offC aHK lo hi) :
    ∀ (W : Nat → Nat) (n : Nat),
      WilsonVacuumSqContraction (robust3UndershootSchedule.nome_pos (0+n))
          (robust3UndershootSchedule.nome_lt_one (0+n)) (W (0+n)) (relativeRate timeRate delta n) ∧
      ((1 : Q') - timeRate) * (timeRate -
          (eDy + Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (0+2))) * aHK (r3Nome n) ≤
        (PC * aHK (r3Nome 0)) * latticeMarginOf (relativeRate timeRate delta) n :=
  fun W n => ⟨(robust3_crossover_instance W delta hd0 hd1 hcross_OPEN hafδ_OPEN (Phi W) (D W)
      (hupper W) (hschur_unif_OPEN W) n).1,
    robust3_physical_floor_noMargin_HK_C W delta hd0 hd1 hcross_OPEN hafδ_OPEN (Phi W) (D W)
      (hupper W) (hschur_unif_OPEN W) aHK lo hi hpos hwin_MC hoff_OPEN n⟩

/-- Analogue of `robust3_floor_width_uniform` with `ρ := rhoC`, `P := PC`. Not chart closure. -/
theorem robust3_floor_width_uniform_C (Phi : PhiFam) (f c : Nat → Q')
    (hupper_unif_OPEN : hupper_unif Phi)
    (hcross_unif_OPEN : hcross_unif Phi f c) (hafδ_unif_OPEN : hafδ_unif Phi f c)
    (aHK : Q' → Q') (lo hi : Nat) (hpos : hposHK aHK)
    (hwin_MC : hspacingHK_winC aHK lo hi) (hoff_OPEN : hspacingHK_offC aHK lo hi) :
    ∀ (W : Nat → Nat) (n : Nat),
      WilsonVacuumSqContraction (robust3UndershootSchedule.nome_pos (0+n))
          (robust3UndershootSchedule.nome_lt_one (0+n)) (W (0+n)) (relativeRate timeRate capDelta n) ∧
      ((1 : Q') - timeRate) * (timeRate -
          (eDy + Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (0+2))) * aHK (r3Nome n) ≤
        (PC * aHK (r3Nome 0)) * latticeMarginOf (relativeRate timeRate capDelta) n :=
  robust3_floor_width_uniform_schur_C capDelta capDelta_nonneg capDelta_le_one
    (fun k hk => by unfold capDelta; rw [if_pos hk]; exact Q'.le_refl' _)
    (fun k hk => by unfold capDelta; rw [if_neg (Nat.not_lt.mpr hk)]; exact Q'.le_refl' _)
    Phi (fun W n => schurSlack _ _ _ _ (W (0+n+1)) (W (0+n)) (capDelta n) (Phi W n)) hupper_unif_OPEN
    (hschur_unif_of_spectral Phi f c hcross_unif_OPEN hafδ_unif_OPEN) aHK lo hi hpos hwin_MC hoff_OPEN

/-! ## Schedule B with R* (`r3NomeB`) -/

/-- Analogue of `hspacingHKB_win` on the corrected table. -/
def hspacingHKB_winC (aHK : Q' → Q') (lo hi : Nat) : Prop :=
  ∀ j, lo ≤ j → j ≤ hi → Q'.ofNat 2 * aHK (r3NomeB (j+1)) ≤ rhoC j * aHK (r3NomeB j)

/-- Analogue of `hspacingHKB_off` on the corrected table; OPEN. -/
def hspacingHKB_offC (aHK : Q' → Q') (lo hi : Nat) : Prop :=
  ∀ j, (j < lo ∨ hi < j) → Q'.ofNat 2 * aHK (r3NomeB (j+1)) ≤ rhoC j * aHK (r3NomeB j)

theorem hspacingBC_of_HK (aHK : Q' → Q') (lo hi : Nat) (hw : hspacingHKB_winC aHK lo hi)
    (ho : hspacingHKB_offC aHK lo hi) :
    ∀ i, Q'.ofNat 2 * (fun j => aHK (r3NomeB j)) (i+1) ≤ rhoC i * (fun j => aHK (r3NomeB j)) i := by
  intro i
  by_cases h1 : i < lo
  · exact ho i (Or.inl h1)
  · by_cases h2 : hi < i
    · exact ho i (Or.inr h2)
    · exact hw i (Nat.le_of_not_lt h1) (Nat.le_of_not_lt h2)

/-- Copy of the private `step_dataRS` (`Robust3CrossResplitB.lean`). -/
private theorem step_dataRS_C (Phi : PhiFamB) (f c : Nat → Q') (hX : hcross_unifRS Phi f c)
    (hA : hafδ_unifB Phi f c) (W : Nat → Nat) (n : Nat) :
    fineAtB W n (f n) ∧ coarseAtB W n (Phi W n) (c n) ∧ SchurBudget (f n) (c n) (capDeltaRS n) := by
  by_cases h : n < 6
  · refine ⟨(hX.2 W n h).1, (hX.2 W n h).2, ?_⟩
    unfold capDeltaRS; rw [if_pos h]; exact hX.1 n h
  · have h6 : 6 ≤ n := Nat.le_of_not_lt h
    refine ⟨(hA.2 W n h6).1, (hA.2 W n h6).2, ?_⟩
    unfold capDeltaRS; rw [if_neg h]; exact hA.1 n h6

/-- Copy of the private `hschurB_of_spectral` (`Robust3CrossResplitB.lean`). -/
private theorem hschurB_of_spectral_C (Phi : PhiFamB) (f c : Nat → Q') (hX : hcross_unifRS Phi f c)
    (hA : hafδ_unifB Phi f c) (W : Nat → Nat) (n : Nat) :
    SchurDecomposition (robust3UndershootScheduleB.nome_pos (0+n+1))
      (robust3UndershootScheduleB.nome_lt_one (0+n+1))
      (robust3UndershootScheduleB.nome_pos (0+n)) (robust3UndershootScheduleB.nome_lt_one (0+n))
      (W (0+n+1)) (W (0+n)) (capDeltaRS n) (Phi W n)
      (schurSlack _ _ _ _ (W (0+n+1)) (W (0+n)) (capDeltaRS n) (Phi W n)) :=
  have hd := step_dataRS_C Phi f c hX hA W n
  schur_of_spectral _ _ _ _ _ _ (capDeltaRS n) (f n) (c n) (Phi W n) (capDeltaRS_le_one n)
    hd.1 hd.2.1 hd.2.2

/-- **Analogue of `robust3B_floor_width_uniform_RS` on the corrected table (PROVED reduction from explicit OPEN
inputs).** The floor is unchanged (`587159/30000000 ≈ 0.0196`, `floor_RS_value`); `P` goes from `r3P ≈ 81.92` to
`PC ≈ 290.80`. OPEN: `hupper`, `hX`, `hA`, and the schedule-B spacing hypotheses on the corrected table.
Not chart closure; not gap evidence. -/
theorem robust3B_floor_width_uniform_RS_C (Phi : PhiFamB) (f c : Nat → Q')
    (hupper : hupper_unifB Phi) (hX : hcross_unifRS Phi f c) (hA : hafδ_unifB Phi f c)
    (aHK : Q' → Q') (lo hi : Nat) (hpos : hposHKB aHK)
    (hwin_MC : hspacingHKB_winC aHK lo hi) (hoff_OPEN : hspacingHKB_offC aHK lo hi) :
    ∀ (W : Nat → Nat) (n : Nat),
      WilsonVacuumSqContraction (robust3UndershootScheduleB.nome_pos (0+n))
          (robust3UndershootScheduleB.nome_lt_one (0+n)) (W (0+n))
          (relativeRate timeRate capDeltaRS n) ∧
      ((1 : Q') - timeRate) *
          (timeRate - (eRS + Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (0+6+2)))
          * aHK (r3NomeB n) ≤
        (PC * aHK (r3NomeB 0)) * latticeMarginOf (relativeRate timeRate capDeltaRS) n := by
  intro W n
  have hc := scaleChain_crossover_floor_k robust3UndershootScheduleB W 0 6 timeRate
    (Q'.mkPos 1 10 (by decide)) eRS capDeltaRS etaRS (Q'.le_of_lt timeRate_positive)
    timeRate_lt_one (by decide) (by decide) capDeltaRS_nonneg capDeltaRS_le_one
    (fun k hk => by unfold capDeltaRS; rw [if_pos hk]; exact Q'.le_refl' _)
    (fun k hk => by unfold capDeltaRS; rw [if_neg (Nat.not_lt.mpr hk)]; exact Q'.le_refl' _)
    etaRS_budget budget_RS_ok (Phi W)
    (fun n => schurSlack _ _ _ _ (W (0+n+1)) (W (0+n)) (capDeltaRS n) (Phi W n))
    (hupper W) (hschurB_of_spectral_C Phi f c hX hA W) (r3_seedB (W 0)) n
  refine ⟨hc.1, ?_⟩
  have hM := margin_nonneg_of_floor _ _ n floor_RS_pos hc.2
  exact floor_C (fun j => aHK (r3NomeB j)) (fun i => Q'.le_of_lt (hpos i))
    (hspacingBC_of_HK aHK lo hi hwin_MC hoff_OPEN)
    (latticeMarginOf (relativeRate timeRate capDeltaRS)) _ n hM hc.2

end YMGap.RG.Robust3SpacingCorrected
#print axioms YMGap.RG.Robust3SpacingCorrected.rhoCHead
#print axioms YMGap.RG.Robust3SpacingCorrected.omegaCHead
#print axioms YMGap.RG.Robust3SpacingCorrected.rhoC
#print axioms YMGap.RG.Robust3SpacingCorrected.omegaC
#print axioms YMGap.RG.Robust3SpacingCorrected.rhoC_eq_of_ge
#print axioms YMGap.RG.Robust3SpacingCorrected.omegaC_eq_of_ge
#print axioms YMGap.RG.Robust3SpacingCorrected.rhoC_weight
#print axioms YMGap.RG.Robust3SpacingCorrected.omegaC_ge_one
#print axioms YMGap.RG.Robust3SpacingCorrected.r2Rho_le_rhoC
#print axioms YMGap.RG.Robust3SpacingCorrected.rhoC_ge_one
#print axioms YMGap.RG.Robust3SpacingCorrected.PC
#print axioms YMGap.RG.Robust3SpacingCorrected.PC_value
#print axioms YMGap.RG.Robust3SpacingCorrected.head_products
#print axioms YMGap.RG.Robust3SpacingCorrected.PC_ratio
#print axioms YMGap.RG.Robust3SpacingCorrected.table_vs_needed
#print axioms YMGap.RG.Robust3SpacingCorrected.spacing_bound_C
#print axioms YMGap.RG.Robust3SpacingCorrected.hspacing_C_of_old
#print axioms YMGap.RG.Robust3SpacingCorrected.floor_C
#print axioms YMGap.RG.Robust3SpacingCorrected.robust2_physical_floor_C
#print axioms YMGap.RG.Robust3SpacingCorrected.robust3_physical_floor_C
#print axioms YMGap.RG.Robust3SpacingCorrected.robust3_physical_floor_noMargin_C
#print axioms YMGap.RG.Robust3SpacingCorrected.hspacingHK_winC
#print axioms YMGap.RG.Robust3SpacingCorrected.hspacingHK_offC
#print axioms YMGap.RG.Robust3SpacingCorrected.hspacingC_of_HK
#print axioms YMGap.RG.Robust3SpacingCorrected.robust3_spacing_bound_HK_C
#print axioms YMGap.RG.Robust3SpacingCorrected.robust3_physical_floor_noMargin_HK_C
#print axioms YMGap.RG.Robust3SpacingCorrected.spacing_nonvacuous_C
#print axioms YMGap.RG.Robust3SpacingCorrected.HK_hyps_of_seq_C
#print axioms YMGap.RG.Robust3SpacingCorrected.robust3_physical_floor_spectral_HK_C
#print axioms YMGap.RG.Robust3SpacingCorrected.robust3_physical_floor_lmax_HK_C
#print axioms YMGap.RG.Robust3SpacingCorrected.robust3_floor_width_uniform_schur_C
#print axioms YMGap.RG.Robust3SpacingCorrected.robust3_floor_width_uniform_C
#print axioms YMGap.RG.Robust3SpacingCorrected.hspacingHKB_winC
#print axioms YMGap.RG.Robust3SpacingCorrected.hspacingHKB_offC
#print axioms YMGap.RG.Robust3SpacingCorrected.hspacingBC_of_HK
#print axioms YMGap.RG.Robust3SpacingCorrected.robust3B_floor_width_uniform_RS_C

