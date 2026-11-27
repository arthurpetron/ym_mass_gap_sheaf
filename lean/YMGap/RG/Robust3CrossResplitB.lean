/-
# Robust3 crossover, instance B: AF-tail fix (B₉) and the uneven budget R*

**Label: PROVED reductions and exact-rational certificates from explicit OPEN inputs.
NOT gap evidence, NOT chart closure.**  Additive; `etaR3`, `Robust3*`, `*W558` modules are
untouched.  Spec: `bridge_rate_resplit.md` §4 (Nov 25, 2026).

* (A) `afPart_tail_budget`: the `afQuadratic_prefix_budget` telescope started at the handoff `k`,
  so the AF tail costs `C·afA²·inv(j0+k+2)` (= `afA²/90` at `C = 1/10`, `j0 = 0`, `k = 6`) instead
  of `C·afA²·inv(j0+2)` (= `afA²/30`).  `crossover_prefix_budget_k` and
  `scaleChain_crossover_floor_k` are the corresponding copies of the existing statements.
* (B) the budget R*: `η = (2⁻²⁰, 1/100, 1/8, 1/64, 1/64, 1/64)`, `E = 91/500`; floor
  `587159/30000000 ≈ 0.0195720 > 0` (decide).
* (C) per-step crossover interface `hcross_unifRS` and its coarse-constant-0 reduction;
  `fineAtB_mono` (a smaller fine factor implies a larger one), so the old `1/64` hypotheses imply
  the new ones at steps 2–5.
* (D) steps 0–1 at `q0RS = 1/1024`, `q1RS = 1/10`: the Dobrushin products are decide-level
  arithmetic only; the analytic inputs stay as the explicit `hDob_OPEN_q0` / `hDobW1_OPEN_q1`
  binders (paper: steps01 §2–3, §9).
* (E) `KPToFineAt_BRIDGE_RS` is an OPEN analytic input (BRIDGE, not in spec): the step-2 KP→fineAt
  link at factor `1/8` needs a decay rate `m ≥ ln 8 / 4 ≈ 0.520` per lattice time slice, while the
  existing certificate gives only `≈ 0.0135` per slice.  It is implied by the old
  `KPToFineAt_BRIDGE_B` (factor `1/64`).
* (F) `robust3B_floor_width_uniform_RS`: the floor on schedule B with R*.  The heat-kernel spacing
  hypotheses are restated on the schedule-B nomes (`hposHKB`, `hspacingHKB_win`,
  `hspacingHKB_off`) and are explicit hypotheses: `ρ₂, ρ₃` at `279/500` still need the Numerics
  recheck, so nothing about them is proved here.

U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence; any
uniform gap at w ≳ 1/8 would not hold for U(1) (YM Numerics interim report, numerical, not proved).

Mathlib-free; no sorry/admit/Classical/native_decide/omega/simpa/grind; axioms within
`propext`, `Quot.sound`.
-/

import YMGap.RG.Robust3CrossUniformW558
import YMGap.RG.CrossoverScaleChain
import YMGap.RG.Step0DobrushinUniform
import YMGap.RG.Step1DobrushinUniform
import YMGap.RG.Step2ConditionalW558
import YMGap.RG.Robust3SchurRankOne

namespace YMGap.RG.Robust3CrossResplitB

set_option autoImplicit false

open YMGap.Constructive YMGap.Constructive.CReal
open YMGap.Constructive.RationalTail (finSum)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner completedInner_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (VacuumComplement completedTime)
open YMGap.Continuum.BF4WilsonAllNomeExprMixRateContraction (WilsonVacuumSqContraction)
open YMGap.Continuum.BF4WilsonAllNomeRGDissipationBudget (relativeRate)
open YMGap.Continuum.BF4WilsonAllNomeRGStepComposition (latticeMarginOf)
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory (afGap afGap_pos afGap_lt_one afA)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory (NomeSchedule)
open YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay (timeRate timeRate_positive timeRate_lt_one)
open YMGap.Continuum.EvenDecayTwoStepFactor (twoStepFactor_of_even_decay)
open YMGap.RG.RelativeDissipationScaleChain
  (SchurDecomposition inv inv_nonneg inv_sq_le_tele afGap_le finSum_le_tele scaleChain_contraction
   relativeRate_side_floor)
open YMGap.RG.CrossoverScaleChain (crossPart afPart crossover_floor_pos)
open YMGap.RG.StrongCouplingNomeThreshold (uniformRate_of_guards scGuards_of_le_inv55)
open YMGap.RG.UndershootPhysicalUnits (floor_physical)
open YMGap.RG.Robust3UndershootPhysicalUnits (r3Rho r3Omega r3P r3P_value r3_weight r3_omega_ge_one)
open YMGap.RG.Robust3UndershootAfScheduleW558 (robust3UndershootScheduleB r3NomeB robust3B_join)
open YMGap.RG.Robust3MarginDischarge (margin_nonneg_of_floor)
open YMGap.RG.Robust3SchurRankOne (SchurBudget schurSlack schur_of_spectral)
open YMGap.RG.Robust3CrossUniformW558
  (VCB PhiFamB fineAtB coarseAtB coarseAtB_zero hupper_unifB hafδ_unifB)
open YMGap.RG.Step0DobrushinUniform (CentredPowerDecayVC evenDecay_of_centredPowerDecayVC)
open YMGap.RG.Step1DobrushinUniform (cKappa1)
open YMGap.RG.Step2Conditional (SphereGasModel)
open YMGap.RG.Step2ConditionalW558 (KPToFineAt_BRIDGE_B)

/-! ## (A) AF tail starting at the handoff `k` -/

/-- Telescoping potential: `inv (j0+k+2)` before the handoff, `inv (j0+m+2)` after. -/
def afTailPot (j0 k m : Nat) : Q' := if m < k then inv (j0 + k + 2) else inv (j0 + m + 2)

private theorem afTailPot_succ_of_lt (j0 k m : Nat) (h : m < k) :
    afTailPot j0 k (m+1) = inv (j0 + k + 2) := by
  unfold afTailPot
  by_cases h' : m + 1 < k
  · rw [if_pos h']
  · rw [if_neg h']
    have e : m + 1 = k := Nat.le_antisymm (Nat.succ_le_of_lt h) (Nat.not_lt.mp h')
    rw [e]

private theorem afTailPot_zero (j0 k : Nat) : afTailPot j0 k 0 = inv (j0 + k + 2) := by
  unfold afTailPot
  by_cases h : 0 < k
  · rw [if_pos h]
  · rw [if_neg h]
    have e : k = 0 := Nat.eq_zero_of_not_pos h
    rw [e]

private theorem afTailPot_nonneg (j0 k m : Nat) : (0 : Q') ≤ afTailPot j0 k m := by
  unfold afTailPot
  by_cases h : m < k
  · rw [if_pos h]; exact inv_nonneg _
  · rw [if_neg h]; exact inv_nonneg _

/-- One AF term against the telescoping difference (copy of the step in
`afQuadratic_prefix_budget`). -/
private theorem afSq_tele_step (C : Q') (hC : (0 : Q') ≤ C) (j : Nat) :
    C * (afGap j * afGap j) ≤ C * (afA * afA) * (inv (j+2) + -inv (j+3)) := by
  have hA : (0 : Q') ≤ afA := by decide
  have hg := afGap_le j
  have hsq := Q'.mul_le_mul_of_nonneg hg hg (Q'.mul_nonneg _ _ hA (inv_nonneg _))
    (Q'.le_of_lt (afGap_pos _))
  have ht : (afA * inv (j+3)) * (afA * inv (j+3)) ≤
      (afA * afA) * (inv (j+2) + -inv (j+3)) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (by decide)
      (fun | 0 => afA | _ => inv (j+3))))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (inv_sq_le_tele (j+2)) (Q'.mul_nonneg _ _ hA hA))
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ C (Q'.le_trans' _ _ _ hsq ht) hC) ?_
  exact Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))

private theorem afPart_tele (C : Q') (hC : (0 : Q') ≤ C) (j0 k m : Nat) :
    afPart C j0 k m ≤ C * (afA * afA) * (afTailPot j0 k m + -afTailPot j0 k (m+1)) := by
  by_cases h : m < k
  · have e0 : afPart C j0 k m = 0 := by unfold afPart; rw [if_pos h]
    have e1 : afTailPot j0 k m = inv (j0 + k + 2) := by unfold afTailPot; rw [if_pos h]
    rw [e0, e1, afTailPot_succ_of_lt j0 k m h]
    exact Q'.ge_of_eqv (poly_identity_of_normal_eq
      (.mul (.var 0) (.add (.var 1) (.neg (.var 1)))) (.const 0) (by decide)
      (fun | 0 => C * (afA * afA) | _ => inv (j0 + k + 2)))
  · have h' : ¬ m + 1 < k := fun h1 => h (Nat.lt_of_succ_lt h1)
    have e0 : afPart C j0 k m = C * (afGap (j0+m) * afGap (j0+m)) := by
      unfold afPart; rw [if_neg h]
    have e1 : afTailPot j0 k m = inv (j0 + m + 2) := by unfold afTailPot; rw [if_neg h]
    have e2 : afTailPot j0 k (m+1) = inv (j0 + (m+1) + 2) := by unfold afTailPot; rw [if_neg h']
    rw [e0, e1, e2]
    exact afSq_tele_step C hC (j0+m)

/-- **(A) AF tail from the handoff (PROVED):** `finSum (afPart C j0 k) n ≤ C·afA²·inv(j0+k+2)`. -/
theorem afPart_tail_budget (C : Q') (hC : (0 : Q') ≤ C) (j0 k n : Nat) :
    finSum (afPart C j0 k) n ≤ C * (afA * afA) * inv (j0 + k + 2) := by
  have hA : (0 : Q') ≤ afA := by decide
  have hc : (0 : Q') ≤ C * (afA * afA) := Q'.mul_nonneg _ _ hC (Q'.mul_nonneg _ _ hA hA)
  have h := finSum_le_tele (afPart C j0 k) (afTailPot j0 k) _ (afPart_tele C hC j0 k) n
  rw [afTailPot_zero] at h
  refine Q'.le_trans' _ _ _ h (Q'.mul_le_mul_of_nonneg_left _ _ _ ?_ hc)
  have hn := Q'.add_le_add_left (inv (j0 + k + 2) + -afTailPot j0 k n) 0 _
    (afTailPot_nonneg j0 k n)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (QPoly.q_add_zero_eqv _))
    (Q'.le_trans' _ _ _ hn (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0) (by decide)
      (fun | 0 => inv (j0 + k + 2) | _ => afTailPot j0 k n))))

private theorem finSum_le_add {d e a : Nat → Q'} (h : ∀ m, d m ≤ e m + a m) :
    ∀ n, finSum d n ≤ finSum e n + finSum a n
  | 0 => by show (0 : Q') ≤ 0 + 0; decide
  | n+1 => Q'.le_trans' _ _ _ (Q'.add_le_add (finSum_le_add h n) (h n))
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
        (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3))) (by decide)
        (fun | 0 => finSum e n | 1 => finSum a n | 2 => e n | _ => a n)))

private theorem split_le (C : Q') (j0 k : Nat) (delta eta : Nat → Q')
    (hcross : ∀ n, n < k → delta n ≤ eta n)
    (hafδ : ∀ n, k ≤ n → delta n ≤ C * (afGap (j0+n) * afGap (j0+n))) (m : Nat) :
    delta m ≤ crossPart k eta m + afPart C j0 k m := by
  unfold crossPart afPart
  by_cases h : m < k
  · rw [if_pos h, if_pos h]
    exact Q'.le_trans' _ _ _ (hcross m h) (Q'.ge_of_eqv (QPoly.q_add_zero_eqv _))
  · rw [if_neg h, if_neg h]
    exact Q'.le_trans' _ _ _ (hafδ m (Nat.not_lt.mp h))
      (Q'.ge_of_eqv (poly_identity_of_normal_eq (.add (.const 0) (.var 0)) (.var 0) (by decide)
        (fun _ => C * (afGap (j0+m) * afGap (j0+m)))))

/-- **Prefix budget with the tail from `k` (PROVED):** `finSum δ n ≤ E + C·afA²·inv(j0+k+2)`. -/
theorem crossover_prefix_budget_k (C E : Q') (hC : (0 : Q') ≤ C) (j0 k : Nat) (delta eta : Nat → Q')
    (hcross_OPEN : ∀ n, n < k → delta n ≤ eta n)
    (hafδ_OPEN : ∀ n, k ≤ n → delta n ≤ C * (afGap (j0+n) * afGap (j0+n)))
    (hE : ∀ n, finSum (crossPart k eta) n ≤ E) (n : Nat) :
    finSum delta n ≤ E + C * (afA * afA) * inv (j0 + k + 2) :=
  Q'.le_trans' _ _ _ (finSum_le_add (split_le C j0 k delta eta hcross_OPEN hafδ_OPEN) n)
    (Q'.add_le_add (hE n) (afPart_tail_budget C hC j0 k n))

/-- **`scaleChain_crossover_floor_k` (PROVED from explicit OPEN inputs).** Same binders and
conclusion as `scaleChain_crossover_floor`, with the AF tail budgeted from `k`:
`inv (j0+k+2)` in place of `inv (j0+2)`. -/
theorem scaleChain_crossover_floor_k (ns : NomeSchedule) (width : Nat → Nat) (j0 k : Nat)
    (seed C E : Q') (delta eta : Nat → Q') (hs0 : (0 : Q') ≤ seed) (hs1 : seed < (1 : Q'))
    (hC : (0 : Q') ≤ C) (hE0 : (0 : Q') ≤ E)
    (hd0 : ∀ n, (0 : Q') ≤ delta n) (hd1 : ∀ n, delta n ≤ (1 : Q'))
    (hcross_OPEN : ∀ n, n < k → delta n ≤ eta n)
    (hafδ_OPEN : ∀ n, k ≤ n → delta n ≤ C * (afGap (j0+n) * afGap (j0+n)))
    (hE : ∀ n, finSum (crossPart k eta) n ≤ E)
    (hbudget : E + C * (afA * afA) * inv (j0 + k + 2) < seed)
    (Phi : ∀ n, VacuumComplement (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1))
        (width := width (j0+n+1)) →
      VacuumComplement (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (width := width (j0+n)))
    (D : ∀ n, VacuumComplement (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1))
        (width := width (j0+n+1)) → RC)
    (hupper_OPEN : ∀ n y, RCle
      (completedInner (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (Phi n y).val (Phi n y).val)
      (completedInner (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1)) y.val y.val))
    (hschur_OPEN : ∀ n, SchurDecomposition (ns.nome_pos (j0+n+1)) (ns.nome_lt_one (j0+n+1))
      (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (width (j0+n+1)) (width (j0+n))
      (delta n) (Phi n) (D n))
    (hseed : WilsonVacuumSqContraction (ns.nome_pos j0) (ns.nome_lt_one j0) (width j0) seed)
    (n : Nat) :
    WilsonVacuumSqContraction (ns.nome_pos (j0+n)) (ns.nome_lt_one (j0+n)) (width (j0+n))
        (relativeRate seed delta n) ∧
      ((1 : Q') - seed) * (seed - (E + C * (afA * afA) * inv (j0 + k + 2))) ≤
        Q'.ofNat (2 ^ n) * latticeMarginOf (relativeRate seed delta) n := by
  have hB : (0 : Q') ≤ C * (afA * afA) * inv (j0 + k + 2) :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hC (Q'.mul_nonneg _ _ (by decide) (by decide)))
      (inv_nonneg _)
  exact ⟨scaleChain_contraction ns width j0 seed delta hs0 (Q'.le_of_lt hs1) hd0 hd1 Phi D
      hupper_OPEN hschur_OPEN hseed n,
    relativeRate_side_floor seed _ delta hs0 hs1 (Q'.le_trans' _ _ _ hE0
        (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (QPoly.q_add_zero_eqv E)) (Q'.add_le_add_left E _ _ hB)))
      hbudget hd0 hd1
      (crossover_prefix_budget_k C E hC j0 k delta eta hcross_OPEN hafδ_OPEN hE) n⟩

/-! ## (B) Non-uniform budget R* (decide) -/

/-- R*: `η = (2⁻²⁰, 1/100, 1/8, 1/64, 1/64, 1/64, …)` (only `n < 6` is used). -/
def etaRS : Nat → Q'
  | 0 => Q'.mkPos 1 1048576 (by decide)
  | 1 => Q'.mkPos 1 100 (by decide)
  | 2 => Q'.mkPos 1 8 (by decide)
  | _ => Q'.mkPos 1 64 (by decide)

/-- `E = 91/500 ≥ 2⁻²⁰ + 1/100 + 1/8 + 3/64 ≈ 0.1818760`. -/
def eRS : Q' := Q'.mkPos 91 500 (by decide)

private theorem tailRS : ∀ m, finSum (crossPart 6 etaRS) (m+6) ≤ eRS
  | 0 => by decide
  | m+1 => by
    have hz : crossPart 6 etaRS (m+6) = 0 := by
      unfold crossPart
      rw [if_neg (Nat.not_lt.mpr (Nat.le_add_left 6 m))]
    show finSum (crossPart 6 etaRS) (m+6) + crossPart 6 etaRS (m+6) ≤ _
    rw [hz]
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (QPoly.q_add_zero_eqv _)) (tailRS m)

private theorem headRS : ∀ n, n < 6 → finSum (crossPart 6 etaRS) n ≤ eRS := by decide

/-- **R* crossover budget (PROVED, decide + tail):** `∑_{n<6} η_n ≤ 91/500`. -/
theorem etaRS_budget (n : Nat) : finSum (crossPart 6 etaRS) n ≤ eRS := by
  by_cases h : n < 6
  · exact headRS n h
  · have e : n = (n - 6) + 6 := (Nat.sub_add_cancel (Nat.not_lt.mp h)).symm
    rw [e]; exact tailRS (n - 6)

/-- **R* budget (decide):** `91/500 + (1/10)·afA²/9 < 1/4` (`≈ 0.223904 < 0.25`). -/
theorem budget_RS_ok :
    eRS + Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (0 + 6 + 2) < timeRate := by decide

/-- **R* floor value (decide):** `(3/4)(1/4 − 91/500 − afA²/90) = 587159/30000000 ≈ 0.0195720`. -/
theorem floor_RS_value :
    Q'.eqv (((1 : Q') - timeRate) * (timeRate - (eRS + Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (0+6+2))))
      (Q'.mkPos 587159 30000000 (by decide)) := by decide

/-- The R* floor is positive (PROVED from `budget_RS_ok`). -/
theorem floor_RS_pos :
    (0 : Q') < ((1 : Q') - timeRate) *
      (timeRate - (eRS + Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (0+6+2))) :=
  crossover_floor_pos timeRate _ timeRate_lt_one budget_RS_ok

/-! ## (C) Crossover interface with the per-step budget -/

/-- **`hcross_unifRS` (OPEN).** Instance-B crossover hypothesis with the R* per-step budget. -/
def hcross_unifRS (Phi : PhiFamB) (f c : Nat → Q') : Prop :=
  (∀ n, n < 6 → SchurBudget (f n) (c n) (etaRS n)) ∧
    ∀ W n, n < 6 → fineAtB W n (f n) ∧ coarseAtB W n (Phi W n) (c n)

/-- `e ≤ e + (1 − e)·0` (PROVED). -/
theorem schurBudget_self_zero (e : Q') : SchurBudget e 0 e :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (QPoly.q_add_zero_eqv e))
    (Q'.add_le_add_left e _ _ (Q'.ge_of_eqv (Q'.mul_zero_eqv _)))

/-- **Coarse-constant-0 reduction for R* (PROVED).** -/
theorem hcross_unifRS_of_fine (Phi : PhiFamB)
    (hfine : ∀ n, n < 6 → ∀ W, fineAtB W n (etaRS n)) :
    hcross_unifRS Phi etaRS (fun _ => 0) :=
  ⟨fun n _ => schurBudget_self_zero (etaRS n),
    fun W n hn => ⟨hfine n hn W, coarseAtB_zero W n (Phi W n)⟩⟩

/-- **Monotonicity of the fine factor (PROVED):** `f ≤ f'` and `fineAtB W n f` give
`fineAtB W n f'`.  So the old `1/64` hypotheses imply the R* ones at steps 2–5. -/
theorem fineAtB_mono (W : Nat → Nat) (n : Nat) {f f' : Q'} (h : f ≤ f') :
    fineAtB W n f → fineAtB W n f' := by
  intro hf y
  exact RCle_trans (hf y) (RCscale_mono_scalar h (completedInner_nonnegative _ _ y.val))

/-! ## (D) Steps 0–1 at the stronger rates (paper: steps01 §2–3, §9.1) -/

/-- Step-0 rate `q₀ = 1/1024` (`e^m = 32`). -/
def q0RS : Q' := Q'.mkPos 1 1024 (by decide)

/-- Step-0 Dobrushin product at `e^m = 32`: `(12 + 2·32)·(79/10000) = 0.6004 ≤ 0.61` (decide).
Arithmetic only; the analytic input stays in `hDob_OPEN_q0`. -/
theorem dobrushin_q0 :
    ((12 : Q') + 2 * 32) * Q'.mkPos 79 10000 (by decide) ≤ Q'.mkPos 61 100 (by decide) := by decide

private theorem q0RS_mul_self : (q0RS * q0RS).eqv (etaRS 0) := by decide

/-- **Step 0 at `2⁻²⁰` (PROVED from the OPEN envelope):** `CentredPowerDecayVC` at rate `1/1024`
on nome index 1 of schedule B gives `fineAtB W 0 (2⁻²⁰)` at every width. -/
theorem fineAtB_step0_RS
    (hDob_OPEN_q0 : ∀ width, CentredPowerDecayVC (robust3UndershootScheduleB.nome_pos 1)
        (robust3UndershootScheduleB.nome_lt_one 1) width q0RS) :
    ∀ W, fineAtB W 0 (etaRS 0) := by
  intro W
  let hw0 := robust3UndershootScheduleB.nome_pos 1
  let hw1 := robust3UndershootScheduleB.nome_lt_one 1
  let width := W (0 + 0 + 1)
  have hq : (0 : Q') < q0RS := by decide
  have hEven := evenDecay_of_centredPowerDecayVC hw0 hw1 q0RS hq (hDob_OPEN_q0 width)
  have hTS := twoStepFactor_of_even_decay hw0 hw1 width q0RS hEven
  intro y
  have h := hTS y
  have hnn := completedInner_nonnegative hw0 hw1 y.val
  exact RCle_trans h (RCscale_mono_scalar (Q'.le_of_eqv q0RS_mul_self) hnn)

/-- Step-1 rate `q₁ = 1/10` (`e^m = √10`). -/
def q1RS : Q' := Q'.mkPos 1 10 (by decide)

/-- `3163/1000 ≥ √10` (decide; `3.163² = 10.004569`). -/
theorem sqrt10_le :
    (10 : Q') ≤ Q'.mkPos 3163 1000 (by decide) * Q'.mkPos 3163 1000 (by decide) := by decide

/-- `317/1000 ≥ 1/√10` (decide; `10·0.317² = 1.00489`). -/
theorem invSqrt10_le :
    (1 : Q') ≤ (10 : Q') * (Q'.mkPos 317 1000 (by decide) * Q'.mkPos 317 1000 (by decide)) := by
  decide

/-- Step-1 one-sided Dobrushin product at `e^m = √10`:
`(12 + 3.163 + 0.317)·0.0618 = 0.956664 ≤ 0.96` (decide).  Arithmetic only; the W₁ input stays
in `hDobW1_OPEN_q1`. -/
theorem dobrushin_W1_q1 :
    ((12 : Q') + Q'.mkPos 3163 1000 (by decide) + Q'.mkPos 317 1000 (by decide)) * cKappa1
      ≤ Q'.mkPos 96 100 (by decide) := by decide

private theorem q1RS_mul_self : (q1RS * q1RS).eqv (etaRS 1) := by decide

/-- **Step 1 at `1/100` (PROVED from the OPEN envelope):** `CentredPowerDecayVC` at rate `1/10`
on nome index 2 of schedule B gives `fineAtB W 1 (1/100)` at every width. -/
theorem fineAtB_step1_RS
    (hDobW1_OPEN_q1 : ∀ width, CentredPowerDecayVC (robust3UndershootScheduleB.nome_pos 2)
        (robust3UndershootScheduleB.nome_lt_one 2) width q1RS) :
    ∀ W, fineAtB W 1 (etaRS 1) := by
  intro W
  let hw0 := robust3UndershootScheduleB.nome_pos 2
  let hw1 := robust3UndershootScheduleB.nome_lt_one 2
  let width := W (0 + 1 + 1)
  have hq : (0 : Q') < q1RS := by decide
  have hEven := evenDecay_of_centredPowerDecayVC hw0 hw1 q1RS hq (hDobW1_OPEN_q1 width)
  have hTS := twoStepFactor_of_even_decay hw0 hw1 width q1RS hEven
  intro y
  have h := hTS y
  have hnn := completedInner_nonnegative hw0 hw1 y.val
  exact RCle_trans h (RCscale_mono_scalar (Q'.le_of_eqv q1RS_mul_self) hnn)

/-! ## (E) Step-2 bridge at the R* target (BRIDGE / OPEN) -/

/-- `KPToFineAt_BRIDGE_RS` [BRIDGE — OPEN analytic input; NOT in spec; no proof cited].
All-spin KP convergence with `6Ψ ≤ a` on the step-2 width ⇒ the instance-B two-step factor
`1/8`.  This needs a decay rate `m ≥ ln 8 / 4 ≈ 0.520` per lattice time slice; the existing
step-2 certificate gives only `≈ 0.0135` per slice, so this is genuinely open.  The polymer
quantities are uninterpreted (`SphereGasModel`).  Not chart closure. -/
def KPToFineAt_BRIDGE_RS (G : SphereGasModel) : Prop :=
  ∀ W : Nat → Nat, 8 ≤ W (0 + 2 + 1) → ∀ a P : Q', (6 : Q') * P ≤ a →
    G.kpAllSpin (W (0 + 2 + 1)) a P → fineAtB W 2 (Q'.mkPos 1 8 (by decide))

/-- The old bridge (factor `1/64`) implies the R* bridge (factor `1/8`) (PROVED, `fineAtB_mono`). -/
theorem KPToFineAt_BRIDGE_RS_of_B (G : SphereGasModel) :
    KPToFineAt_BRIDGE_B G → KPToFineAt_BRIDGE_RS G :=
  fun h W hW a P hP hkp =>
    fineAtB_mono W 2 (by decide : Q'.mkPos 1 64 (by decide) ≤ Q'.mkPos 1 8 (by decide))
      (h W hW a P hP hkp)

/-! ## (F) Floor on schedule B with R* -/

/-- Per-step cap for R*: `η_n` for `n < 6`, else `afGap(n)²/10`. -/
def capDeltaRS (n : Nat) : Q' :=
  if n < 6 then etaRS n else Q'.mkPos 1 10 (by decide) * (afGap (0+n) * afGap (0+n))

private theorem etaRS_nonneg : ∀ n, (0 : Q') ≤ etaRS n
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | _+3 => by show (0 : Q') ≤ Q'.mkPos 1 64 (by decide); decide

private theorem etaRS_le_one : ∀ n, etaRS n ≤ (1 : Q')
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | _+3 => by show Q'.mkPos 1 64 (by decide) ≤ (1 : Q'); decide

theorem capDeltaRS_nonneg (n : Nat) : (0 : Q') ≤ capDeltaRS n := by
  unfold capDeltaRS
  by_cases h : n < 6
  · rw [if_pos h]; exact etaRS_nonneg n
  · rw [if_neg h]
    have hg := Q'.le_of_lt (afGap_pos (0+n))
    exact Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ hg hg)

theorem capDeltaRS_le_one (n : Nat) : capDeltaRS n ≤ (1 : Q') := by
  unfold capDeltaRS
  by_cases h : n < 6
  · rw [if_pos h]; exact etaRS_le_one n
  · rw [if_neg h]
    have hg0 := Q'.le_of_lt (afGap_pos (0+n))
    have hg1 := Q'.le_of_lt (afGap_lt_one (0+n))
    have hsq : afGap (0+n) * afGap (0+n) ≤ (1 : Q') * 1 :=
      Q'.mul_le_mul_of_nonneg hg1 hg1 (by decide) hg0
    have h2 := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.mkPos 1 10 (by decide)) hsq (by decide)
    exact Q'.le_trans' _ _ _ h2 (by decide)

/-- Positivity of `aHK` on the schedule-B nomes. -/
def hposHKB (aHK : Q' → Q') : Prop := ∀ j, (0 : Q') < aHK (r3NomeB j)

/-- Spacing on `aHK` at the schedule-B nomes, `lo ≤ j ≤ hi` (OPEN for schedule B: `ρ₂, ρ₃` at
`279/500` need the Numerics recheck). -/
def hspacingHKB_win (aHK : Q' → Q') (lo hi : Nat) : Prop :=
  ∀ j, lo ≤ j → j ≤ hi → Q'.ofNat 2 * aHK (r3NomeB (j+1)) ≤ r3Rho j * aHK (r3NomeB j)

/-- Spacing on `aHK` at the schedule-B nomes off the window; OPEN. -/
def hspacingHKB_off (aHK : Q' → Q') (lo hi : Nat) : Prop :=
  ∀ j, (j < lo ∨ hi < j) → Q'.ofNat 2 * aHK (r3NomeB (j+1)) ≤ r3Rho j * aHK (r3NomeB j)

private theorem hspacingB_of_HK (aHK : Q' → Q') (lo hi : Nat) (hw : hspacingHKB_win aHK lo hi)
    (ho : hspacingHKB_off aHK lo hi) :
    ∀ i, Q'.ofNat 2 * (fun j => aHK (r3NomeB j)) (i+1) ≤ r3Rho i * (fun j => aHK (r3NomeB j)) i := by
  intro i
  by_cases h1 : i < lo
  · exact ho i (Or.inl h1)
  · by_cases h2 : hi < i
    · exact ho i (Or.inr h2)
    · exact hw i (Nat.le_of_not_lt h1) (Nat.le_of_not_lt h2)

/-- The seed on schedule B (`w_0 = 1/64 ≤ 1/55`, PROVED as `r3_seed`). -/
theorem r3_seedB (width : Nat) :
    WilsonVacuumSqContraction (robust3UndershootScheduleB.nome_pos 0)
      (robust3UndershootScheduleB.nome_lt_one 0) width timeRate :=
  uniformRate_of_guards _ _
    (scGuards_of_le_inv55 (Q'.le_of_lt (robust3UndershootScheduleB.nome_pos 0)) robust3B_join.1)
    width

private theorem step_dataRS (Phi : PhiFamB) (f c : Nat → Q') (hX : hcross_unifRS Phi f c)
    (hA : hafδ_unifB Phi f c) (W : Nat → Nat) (n : Nat) :
    fineAtB W n (f n) ∧ coarseAtB W n (Phi W n) (c n) ∧ SchurBudget (f n) (c n) (capDeltaRS n) := by
  by_cases h : n < 6
  · refine ⟨(hX.2 W n h).1, (hX.2 W n h).2, ?_⟩
    unfold capDeltaRS; rw [if_pos h]; exact hX.1 n h
  · have h6 : 6 ≤ n := Nat.le_of_not_lt h
    refine ⟨(hA.2 W n h6).1, (hA.2 W n h6).2, ?_⟩
    unfold capDeltaRS; rw [if_neg h]; exact hA.1 n h6

private theorem hschurB_of_spectral (Phi : PhiFamB) (f c : Nat → Q') (hX : hcross_unifRS Phi f c)
    (hA : hafδ_unifB Phi f c) (W : Nat → Nat) (n : Nat) :
    SchurDecomposition (robust3UndershootScheduleB.nome_pos (0+n+1))
      (robust3UndershootScheduleB.nome_lt_one (0+n+1))
      (robust3UndershootScheduleB.nome_pos (0+n)) (robust3UndershootScheduleB.nome_lt_one (0+n))
      (W (0+n+1)) (W (0+n)) (capDeltaRS n) (Phi W n)
      (schurSlack _ _ _ _ (W (0+n+1)) (W (0+n)) (capDeltaRS n) (Phi W n)) :=
  have hd := step_dataRS Phi f c hX hA W n
  schur_of_spectral _ _ _ _ _ _ (capDeltaRS n) (f n) (c n) (Phi W n) (capDeltaRS_le_one n)
    hd.1 hd.2.1 hd.2.2

/-- **Width-uniform floor on schedule B with R* (PROVED reduction from explicit OPEN inputs).**
OPEN: `hupper`, `hX` (`hcross_unifRS`), `hA` (`hafδ_unifB`), and the schedule-B spacing
hypotheses `hpos`, `hwin_MC`, `hoff_OPEN` on `aHK` (`ρ₂, ρ₃` at `279/500` are NOT rechecked;
they enter only as hypotheses).  Floor `587159/30000000 ≈ 0.0196` (`floor_RS_value`).
Not chart closure; not gap evidence. -/
theorem robust3B_floor_width_uniform_RS (Phi : PhiFamB) (f c : Nat → Q')
    (hupper : hupper_unifB Phi) (hX : hcross_unifRS Phi f c) (hA : hafδ_unifB Phi f c)
    (aHK : Q' → Q') (lo hi : Nat) (hpos : hposHKB aHK)
    (hwin_MC : hspacingHKB_win aHK lo hi) (hoff_OPEN : hspacingHKB_off aHK lo hi) :
    ∀ (W : Nat → Nat) (n : Nat),
      WilsonVacuumSqContraction (robust3UndershootScheduleB.nome_pos (0+n))
          (robust3UndershootScheduleB.nome_lt_one (0+n)) (W (0+n))
          (relativeRate timeRate capDeltaRS n) ∧
      ((1 : Q') - timeRate) *
          (timeRate - (eRS + Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (0+6+2)))
          * aHK (r3NomeB n) ≤
        (r3P * aHK (r3NomeB 0)) * latticeMarginOf (relativeRate timeRate capDeltaRS) n := by
  intro W n
  have hc := scaleChain_crossover_floor_k robust3UndershootScheduleB W 0 6 timeRate
    (Q'.mkPos 1 10 (by decide)) eRS capDeltaRS etaRS (Q'.le_of_lt timeRate_positive)
    timeRate_lt_one (by decide) (by decide) capDeltaRS_nonneg capDeltaRS_le_one
    (fun k hk => by unfold capDeltaRS; rw [if_pos hk]; exact Q'.le_refl' _)
    (fun k hk => by unfold capDeltaRS; rw [if_neg (Nat.not_lt.mpr hk)]; exact Q'.le_refl' _)
    etaRS_budget budget_RS_ok (Phi W)
    (fun n => schurSlack _ _ _ _ (W (0+n+1)) (W (0+n)) (capDeltaRS n) (Phi W n))
    (hupper W) (hschurB_of_spectral Phi f c hX hA W) (r3_seedB (W 0)) n
  refine ⟨hc.1, ?_⟩
  have hM := margin_nonneg_of_floor _ _ n floor_RS_pos hc.2
  have h := floor_physical (fun j => aHK (r3NomeB j)) r3Rho r3Omega
    (latticeMarginOf (relativeRate timeRate capDeltaRS)) _ (fun i => Q'.le_of_lt (hpos i))
    r3_omega_ge_one (hspacingB_of_HK aHK lo hi hwin_MC hoff_OPEN) r3_weight n hM hc.2
  rw [r3P_value.1] at h
  exact h

end YMGap.RG.Robust3CrossResplitB

#print axioms YMGap.RG.Robust3CrossResplitB.afPart_tail_budget
#print axioms YMGap.RG.Robust3CrossResplitB.crossover_prefix_budget_k
#print axioms YMGap.RG.Robust3CrossResplitB.scaleChain_crossover_floor_k
#print axioms YMGap.RG.Robust3CrossResplitB.etaRS_budget
#print axioms YMGap.RG.Robust3CrossResplitB.budget_RS_ok
#print axioms YMGap.RG.Robust3CrossResplitB.floor_RS_value
#print axioms YMGap.RG.Robust3CrossResplitB.floor_RS_pos
#print axioms YMGap.RG.Robust3CrossResplitB.schurBudget_self_zero
#print axioms YMGap.RG.Robust3CrossResplitB.hcross_unifRS_of_fine
#print axioms YMGap.RG.Robust3CrossResplitB.fineAtB_mono
#print axioms YMGap.RG.Robust3CrossResplitB.dobrushin_q0
#print axioms YMGap.RG.Robust3CrossResplitB.fineAtB_step0_RS
#print axioms YMGap.RG.Robust3CrossResplitB.sqrt10_le
#print axioms YMGap.RG.Robust3CrossResplitB.invSqrt10_le
#print axioms YMGap.RG.Robust3CrossResplitB.dobrushin_W1_q1
#print axioms YMGap.RG.Robust3CrossResplitB.fineAtB_step1_RS
#print axioms YMGap.RG.Robust3CrossResplitB.KPToFineAt_BRIDGE_RS_of_B
#print axioms YMGap.RG.Robust3CrossResplitB.capDeltaRS_nonneg
#print axioms YMGap.RG.Robust3CrossResplitB.capDeltaRS_le_one
#print axioms YMGap.RG.Robust3CrossResplitB.r3_seedB
#print axioms YMGap.RG.Robust3CrossResplitB.robust3B_floor_width_uniform_RS
