import YMGap.RG.Robust3SchurRankOne

/-!
# Robust3: width-uniform floor from a volume-uniform crossover hypothesis `hcross_unif`

Implements `audits/SCOPE-HCROSS-UNIF-2026-11-16.md`. `Phi` (and, in the Schur form, `D`) are indexed by the width
function `W : Nat → Nat`; `delta` (here `capDelta`), `f`, `c` and every constant are independent of `W`. The conclusion
holds at **every** width with the **same** rate and floor: the width-`W(n)` carrier contraction at the W-independent rate
`relativeRate timeRate capDelta n`, and `floor·aHK(w_n) ≤ (P₃·aHK(w_0))·latticeMargin_n`. (The floor inequality alone does
not mention `W`; the contraction conjunct is what carries the width-uniform carrier content.)

Open hypotheses of `robust3_floor_width_uniform` (all W-uniform): `hupper_unif`, `hcross_unif` (steps `n < 6`: fine factor,
coarse attainment, budget at `1/64`), `hafδ_unif` (steps `n ≥ 6`, budget at `afGap²/10`), and the heat-kernel spacing binders
`hpos`, `hwin_MC`, `hoff_OPEN`.

**U(1) remark.** U(1) passing the finite-volume `hcross` (task2n: ≤ 12 sites, δ_min ≤ 1.2e-4; numerical) gives hypotheses
at ONE width only; it does NOT give `hcross_unif`, which quantifies over all `W` with `W`-independent `f, c`. U(1) is expected to
FAIL `hcross_unif` at step 2 (0.35 → 0.56, across the Villain transition; task2n estimate, not run). So `hcross_unif` is the
place where non-abelian content enters. Additive; the existing `hcross_OPEN` is not edited. Not chart closure.
-/

namespace YMGap.RG.Robust3CrossUniform

set_option autoImplicit false

open YMGap.Constructive YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (VacuumComplement completedTime)
open YMGap.Continuum.BF4WilsonAllNomeRGStepComposition (WilsonVacuumSqTwoStepFactor latticeMarginOf)
open YMGap.Continuum.BF4WilsonAllNomeRGDissipationBudget (relativeRate)
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory (afGap afA)
open YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay (timeRate)
open YMGap.RG.RelativeDissipationScaleChain (SchurDecomposition inv)
open YMGap.RG.DyadicCrossoverInstance (eDy)
open YMGap.RG.Robust3UndershootAfSchedule (robust3UndershootSchedule r3Nome)
open YMGap.RG.Robust3UndershootPhysicalUnits (r3P)
open YMGap.RG.Robust3UndershootCrossoverInstance (etaR3 robust3_crossover_instance)
open YMGap.Continuum.BF4WilsonAllNomeExprMixRateContraction (WilsonVacuumSqContraction)
open YMGap.RG.Robust3SpacingHeatKernel
  (hposHK hspacingHK_win hspacingHK_off robust3_physical_floor_noMargin_HK)
open YMGap.RG.Robust3SchurRankOne
  (SchurBudget schurSlack schur_of_spectral capDelta capDelta_nonneg capDelta_le_one)

/-- Vacuum complement of the Robust3 carrier at scale `j` and width `W j`. -/
abbrev VC (W : Nat → Nat) (j : Nat) :=
  VacuumComplement (robust3UndershootSchedule.nome_pos j) (robust3UndershootSchedule.nome_lt_one j) (width := W j)

/-- Width-indexed RG maps `Φ_W,n : VC_W(n+1) → VC_W(n)`. -/
abbrev PhiFam := ∀ (W : Nat → Nat) (n : Nat), VC W (0+n+1) → VC W (0+n)

/-- Fine two-step factor `f` at width `W`, step `n`. -/
def fineAt (W : Nat → Nat) (n : Nat) (f : Q') : Prop :=
  WilsonVacuumSqTwoStepFactor (robust3UndershootSchedule.nome_pos (0+n+1))
    (robust3UndershootSchedule.nome_lt_one (0+n+1)) (W (0+n+1)) f

/-- Coarse attainment `c‖y‖² ≤ ‖T_C(1)Φy‖²` at width `W`, step `n`. -/
def coarseAt (W : Nat → Nat) (n : Nat) (Phi : VC W (0+n+1) → VC W (0+n)) (c : Q') : Prop :=
  ∀ y, RCle (RCscale c (completedInner (robust3UndershootSchedule.nome_pos (0+n+1))
      (robust3UndershootSchedule.nome_lt_one (0+n+1)) y.val y.val))
    (completedInner (robust3UndershootSchedule.nome_pos (0+n)) (robust3UndershootSchedule.nome_lt_one (0+n))
      (completedTime (robust3UndershootSchedule.nome_pos (0+n)) (robust3UndershootSchedule.nome_lt_one (0+n)) 1
        (Phi y).val)
      (completedTime (robust3UndershootSchedule.nome_pos (0+n)) (robust3UndershootSchedule.nome_lt_one (0+n)) 1
        (Phi y).val))

/-- `hupper` at every width: `‖Φ_W,n y‖_C ≤ ‖y‖_F`. -/
def hupper_unif (Phi : PhiFam) : Prop :=
  ∀ W n (y : VC W (0+n+1)), RCle
    (completedInner (robust3UndershootSchedule.nome_pos (0+n)) (robust3UndershootSchedule.nome_lt_one (0+n))
      (Phi W n y).val (Phi W n y).val)
    (completedInner (robust3UndershootSchedule.nome_pos (0+n+1)) (robust3UndershootSchedule.nome_lt_one (0+n+1))
      y.val y.val)

/-- **`hcross_unif` (OPEN, volume-uniform crossover).** For the six crossover steps: W-independent budget at `1/64`, and
the fine factor `f n` and coarse attainment `c n` at EVERY width `W`. -/
def hcross_unif (Phi : PhiFam) (f c : Nat → Q') : Prop :=
  (∀ n, n < 6 → SchurBudget (f n) (c n) (etaR3 n)) ∧
    ∀ W n, n < 6 → fineAt W n (f n) ∧ coarseAt W n (Phi W n) (c n)

/-- **`hafδ_unif` (OPEN, volume-uniform AF steps).** Same for `n ≥ 6`, budget at `afGap(n)²/10`. -/
def hafδ_unif (Phi : PhiFam) (f c : Nat → Q') : Prop :=
  (∀ n, 6 ≤ n → SchurBudget (f n) (c n) (Q'.mkPos 1 10 (by decide) * (afGap (0+n) * afGap (0+n)))) ∧
    ∀ W n, 6 ≤ n → fineAt W n (f n) ∧ coarseAt W n (Phi W n) (c n)

/-- Per-step spectral data from the two uniform hypotheses (PROVED). -/
theorem step_data (Phi : PhiFam) (f c : Nat → Q') (hX : hcross_unif Phi f c) (hA : hafδ_unif Phi f c)
    (W : Nat → Nat) (n : Nat) :
    fineAt W n (f n) ∧ coarseAt W n (Phi W n) (c n) ∧ SchurBudget (f n) (c n) (capDelta n) := by
  by_cases h : n < 6
  · refine ⟨(hX.2 W n h).1, (hX.2 W n h).2, ?_⟩
    unfold capDelta; rw [if_pos h]; exact hX.1 n h
  · have h6 : 6 ≤ n := Nat.le_of_not_lt h
    refine ⟨(hA.2 W n h6).1, (hA.2 W n h6).2, ?_⟩
    unfold capDelta; rw [if_neg h]; exact hA.1 n h6

/-- **Width-uniform Schur decomposition (PROVED from the uniform hypotheses).** `D_W,n := schurSlack`, δ := `capDelta`
(independent of `W`). -/
theorem hschur_unif_of_spectral (Phi : PhiFam) (f c : Nat → Q') (hX : hcross_unif Phi f c)
    (hA : hafδ_unif Phi f c) (W : Nat → Nat) (n : Nat) :
    SchurDecomposition (robust3UndershootSchedule.nome_pos (0+n+1)) (robust3UndershootSchedule.nome_lt_one (0+n+1))
      (robust3UndershootSchedule.nome_pos (0+n)) (robust3UndershootSchedule.nome_lt_one (0+n)) (W (0+n+1)) (W (0+n))
      (capDelta n) (Phi W n) (schurSlack _ _ _ _ (W (0+n+1)) (W (0+n)) (capDelta n) (Phi W n)) :=
  have hd := step_data Phi f c hX hA W n
  schur_of_spectral _ _ _ _ _ _ (capDelta n) (f n) (c n) (Phi W n) (capDelta_le_one n) hd.1 hd.2.1 hd.2.2

/-- **Width-uniform floor, Schur form (PROVED reduction).** `Phi`, `D` indexed by width; `delta` and the caps independent of
width; the conclusion holds at every `W` with the same right-hand side. -/
theorem robust3_floor_width_uniform_schur (delta : Nat → Q')
    (hd0 : ∀ n, (0 : Q') ≤ delta n) (hd1 : ∀ n, delta n ≤ (1 : Q'))
    (hcross_OPEN : ∀ n, n < 6 → delta n ≤ etaR3 n)
    (hafδ_OPEN : ∀ n, 6 ≤ n → delta n ≤ Q'.mkPos 1 10 (by decide) * (afGap (0+n) * afGap (0+n)))
    (Phi : PhiFam) (D : ∀ (W : Nat → Nat) (n : Nat), VC W (0+n+1) → RC)
    (hupper : hupper_unif Phi)
    (hschur_unif_OPEN : ∀ (W : Nat → Nat) n, SchurDecomposition (robust3UndershootSchedule.nome_pos (0+n+1))
      (robust3UndershootSchedule.nome_lt_one (0+n+1)) (robust3UndershootSchedule.nome_pos (0+n))
      (robust3UndershootSchedule.nome_lt_one (0+n)) (W (0+n+1)) (W (0+n)) (delta n) (Phi W n) (D W n))
    (aHK : Q' → Q') (lo hi : Nat) (hpos : hposHK aHK)
    (hwin_MC : hspacingHK_win aHK lo hi) (hoff_OPEN : hspacingHK_off aHK lo hi) :
    ∀ (W : Nat → Nat) (n : Nat),
      WilsonVacuumSqContraction (robust3UndershootSchedule.nome_pos (0+n))
          (robust3UndershootSchedule.nome_lt_one (0+n)) (W (0+n)) (relativeRate timeRate delta n) ∧
      ((1 : Q') - timeRate) * (timeRate -
          (eDy + Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (0+2))) * aHK (r3Nome n) ≤
        (r3P * aHK (r3Nome 0)) * latticeMarginOf (relativeRate timeRate delta) n :=
  fun W n => ⟨(robust3_crossover_instance W delta hd0 hd1 hcross_OPEN hafδ_OPEN (Phi W) (D W)
      (hupper W) (hschur_unif_OPEN W) n).1,
    robust3_physical_floor_noMargin_HK W delta hd0 hd1 hcross_OPEN hafδ_OPEN (Phi W) (D W)
      (hupper W) (hschur_unif_OPEN W) aHK lo hi hpos hwin_MC hoff_OPEN n⟩

/-- **Width-uniform floor from spectral data (PROVED reduction; wires `hcross_unif` into the `lmax` form).**
Open: `hupper_unif`, `hcross_unif`, `hafδ_unif`, `hpos`, `hwin_MC`, `hoff_OPEN`. δ = `capDelta`, `f`, `c` and all constants are
W-independent; the conclusion holds at every width `W` with the same floor and the same right-hand side.
U(1): finite-volume `hcross` (one width) does not give `hcross_unif`; U(1) is expected to fail it at step 2. -/
theorem robust3_floor_width_uniform (Phi : PhiFam) (f c : Nat → Q')
    (hupper_unif_OPEN : hupper_unif Phi)
    (hcross_unif_OPEN : hcross_unif Phi f c) (hafδ_unif_OPEN : hafδ_unif Phi f c)
    (aHK : Q' → Q') (lo hi : Nat) (hpos : hposHK aHK)
    (hwin_MC : hspacingHK_win aHK lo hi) (hoff_OPEN : hspacingHK_off aHK lo hi) :
    ∀ (W : Nat → Nat) (n : Nat),
      WilsonVacuumSqContraction (robust3UndershootSchedule.nome_pos (0+n))
          (robust3UndershootSchedule.nome_lt_one (0+n)) (W (0+n)) (relativeRate timeRate capDelta n) ∧
      ((1 : Q') - timeRate) * (timeRate -
          (eDy + Q'.mkPos 1 10 (by decide) * (afA * afA) * inv (0+2))) * aHK (r3Nome n) ≤
        (r3P * aHK (r3Nome 0)) * latticeMarginOf (relativeRate timeRate capDelta) n :=
  robust3_floor_width_uniform_schur capDelta capDelta_nonneg capDelta_le_one
    (fun k hk => by unfold capDelta; rw [if_pos hk]; exact Q'.le_refl' _)
    (fun k hk => by unfold capDelta; rw [if_neg (Nat.not_lt.mpr hk)]; exact Q'.le_refl' _)
    Phi (fun W n => schurSlack _ _ _ _ (W (0+n+1)) (W (0+n)) (capDelta n) (Phi W n)) hupper_unif_OPEN
    (hschur_unif_of_spectral Phi f c hcross_unif_OPEN hafδ_unif_OPEN) aHK lo hi hpos hwin_MC hoff_OPEN

end YMGap.RG.Robust3CrossUniform
