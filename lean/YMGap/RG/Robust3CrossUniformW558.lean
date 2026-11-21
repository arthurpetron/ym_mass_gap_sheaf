/-
# Robust3 width-uniform crossover interface, instance B (step-2 fine nome `279/500`)

**Label: definitions (OPEN interface) plus PROVED transfer lemmas. NOT gap evidence, NOT chart
closure.**  Additive copy of the `Robust3CrossUniform` interface (`VC`, `PhiFam`, `fineAt`,
`coarseAt`, `hupper_unif`, `hcross_unif`, `hafδ_unif`) over `robust3UndershootScheduleB`, whose
only changed nome is index 3 (`279/500`).  `etaR3`, `SchurBudget`, `afGap` are reused unchanged.

PROVED here:
* `fineAtB_iff`: for `n ≠ 2` the instance-B fine factor is literally the original one (same nome,
  proofs irrelevant).  Only step 2 changes meaning.
* `coarseAtB_zero`, `hcross_unifB_of_fine`: the coarse-constant-0 reduction (copy of
  `CoarseConstantZero`) — a fine-factor hypothesis on the six crossover steps yields
  `hcross_unifB` at `(f,c) = (1/64, 0)`.

The floor theorems of `Robust3CrossUniform` are NOT copied.  The original module is untouched.
Constructive, no external library; axioms within `propext`, `Quot.sound`.
-/

import YMGap.RG.Robust3UndershootAfScheduleW558
import YMGap.RG.CoarseConstantZero

namespace YMGap.RG.Robust3CrossUniformW558

set_option autoImplicit false

open YMGap.Constructive YMGap.Constructive.CReal
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner completedInner_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (VacuumComplement completedTime)
open YMGap.Continuum.BF4WilsonAllNomeRGStepComposition (WilsonVacuumSqTwoStepFactor)
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory (afGap)
open YMGap.RG.Robust3UndershootAfSchedule (robust3UndershootSchedule)
open YMGap.RG.Robust3UndershootAfScheduleW558 (robust3UndershootScheduleB robust3B_nome_eq)
open YMGap.RG.Robust3UndershootCrossoverInstance (etaR3)
open YMGap.RG.Robust3SchurRankOne (SchurBudget)
open YMGap.RG.Robust3CrossUniform (fineAt)
open YMGap.RG.CoarseConstantZero (schurBudget_fine_zero)

/-- Vacuum complement of the instance-B carrier at scale `j` and width `W j`. -/
abbrev VCB (W : Nat → Nat) (j : Nat) :=
  VacuumComplement (robust3UndershootScheduleB.nome_pos j) (robust3UndershootScheduleB.nome_lt_one j)
    (width := W j)

/-- Width-indexed instance-B RG maps `Φ_W,n : VCB_W(n+1) → VCB_W(n)`. -/
abbrev PhiFamB := ∀ (W : Nat → Nat) (n : Nat), VCB W (0+n+1) → VCB W (0+n)

/-- Instance-B fine two-step factor `f` at width `W`, step `n`. -/
def fineAtB (W : Nat → Nat) (n : Nat) (f : Q') : Prop :=
  WilsonVacuumSqTwoStepFactor (robust3UndershootScheduleB.nome_pos (0+n+1))
    (robust3UndershootScheduleB.nome_lt_one (0+n+1)) (W (0+n+1)) f

/-- Instance-B coarse attainment `c‖y‖² ≤ ‖T_C(1)Φy‖²`. -/
def coarseAtB (W : Nat → Nat) (n : Nat) (Phi : VCB W (0+n+1) → VCB W (0+n)) (c : Q') : Prop :=
  ∀ y, RCle (RCscale c (completedInner (robust3UndershootScheduleB.nome_pos (0+n+1))
      (robust3UndershootScheduleB.nome_lt_one (0+n+1)) y.val y.val))
    (completedInner (robust3UndershootScheduleB.nome_pos (0+n))
      (robust3UndershootScheduleB.nome_lt_one (0+n))
      (completedTime (robust3UndershootScheduleB.nome_pos (0+n))
        (robust3UndershootScheduleB.nome_lt_one (0+n)) 1 (Phi y).val)
      (completedTime (robust3UndershootScheduleB.nome_pos (0+n))
        (robust3UndershootScheduleB.nome_lt_one (0+n)) 1 (Phi y).val))

/-- Instance-B `hupper` at every width. -/
def hupper_unifB (Phi : PhiFamB) : Prop :=
  ∀ W n (y : VCB W (0+n+1)), RCle
    (completedInner (robust3UndershootScheduleB.nome_pos (0+n))
      (robust3UndershootScheduleB.nome_lt_one (0+n)) (Phi W n y).val (Phi W n y).val)
    (completedInner (robust3UndershootScheduleB.nome_pos (0+n+1))
      (robust3UndershootScheduleB.nome_lt_one (0+n+1)) y.val y.val)

/-- **`hcross_unifB` (OPEN).** Instance-B volume-uniform crossover hypothesis. -/
def hcross_unifB (Phi : PhiFamB) (f c : Nat → Q') : Prop :=
  (∀ n, n < 6 → SchurBudget (f n) (c n) (etaR3 n)) ∧
    ∀ W n, n < 6 → fineAtB W n (f n) ∧ coarseAtB W n (Phi W n) (c n)

/-- **`hafδ_unifB` (OPEN).** Instance-B volume-uniform AF steps. -/
def hafδ_unifB (Phi : PhiFamB) (f c : Nat → Q') : Prop :=
  (∀ n, 6 ≤ n → SchurBudget (f n) (c n) (Q'.mkPos 1 10 (by decide) * (afGap (0+n) * afGap (0+n)))) ∧
    ∀ W n, 6 ≤ n → fineAtB W n (f n) ∧ coarseAtB W n (Phi W n) (c n)

/-- The two-step factor depends on its nome only through its value (proof irrelevance). -/
theorem twoStepFactor_congr {w w' : Q'} (e : w = w') (hw0 : 0 < w) (hw1 : w < 1)
    (hw0' : 0 < w') (hw1' : w' < 1) (width : Nat) (f : Q') :
    WilsonVacuumSqTwoStepFactor hw0 hw1 width f ↔ WilsonVacuumSqTwoStepFactor hw0' hw1' width f := by
  subst e; exact Iff.rfl

/-- **Only step 2 changes (PROVED).** For `n ≠ 2` the instance-B fine factor is the original. -/
theorem fineAtB_iff (W : Nat → Nat) (n : Nat) (f : Q') (h : n ≠ 2) : fineAtB W n f ↔ fineAt W n f := by
  have h3 : 0 + n + 1 ≠ 3 := fun e => h (by rw [Nat.zero_add] at e; exact Nat.succ.inj e)
  exact twoStepFactor_congr (robust3B_nome_eq (0+n+1) h3) _ _ _ _ _ _

/-- `0 · a = 0` on `RC` (local clone; the original in `CoarseConstantZero` is private). -/
private theorem RCscale_zeroB (a : RC) : RCscale (0 : Q') a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.zero_mul_eqv (A.approx n)))

/-- Instance-B coarse attainment at constant `0` holds for every width, step and map (PROVED). -/
theorem coarseAtB_zero (W : Nat → Nat) (n : Nat) (Phi : VCB W (0 + n + 1) → VCB W (0 + n)) :
    coarseAtB W n Phi 0 := by
  intro y
  let hw0 := robust3UndershootScheduleB.nome_pos (0 + n)
  let hw1 := robust3UndershootScheduleB.nome_lt_one (0 + n)
  let hw0F := robust3UndershootScheduleB.nome_pos (0 + n + 1)
  let hw1F := robust3UndershootScheduleB.nome_lt_one (0 + n + 1)
  change RCle
    (RCscale (0 : Q') (completedInner hw0F hw1F y.val y.val))
    (completedInner hw0 hw1
      (completedTime hw0 hw1 1 (Phi y).val)
      (completedTime hw0 hw1 1 (Phi y).val))
  rw [RCscale_zeroB]
  exact completedInner_nonnegative hw0 hw1 (completedTime hw0 hw1 1 (Phi y).val)

/-- **Coarse-constant-0 reduction, instance B (PROVED).** -/
theorem hcross_unifB_of_fine (Phi : PhiFamB)
    (hfine : ∀ n, n < 6 → ∀ W, fineAtB W n (Q'.mkPos 1 64 (by decide))) :
    hcross_unifB Phi (fun _ => Q'.mkPos 1 64 (by decide)) (fun _ => 0) := by
  refine ⟨fun n _ => schurBudget_fine_zero n, fun W n hn => ?_⟩
  exact ⟨hfine n hn W, coarseAtB_zero W n (Phi W n)⟩

end YMGap.RG.Robust3CrossUniformW558

#print axioms YMGap.RG.Robust3CrossUniformW558.fineAtB_iff
#print axioms YMGap.RG.Robust3CrossUniformW558.coarseAtB_zero
#print axioms YMGap.RG.Robust3CrossUniformW558.hcross_unifB_of_fine
