/-
# Coarse-constant-0 reduction for `hcross_unif`

When the coarse attainment constant is identically zero, `coarseAt` is the
trivial comparison `0 · ‖y‖² ≤ ‖T_C(1) Φ y‖²`. The left side is `RCzero` and the
right side is nonnegative by `completedInner_nonnegative`, so the inequality
holds for every width, step and RG map.

Combined with the algebraic Schur budget check `1/64 ≤ 1/64 + (1−1/64)·0`, a
fine-factor hypothesis for the six crossover steps yields `hcross_unif` at
`(f,c) = (1/64, 0)`.

Additive; Mathlib-free. Does not discharge the fine factor, does not claim
chart closure, and does not edit existing proofs or statements.
-/

import YMGap.RG.Robust3CrossUniform
import YMGap.Constructive.SumOfSquares
import YMGap.Constructive.FinSumAlg
import YMGap.Constructive.QPoly

namespace YMGap.RG.CoarseConstantZero

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.SumOfSquares
open YMGap.Constructive.QPoly (q_add_zero_eqv)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner completedInner_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (VacuumComplement completedTime)
open YMGap.RG.Robust3UndershootAfSchedule (robust3UndershootSchedule)
open YMGap.RG.Robust3UndershootCrossoverInstance (etaR3)
open YMGap.RG.Robust3SchurRankOne (SchurBudget)
open YMGap.RG.Robust3CrossUniform
  (VC PhiFam fineAt coarseAt hcross_unif)

/-- `0 · a = 0` on `RC`. Local clone of the private lemma in
`BF4WilsonAllNomePlaquetteFamilyKineticUpper`; not exported from there. -/
private theorem RCscale_zero (a : RC) : RCscale (0 : Q') a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.zero_mul_eqv (A.approx n)))

/-- Coarse attainment at constant `0` holds for every width, step and map:
`RCscale 0 (‖y‖²) = 0 ≤ ‖T_C(1) Φ y‖²` by `completedInner_nonnegative`. -/
theorem coarseAt_zero (W : Nat → Nat) (n : Nat)
    (Phi : VC W (0 + n + 1) → VC W (0 + n)) :
    coarseAt W n Phi 0 := by
  intro y
  let hw0 := robust3UndershootSchedule.nome_pos (0 + n)
  let hw1 := robust3UndershootSchedule.nome_lt_one (0 + n)
  let hw0F := robust3UndershootSchedule.nome_pos (0 + n + 1)
  let hw1F := robust3UndershootSchedule.nome_lt_one (0 + n + 1)
  change RCle
    (RCscale (0 : Q') (completedInner hw0F hw1F y.val y.val))
    (completedInner hw0 hw1
      (completedTime hw0 hw1 1 (Phi y).val)
      (completedTime hw0 hw1 1 (Phi y).val))
  rw [RCscale_zero]
  exact completedInner_nonnegative hw0 hw1
    (completedTime hw0 hw1 1 (Phi y).val)

/-- Algebraic Schur budget at fine factor `1/64`, coarse constant `0`, and
δ = η_R3(n) = 1/64: `1/64 ≤ 1/64 + (1 − 1/64)·0`. -/
theorem schurBudget_fine_zero (_n : Nat) :
    SchurBudget (Q'.mkPos 1 64 (by decide)) 0 (etaR3 _n) := by
  unfold SchurBudget etaR3
  -- Goal: 1/64 ≤ 1/64 + (1 - 1/64) * 0.
  have hz : (((1 : Q') - Q'.mkPos 1 64 (by decide)) * (0 : Q')).eqv (0 : Q') :=
    Q'.mul_zero_eqv _
  have hadd :
      (Q'.mkPos 1 64 (by decide) +
          ((1 : Q') - Q'.mkPos 1 64 (by decide)) * (0 : Q')).eqv
        (Q'.mkPos 1 64 (by decide)) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ hz)
      (q_add_zero_eqv _)
  exact Q'.le_trans' _ _ _
    (Q'.le_refl' (Q'.mkPos 1 64 (by decide)))
    (Q'.le_of_eqv (Q'.eqv_symm hadd))

/-- One crossover step: a fine-factor hypothesis at every width, together with
`coarseAt_zero` and `schurBudget_fine_zero`, yields the per-step conjunct of
`hcross_unif` at `(f,c)=(1/64,0)`. -/
theorem hcross_step_of_fine (Phi : PhiFam) (n : Nat) (_hn : n < 6)
    (hfine : ∀ W : Nat → Nat, fineAt W n (Q'.mkPos 1 64 (by decide))) :
    SchurBudget (Q'.mkPos 1 64 (by decide)) 0 (etaR3 n) ∧
      ∀ W, fineAt W n (Q'.mkPos 1 64 (by decide)) ∧
        coarseAt W n (Phi W n) 0 := by
  refine ⟨schurBudget_fine_zero n, fun W => ?_⟩
  exact ⟨hfine W, coarseAt_zero W n (Phi W n)⟩

/-- Uniform crossover hypothesis from a fine-factor hypothesis on the six
crossover steps: `hcross_unif Phi (fun _ => 1/64) (fun _ => 0)`. -/
theorem hcross_unif_of_fine (Phi : PhiFam)
    (hfine : ∀ n, n < 6 → ∀ W, fineAt W n (Q'.mkPos 1 64 (by decide))) :
    hcross_unif Phi (fun _ => Q'.mkPos 1 64 (by decide)) (fun _ => 0) := by
  refine ⟨fun n hn => schurBudget_fine_zero n, fun W n hn => ?_⟩
  exact ⟨hfine n hn W, coarseAt_zero W n (Phi W n)⟩

end YMGap.RG.CoarseConstantZero

/-! ## Axiom audit -/

#print axioms YMGap.RG.CoarseConstantZero.coarseAt_zero
#print axioms YMGap.RG.CoarseConstantZero.schurBudget_fine_zero
#print axioms YMGap.RG.CoarseConstantZero.hcross_step_of_fine
#print axioms YMGap.RG.CoarseConstantZero.hcross_unif_of_fine
