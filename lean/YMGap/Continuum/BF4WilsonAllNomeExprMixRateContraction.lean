/-
# The Wilson carrier's own all-vector contraction feeds the Expr gap-branch slot (RETARGET PLUMBING)

Companion to `audits/SCOPE-WILSON-CARRIER-GAP-RETARGET-2026-10-06.md`. ADDITIVE.

SCOPE. The all-nome literal-width Wilson completion ALREADY has an all-vector strict
squared-norm contraction on its vacuum complement, `completed_oneStep_norm_gap`
(`BF4WilsonAllNomeCompletedGap`). It holds for every `0 < w < 1` and every width, with rate
`mixRate(w,width) = 1 − kineticFloor/kineticCap < 1`. This file only restates it in the
gap-branch shapes:
* `WilsonVacuumSqContraction r`: the all-vector shape, the same shape as the cube
  `…StrictContractionData.contraction`.
* `wilsonVacuumSqContraction_mixRate`: that shape holds at `r = mixRate`.
* `orbitContraction_of_vacuumSq`: all-vector ⇒ orbit, by specialization.
* `expr_orbitContraction_mixRate`: `ExprPathOrbitContraction tr mixRate`, UNCONDITIONALLY
  for every Expr trajectory.
* `exprCenteredContractionLower_mixRate`: with `r = mixRate`, the ONLY remaining field of
  `ExprCenteredContractionLower` is the lower margin `m·2^-j ≤ 1 − mixRate_j`, i.e.
  `m·2^-j ≤ mixFraction_j`.

NO PROGRESS on the gap input. The lower margin is the mass-gap content and stays OPEN. The
existing Doeblin-type fraction `kineticFloor/kineticCap` is not shown, and is not expected, to
be `≥ m·2^-j` along a trajectory.

Constructive, no external library; axioms `propext`, `Quot.sound` only.
-/

import YMGap.Continuum.BF4WilsonAllNomeExprTwoSidedBand
import YMGap.Continuum.BF4WilsonAllNomeCompletedGap

namespace YMGap.Continuum.BF4WilsonAllNomeExprMixRateContraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4DyadicWilsonSquare (spacing)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
  (Completion completedInner completedInner_symm unitState)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
  (completedTime completedTime_zero completedTime_add VacuumComplement
   completedTime_preserves_vacuumComplement)
open YMGap.Continuum.BF4WilsonAllNomeCompletedGap (completed_oneStep_norm_gap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
  (mixRate mixRate_nonnegative mixRate_lt_one)
open YMGap.Continuum.BF4WilsonAllNomeWindowGapCompatibility (OrbitContraction)
open YMGap.Continuum.BF4WilsonAllNomeExprAnchorTrajectory
open YMGap.Continuum.BF4WilsonAllNomeExprWindowGapCompatibility (ExprPathOrbitContraction)
open YMGap.Continuum.BF4WilsonAllNomeExprTwoSidedBand (ExprCenteredContractionLower)

section Carrier

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1

/-- All-vector squared-norm contraction on the Wilson vacuum complement (same shape as the
cube `CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData.contraction`). -/
def WilsonVacuumSqContraction (r : Q') : Prop :=
  ∀ y : VacuumComplement hw0 hw1 (width := width),
    RCle (B (T 1 y.val) (T 1 y.val)) (RCscale (r*r) (B y.val y.val))

/-- The existing all-nome Wilson strict contraction, at `r = mixRate(w,width) < 1`. -/
theorem wilsonVacuumSqContraction_mixRate :
    WilsonVacuumSqContraction hw0 hw1 width (mixRate hw0 hw1 width) := fun y => by
  have h := completed_oneStep_norm_gap hw0 hw1 width 0 y.val
    ((completedInner_symm hw0 hw1 y.val _).trans y.property)
  rw [completedTime_zero hw0 hw1] at h
  exact h

/-- All-vector ⇒ orbit contraction of any vacuum-complement vector (specialization). -/
theorem orbitContraction_of_vacuumSq (r : Q') (H : WilsonVacuumSqContraction hw0 hw1 width r)
    (x : V) (hx : B (unitState hw0 hw1 width) x = RCzero) :
    OrbitContraction hw0 hw1 width x r := fun k => by
  have h := H ⟨T k x, completedTime_preserves_vacuumComplement hw0 hw1 k x hx⟩
  change RCle (B (T 1 (T k x)) (T 1 (T k x))) (RCscale (r*r) (B (T k x) (T k x))) at h
  rw [← completedTime_add hw0 hw1 1 k x, Nat.add_comm 1 k] at h
  exact h

end Carrier

/-- **Unconditional**: every Expr anchor orbit contracts at the Wilson rate `mixRate`. -/
theorem expr_orbitContraction_mixRate (tr : ExprAnchorTrajectory) :
    ExprPathOrbitContraction tr
      (fun j => mixRate (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (tr.width j)) :=
  fun j => orbitContraction_of_vacuumSq (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
    (tr.width j) _ (wilsonVacuumSqContraction_mixRate _ _ _) (tr.state j)
    (exprSmoothedState (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (tr.width j)
      (tr.expr j) (tr.radius j)).property

/-- With `r = mixRate`, the gap-branch input reduces EXACTLY to its lower margin (OPEN). -/
theorem exprCenteredContractionLower_mixRate (tr : ExprAnchorTrajectory) (m : Q')
    (hm : (0 : Q') < m)
    (hlow : ∀ j, m * spacing j ≤
      (1 : Q') - mixRate (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (tr.width j)) :
    ExprCenteredContractionLower tr
      (fun j => mixRate (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (tr.width j)) m :=
  { contraction := expr_orbitContraction_mixRate tr
    rate_nonneg := fun _ => mixRate_nonnegative _ _ _
    rate_le_one := fun _ => Q'.le_of_lt (mixRate_lt_one _ _ _)
    floor_pos := hm
    lowerRate := hlow }

#print axioms WilsonVacuumSqContraction
#print axioms wilsonVacuumSqContraction_mixRate
#print axioms orbitContraction_of_vacuumSq
#print axioms expr_orbitContraction_mixRate
#print axioms exprCenteredContractionLower_mixRate

end YMGap.Continuum.BF4WilsonAllNomeExprMixRateContraction
