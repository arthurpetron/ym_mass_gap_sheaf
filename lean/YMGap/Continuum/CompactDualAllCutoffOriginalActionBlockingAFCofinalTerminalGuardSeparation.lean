/-
# AF terminal laws lie outside both existing strong-coupling guards

The directed terminal carriers of the AF cofinal block family have coupling
`afNomeSchedule.nome (depth + 1)`.  Every such nome is already greater than
`1/2`, hence strictly greater than the strong-coupling cutoff-tail anchor
`1/400`.  The existing anchor-dominated cutoff modulus therefore cannot be
instantiated at any AF terminal law.  The existing heat-ratio thermodynamic
guard also fails at every AF terminal law.

This is an applicability obstruction, not a divergence theorem.  It does not
show that terminal laws fail to be Cauchy, and it supplies no arbitrary-nome
cutoff estimate, coupling-variation estimate, signed telescope, continuum
limit, spectral gap, or Clay theorem.

Constructive contract: rational cross-multiplication and previously checked
AF schedule facts only; no choice, `Classical`, `native_decide`, `sorry`,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingAFCofinalTerminalCarrier
import YMGap.Continuum.BF4WilsonAllNomeRGStepComposition
import YMGap.Continuum.Z4CouplingParametricCutoffTail

namespace
  YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingAFCofinalTerminalGuardSeparation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory
open YMGap.Continuum.BF4WilsonAllNomeRGStepComposition
open YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingAFCofinalTerminalCarrier
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

private theorem q_lt_of_lt_of_le_local
    {left middle right : Q'}
    (hleft : left < middle) (hright : middle ≤ right) :
    left < right := by
  have firstCross :
      left.num * (middle.den : Int) <
        middle.num * (left.den : Int) := hleft
  have secondCross :
      middle.num * (right.den : Int) ≤
        right.num * (middle.den : Int) := hright
  show left.num * (right.den : Int) <
    right.num * (left.den : Int)
  have rightDenPos : (0 : Int) < (right.den : Int) := by
    exact_mod_cast right.den_pos
  have leftDenNonnegative : (0 : Int) ≤ (left.den : Int) := by
    exact_mod_cast Nat.zero_le _
  have firstScaled :
      (left.num * (right.den : Int)) * (middle.den : Int) <
        (middle.num * (left.den : Int)) * (right.den : Int) := by
    have raw := Int.mul_lt_mul_of_pos_right firstCross rightDenPos
    have rearrange :
        (left.num * (middle.den : Int)) * (right.den : Int) =
          (left.num * (right.den : Int)) * (middle.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc,
        Int.mul_comm (middle.den : Int) (right.den : Int)]
    rwa [rearrange] at raw
  have secondScaled :
      (middle.num * (left.den : Int)) * (right.den : Int) ≤
        (right.num * (left.den : Int)) * (middle.den : Int) := by
    have raw := Int.mul_le_mul_of_nonneg_left secondCross leftDenNonnegative
    have leftRearrange :
        (left.den : Int) * (middle.num * (right.den : Int)) =
          (middle.num * (left.den : Int)) * (right.den : Int) := by
      rw [Int.mul_comm middle.num (left.den : Int), Int.mul_assoc]
    have rightRearrange :
        (left.den : Int) * (right.num * (middle.den : Int)) =
          (right.num * (left.den : Int)) * (middle.den : Int) := by
      rw [Int.mul_comm right.num (left.den : Int), Int.mul_assoc]
    rwa [leftRearrange, rightRearrange] at raw
  have chain :
      (left.num * (right.den : Int)) * (middle.den : Int) <
        (right.num * (left.den : Int)) * (middle.den : Int) :=
    Int.lt_of_lt_of_le firstScaled secondScaled
  exact Int.lt_of_mul_lt_mul_right chain
    (by exact_mod_cast Nat.zero_le middle.den)

/-! ## 1. Exact terminal coupling range -/

theorem half_lt_afTerminalCoupling (depth : Nat) :
    half < (afTerminalData depth).coupling := by
  rw [afTerminalData_coupling]
  exact q_lt_of_lt_of_le_local afNome_zero_gt_half
    (afNome_ge_zero (depth + 1))

theorem anchorCoupling_lt_afTerminalCoupling (depth : Nat) :
    anchorCoupling < (afTerminalData depth).coupling := by
  exact q_lt_of_lt_of_le_local
    (by decide : anchorCoupling < half)
    (Q'.le_of_lt (half_lt_afTerminalCoupling depth))

theorem afTerminalCoupling_not_le_anchorCoupling (depth : Nat) :
    ¬ ((afTerminalData depth).coupling ≤ anchorCoupling) := by
  intro hle
  have impossible :
      (afTerminalData depth).coupling <
        (afTerminalData depth).coupling :=
    Q'.lt_of_le_of_lt hle
      (anchorCoupling_lt_afTerminalCoupling depth)
  exact Int.lt_irrefl _ impossible

/-! ## 2. Exact guard incompatibilities -/

theorem no_afTerminalCoupling_cutoffTailGuard (depth : Nat) :
    ¬ ((0 : Q') ≤ (afTerminalData depth).coupling ∧
      (afTerminalData depth).coupling ≤ anchorCoupling) := by
  intro guards
  exact afTerminalCoupling_not_le_anchorCoupling depth guards.2

theorem afTerminalCoupling_not_heatRatio_le_half (depth : Nat) :
    ¬ (heatRatio (afTerminalData depth).coupling ≤ half) := by
  rw [afTerminalData_coupling]
  exact not_heatRatio_le_half_afNome (depth + 1)

theorem no_afTerminalCoupling_parametricThermodynamicGuards (depth : Nat) :
    ¬ ((0 : Q') ≤ (afTerminalData depth).coupling ∧
      (afTerminalData depth).coupling < (1 : Q') ∧
      heatRatio (afTerminalData depth).coupling ≤ half) := by
  intro guards
  exact afTerminalCoupling_not_heatRatio_le_half depth guards.2.2

/-! ## Axiom audit -/

#print axioms half_lt_afTerminalCoupling
#print axioms anchorCoupling_lt_afTerminalCoupling
#print axioms afTerminalCoupling_not_le_anchorCoupling
#print axioms no_afTerminalCoupling_cutoffTailGuard
#print axioms afTerminalCoupling_not_heatRatio_le_half
#print axioms no_afTerminalCoupling_parametricThermodynamicGuards

end
  YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingAFCofinalTerminalGuardSeparation
