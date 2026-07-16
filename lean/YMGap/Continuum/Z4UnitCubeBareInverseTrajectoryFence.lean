/-
# The bare unit-cube map has no all-scale inverse trajectory in its corridor

The exact activity-matching coarse map is `B(w) = 2*w^4`.  On the checked
strong-coupling interval `0 <= w <= 1/2` it obeys the sharper contraction

    4 * B(w) <= w.

Consequently an exact inverse chain `w_k = B(w_{k+1})` grows by at least a
factor four at every fine step.  Starting at or above the derived anchor
`1/400`, four inverse steps already exceed `1/2`.  Thus the bare map cannot be
silently reversed into an all-scale ultraviolet trajectory inside the regime
where the present polymer estimates apply.  A physical fine flow must contain
new renormalized interactions or a different coupling coordinate.
-/

import YMGap.Continuum.Z4UnitCubeBareCouplingCorridor

namespace YMGap.Continuum.Z4UnitCubeBareInverseTrajectoryFence

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UnitCubeBareCouplingCorridor
open YMGap.Continuum.Z4UnitCubeBareCouplingShift

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.mul_num_cast, Q'.mul_den_cast,
               Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm];
             ac_rfl))

private theorem qpow_mono_base
    {lower upper : Q'} (hlower : (0 : Q') ≤ lower)
    (hle : lower ≤ upper) :
    ∀ exponent : Nat, lower ^ exponent ≤ upper ^ exponent
  | 0 => Q'.le_refl' 1
  | exponent + 1 => by
      have hupper : (0 : Q') ≤ upper :=
        Q'.le_trans' _ _ _ hlower hle
      show lower * lower ^ exponent ≤ upper * upper ^ exponent
      exact Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right
          lower upper (lower ^ exponent) hle
          (Q'.pow_nonneg lower hlower exponent))
        (Q'.mul_le_mul_of_nonneg_left
          (lower ^ exponent) (upper ^ exponent) upper
          (qpow_mono_base hlower hle exponent) hupper)

/-- On the entire checked corridor the exact bare block map contracts by at
least a factor four. -/
theorem four_mul_unitCubeBlockCoupling_le
    {coupling : Q'} (hnonnegative : (0 : Q') ≤ coupling)
    (hleHalf : coupling ≤ Q'.mkPos 1 2 (by decide)) :
    Q'.ofNat 4 * unitCubeBlockCoupling coupling ≤ coupling := by
  have hcube : coupling ^ 3 ≤
      (Q'.mkPos 1 2 (by decide)) ^ 3 :=
    qpow_mono_base hnonnegative hleHalf 3
  have hscaled : Q'.ofNat 8 * coupling ^ 3 ≤ (1 : Q') :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left
        (coupling ^ 3) ((Q'.mkPos 1 2 (by decide)) ^ 3)
        (Q'.ofNat 8) hcube (by decide))
      (by decide)
  have hmul :
      coupling * (Q'.ofNat 8 * coupling ^ 3) ≤ coupling * 1 :=
    Q'.mul_le_mul_of_nonneg_left _ _ coupling hscaled hnonnegative
  have hleft :
      Q'.ofNat 4 * unitCubeBlockCoupling coupling ≈
        coupling * (Q'.ofNat 8 * coupling ^ 3) := by
    unfold unitCubeBlockCoupling
    simp only [Q'.pow_succ, Q'.pow_zero]
    ring_qeqv
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hmul
      (Q'.le_of_eqv (Q'.mul_one_eqv coupling)))

/-- An exact inverse bare step in the checked corridor expands the coupling by
at least a factor four. -/
theorem exact_inverse_step_grows_four
    {coarse fine : Q'} (hfineNonnegative : (0 : Q') ≤ fine)
    (hfineHalf : fine ≤ Q'.mkPos 1 2 (by decide))
    (hstep : coarse ≈ unitCubeBlockCoupling fine) :
    Q'.ofNat 4 * coarse ≤ fine := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.mul_eqv_congr_left (Q'.ofNat 4) coarse
        (unitCubeBlockCoupling fine) hstep))
    (four_mul_unitCubeBlockCoupling_le hfineNonnegative hfineHalf)

/-- An all-scale exact inverse trajectory staying in the checked corridor. -/
def BareInverseCorridorTrajectory (trajectory : Nat → Q') : Prop :=
  (∀ step, (0 : Q') ≤ trajectory step) ∧
  (∀ step, trajectory step ≤ Q'.mkPos 1 2 (by decide)) ∧
  (∀ step,
    trajectory step ≈ unitCubeBlockCoupling (trajectory (step + 1)))

/-- Exact inverse iteration forces the explicit geometric lower bound
`4^steps * w_0 <= w_steps`. -/
theorem bareInverseCorridorTrajectory_growth
    {trajectory : Nat → Q'}
    (htrajectory : BareInverseCorridorTrajectory trajectory) :
    ∀ steps : Nat,
      (Q'.ofNat 4) ^ steps * trajectory 0 ≤ trajectory steps
  | 0 => Q'.le_of_eqv (Q'.one_mul_eqv (trajectory 0))
  | steps + 1 => by
      have hinduction :=
        bareInverseCorridorTrajectory_growth htrajectory steps
      have hscaled :
          Q'.ofNat 4 *
              ((Q'.ofNat 4) ^ steps * trajectory 0) ≤
            Q'.ofNat 4 * trajectory steps :=
        Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 4)
          hinduction (by decide)
      have hstep : Q'.ofNat 4 * trajectory steps ≤
          trajectory (steps + 1) :=
        exact_inverse_step_grows_four
          (htrajectory.1 (steps + 1))
          (htrajectory.2.1 (steps + 1))
          (htrajectory.2.2 steps)
      have hregroup :
          (Q'.ofNat 4) ^ (steps + 1) * trajectory 0 ≈
            Q'.ofNat 4 *
              ((Q'.ofNat 4) ^ steps * trajectory 0) := by
        rw [Q'.pow_succ]
        exact Q'.mul_assoc_eqv _ _ _
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv hregroup)
        (Q'.le_trans' _ _ _ hscaled hstep)

/-- Four inverse steps from the derived anchor already leave the checked
`w <= 1/2` corridor.  Hence no infinite exact inverse bare trajectory can
start at or above the anchor while retaining the hypotheses of the current
strong-coupling construction. -/
theorem no_bare_inverse_corridor_trajectory_from_anchor :
    ¬ ∃ trajectory : Nat → Q',
      BareInverseCorridorTrajectory trajectory ∧
        anchorCoupling ≤ trajectory 0 := by
  intro hexists
  rcases hexists with ⟨trajectory, htrajectory, hanchor⟩
  have hpowNonnegative :
      (0 : Q') ≤ (Q'.ofNat 4) ^ 4 :=
    Q'.pow_nonneg _ (by decide) 4
  have hanchorScaled :
      (Q'.ofNat 4) ^ 4 * anchorCoupling ≤
        (Q'.ofNat 4) ^ 4 * trajectory 0 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hanchor hpowNonnegative
  have hgrowth := bareInverseCorridorTrajectory_growth htrajectory 4
  have hupper := htrajectory.2.1 4
  have himpossible :
      (Q'.ofNat 4) ^ 4 * anchorCoupling ≤
        Q'.mkPos 1 2 (by decide) :=
    Q'.le_trans' _ _ _ hanchorScaled
      (Q'.le_trans' _ _ _ hgrowth hupper)
  have hnot :
      ¬ ((Q'.ofNat 4) ^ 4 * anchorCoupling ≤
        Q'.mkPos 1 2 (by decide)) := by
    unfold anchorCoupling
    decide
  exact hnot himpossible

end YMGap.Continuum.Z4UnitCubeBareInverseTrajectoryFence

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4UnitCubeBareInverseTrajectoryFence.four_mul_unitCubeBlockCoupling_le
#print axioms YMGap.Continuum.Z4UnitCubeBareInverseTrajectoryFence.exact_inverse_step_grows_four
#print axioms YMGap.Continuum.Z4UnitCubeBareInverseTrajectoryFence.bareInverseCorridorTrajectory_growth
#print axioms YMGap.Continuum.Z4UnitCubeBareInverseTrajectoryFence.no_bare_inverse_corridor_trajectory_from_anchor
