/-
# Relative RG comparison must retain the actual shifted slow state

The state is the EXISTING original centered expression, box-smoothed and
advanced by side/2 on its original completed Wilson carrier. Shifted H1 and
the positive mixed-moment split imply its four-lag loss is at most four
times its one-lag loss. Fine TWO-step squared-norm loss is a FOUR-lag loss.

An actual relative comparison and the existing coarse time contraction then
force side*(1-delta)*(A-B) <= 4*c0*A. With an upper norm comparison and an
ordinary delta prefix budget D, the same bound holds with 1-D. No excitation
norm is divided, no retention is assumed, and no new structure is introduced.

These are NECESSARY constraints on a supplied comparison map. They construct
neither such a map nor the open AF window-survival input. They do not impose
the full coercive RG interface or prevent loss of fast/fringe states.
-/

import YMGap.Continuum.BF4WilsonAllNomeRGRelativeDissipation
import YMGap.Continuum.BF4WilsonAllNomeExprAnchorTrajectory
import YMGap.Constructive.FinSumAlg

namespace YMGap.Continuum.BF4WilsonAllNomeRGSlowStateRetention

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.RationalTail (finSum)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4DyadicWilsonSquare (side)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (Completion completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
  (VacuumComplement completedTime vacuumComplementTime completedInner_time_sum
   completedInner_time_contraction completedTime_zero)
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
  (mixedMoment mixedMoment_split defectPower)
open YMGap.Continuum.BF4WilsonAllNomeShiftedWindowSurvival (window_energy_antitone)
open YMGap.Continuum.BF4WilsonAllNomeShiftedH1Anchor (OneStepEpsBound)
open YMGap.Continuum.BF4WilsonAllNomeExprAnchorTrajectory
open YMGap.Continuum.BF4WilsonAllNomeRGRelativeDissipation
  (relative_comparison_iff_dissipation)
open YMGap.Continuum.RCSignedPairBudget (neg_mono scale_congr)
open YMGap.Continuum.RCPolynomialFunctional (rc_add_zero)

local infix:50 " ≈ " => Q'.eqv

private theorem sub_add_right (a b : RC) : RCsub (RCadd a b) a = b := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq (.add (.add (.var 0) (.var 1)) (.neg (.var 0)))
      (.var 1) (by decide) (fun | 0 => A.approx n | _ => B.approx n)))

private theorem sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.add_neg_self_eqv (A.approx n)))

private theorem forward_succ (a e : RC) (q : Q') :
    RCadd (RCadd a e) (RCscale q e) = RCadd a (RCscale (q+1) e) := by
  refine Quotient.inductionOn₂ a e ?_
  intro A E
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.mul (.var 2) (.var 1)))
      (.add (.var 0) (.mul (.add (.var 2) (.const 1)) (.var 1)))
      (by decide) (fun | 0 => A.approx n | 1 => E.approx n | _ => q)))

private theorem ofNat_nonnegative (n : Nat) : (0 : Q') ≤ Q'.ofNat n := by
  change (0 : Int)*1 ≤ (n : Int)*1
  simp only [Int.mul_one]
  exact Int.natCast_nonneg n

private theorem ofNat_succ (n : Nat) : Q'.ofNat (n+1) ≈ Q'.ofNat n+1 :=
  Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv n 1)
    (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_of_eq rfl))

private theorem finite_forward_telescope {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (width : Nat) (x : Completion hw0 hw1 width) :
    ∀ n, RCle (mixedMoment hw0 hw1 x 0 0)
      (RCadd (mixedMoment hw0 hw1 x n 0)
        (RCscale (Q'.ofNat n) (mixedMoment hw0 hw1 x 0 1))) := by
  intro n
  induction n with
  | zero =>
    rw [show Q'.ofNat 0 = (0 : Q') from rfl, RCPolynomialFunctional.rc_scale_zero, rc_add_zero]
    exact RCle_refl _
  | succ n ih =>
    have he := window_energy_antitone hw0 hw1 width x n 0
    rw [Nat.zero_add] at he
    have hstep : RCle (mixedMoment hw0 hw1 x n 0)
        (RCadd (mixedMoment hw0 hw1 x (n+1) 0) (mixedMoment hw0 hw1 x 0 1)) := by
      rw [mixedMoment_split hw0 hw1 x n 0]
      exact RCadd_le_add (RCle_refl _) he
    have h := RCle_trans ih (RCadd_le_add hstep
      (RCle_refl (RCscale (Q'.ofNat n) (mixedMoment hw0 hw1 x 0 1))))
    rw [forward_succ] at h
    rw [scale_congr (ofNat_succ n)]
    exact h

private theorem fourStep_loss_le {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (width : Nat) (x : Completion hw0 hw1 width) :
    RCle (RCsub (completedInner hw0 hw1 x x)
      (completedInner hw0 hw1 (completedTime hw0 hw1 2 x) (completedTime hw0 hw1 2 x)))
      (RCscale 4 (RCsub (completedInner hw0 hw1 x x)
        (completedInner hw0 hw1 x (completedTime hw0 hw1 1 x)))) := by
  have h := finite_forward_telescope hw0 hw1 width x 4
  have hsub := RCadd_le_add h (RCle_refl (RCneg (mixedMoment hw0 hw1 x 4 0)))
  change RCle (RCsub (mixedMoment hw0 hw1 x 0 0) (mixedMoment hw0 hw1 x 4 0))
    (RCsub (RCadd (mixedMoment hw0 hw1 x 4 0)
      (RCscale (Q'.ofNat 4) (mixedMoment hw0 hw1 x 0 1))) (mixedMoment hw0 hw1 x 4 0)) at hsub
  rw [sub_add_right] at hsub
  have he : mixedMoment hw0 hw1 x 0 1 =
      RCsub (mixedMoment hw0 hw1 x 0 0) (mixedMoment hw0 hw1 x 1 0) := by
    rw [mixedMoment_split hw0 hw1 x 0 0]
    exact (sub_add_right _ _).symm
  rw [he] at hsub
  simp only [mixedMoment, defectPower, completedTime_zero] at hsub
  rw [completedInner_time_sum hw0 hw1 2 2 x x]
  exact hsub

/-- The actual shifted original smoothed excitation, with its original
nome, width, expression and completed time retained. -/
def shiftedState (tr : ExprAnchorTrajectory) (j : Nat) :
    VacuumComplement (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (width := tr.width j) :=
  vacuumComplementTime (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (side j/2)
    (exprSmoothedState (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
      (tr.width j) (tr.expr j) (tr.radius j))

section Retention

variable (tr : ExprAnchorTrajectory) (j : Nat)
local notation "x" => Subtype.val (shiftedState tr j)
local notation "A" => completedInner (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) x x
local notation "F" => completedInner (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
  (completedTime (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) 2 x)
  (completedTime (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) 2 x)

/-- Four-lag loss of the actual shifted state is derived from shifted H1,
not assumed as another slow-state hypothesis. -/
theorem shiftedState_fourStep_loss (c0 : Q') (H1 : ExprShiftedEpsBound tr c0) :
    RCle (RCscale (Q'.ofNat (side j)) (RCsub A F)) (RCscale (4*c0) A) := by
  have h := RCscale_mono (ofNat_nonnegative (side j))
    (fourStep_loss_le (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (tr.width j) x)
  have hs := RCscale_mono (by decide : (0 : Q') ≤ 4) (H1 j)
  unfold OneStepEpsBound at hs
  rw [RCscale_RCscale] at h
  rw [RCscale_RCscale, RCscale_RCscale] at hs
  have hc : Q'.ofNat (side j)*4 ≈ 4*Q'.ofNat (side j) := Q'.mul_comm_eqv _ _
  rw [scale_congr hc] at h
  exact RCle_trans h hs

variable {wC : Q'} (hwC0 : (0 : Q') < wC) (hwC1 : wC < (1 : Q')) (widthC : Nat)
  (Phi : VacuumComplement (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
    (width := tr.width j) → VacuumComplement hwC0 hwC1 (width := widthC))

local notation "B" => completedInner hwC0 hwC1
  (Subtype.val (Phi (shiftedState tr j))) (Subtype.val (Phi (shiftedState tr j)))
local notation "C" => completedInner hwC0 hwC1
  (completedTime hwC0 hwC1 1 (Subtype.val (Phi (shiftedState tr j))))
  (completedTime hwC0 hwC1 1 (Subtype.val (Phi (shiftedState tr j))))

/-- Selective necessary norm retention. Only the ACTUAL shifted state is
tested; no lower norm comparison or nonzero-norm division is assumed. -/
theorem shiftedState_retention (c0 delta : Q') (H1 : ExprShiftedEpsBound tr c0)
    (hd : delta ≤ (1 : Q'))
    (hrelative : RCle F (RCadd (RCscale delta A) (RCscale ((1 : Q')-delta) C))) :
    RCle (RCscale (Q'.ofNat (side j)*((1 : Q')-delta)) (RCsub A B))
      (RCscale (4*c0) A) := by
  have hcb := completedInner_time_contraction hwC0 hwC1 1 (Phi (shiftedState tr j)).val
  have hsub := RCadd_le_add (RCle_refl A) (neg_mono hcb)
  have h := RCle_trans (RCscale_mono (Q'.sub_nonneg_of_le hd) hsub)
    ((relative_comparison_iff_dissipation delta A F C).mp hrelative)
  have hs := RCscale_mono (ofNat_nonnegative (side j)) h
  rw [RCscale_RCscale] at hs
  exact RCle_trans hs (shiftedState_fourStep_loss tr j c0 H1)

/-- An upper norm comparison and delta<=D give the same cleared necessary
retention with the uniform coefficient 1-D. -/
theorem shiftedState_retention_of_cap (c0 delta D : Q') (H1 : ExprShiftedEpsBound tr c0)
    (hD : D ≤ (1 : Q')) (hd : delta ≤ D) (hupper : RCle B A)
    (hrelative : RCle F (RCadd (RCscale delta A) (RCscale ((1 : Q')-delta) C))) :
    RCle (RCscale (Q'.ofNat (side j)*((1 : Q')-D)) (RCsub A B))
      (RCscale (4*c0) A) := by
  have hnonnegative := RCadd_le_add hupper (RCle_refl (RCneg B))
  change RCle (RCsub B B) (RCsub A B) at hnonnegative
  rw [sub_self] at hnonnegative
  have hcoeff := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat (side j))
    (Q'.add_le_add_left (1 : Q') _ _ (Q'.neg_le_neg hd)) (ofNat_nonnegative (side j))
  exact RCle_trans (RCscale_mono_scalar hcoeff hnonnegative)
    (shiftedState_retention tr j hwC0 hwC1 widthC Phi c0 delta H1
      (Q'.le_trans' _ _ _ hd hD) hrelative)

/-- Backward-window survival feeds the selective retention constraint
through the EXISTING shifted-H1 compiler. Survival remains an analytic input. -/
theorem shiftedState_retention_of_window (c0 theta delta : Q')
    (ht0 : (0 : Q') < theta) (ht1 : theta ≤ (1 : Q'))
    (hc0 : ((1 : Q')-theta)*Q'.ofNat 2 ≤ theta*c0) (hc1 : (1 : Q') ≤ c0)
    (Hw : ExprShiftedWindowSurvival tr theta) (hd : delta ≤ (1 : Q'))
    (hrelative : RCle F (RCadd (RCscale delta A) (RCscale ((1 : Q')-delta) C))) :
    RCle (RCscale (Q'.ofNat (side j)*((1 : Q')-delta)) (RCsub A B))
      (RCscale (4*c0) A) :=
  shiftedState_retention tr j hwC0 hwC1 widthC Phi c0 delta
    (exprShiftedEpsBound_of_windowSurvival tr c0 theta ht0 ht1 hc0 hc1 Hw) hd hrelative

end Retention

private theorem finSum_nonnegative (delta : Nat → Q') (hd : ∀ n, (0 : Q') ≤ delta n) :
    ∀ n, (0 : Q') ≤ finSum delta n
  | 0 => by change (0 : Q') ≤ 0; decide
  | n+1 => Q'.zero_le_add _ _ (finSum_nonnegative delta hd n) (hd n)

/-- Ordinary prefixes cap each relative error at the fine scale n+1.
The resulting denominator-cleared retention uses 1-D, not a norm inverse. -/
theorem shiftedState_retention_of_prefix (tr : ExprAnchorTrajectory) (n : Nat)
    {wC : Q'} (hwC0 : (0 : Q') < wC) (hwC1 : wC < (1 : Q')) (widthC : Nat)
    (Phi : VacuumComplement (tr.schedule.nome_pos (n+1)) (tr.schedule.nome_lt_one (n+1))
      (width := tr.width (n+1)) → VacuumComplement hwC0 hwC1 (width := widthC))
    (c0 D : Q') (delta : Nat → Q') (H1 : ExprShiftedEpsBound tr c0)
    (hD : D ≤ (1 : Q')) (hd : ∀ i, (0 : Q') ≤ delta i)
    (hprefix : ∀ i, finSum delta i ≤ D)
    (hupper : RCle
      (completedInner hwC0 hwC1 (Phi (shiftedState tr (n+1))).val (Phi (shiftedState tr (n+1))).val)
      (completedInner (tr.schedule.nome_pos (n+1)) (tr.schedule.nome_lt_one (n+1))
        (shiftedState tr (n+1)).val (shiftedState tr (n+1)).val))
    (hrelative : RCle
      (completedInner (tr.schedule.nome_pos (n+1)) (tr.schedule.nome_lt_one (n+1))
        (completedTime (tr.schedule.nome_pos (n+1)) (tr.schedule.nome_lt_one (n+1)) 2
          (shiftedState tr (n+1)).val)
        (completedTime (tr.schedule.nome_pos (n+1)) (tr.schedule.nome_lt_one (n+1)) 2
          (shiftedState tr (n+1)).val))
      (RCadd (RCscale (delta n)
        (completedInner (tr.schedule.nome_pos (n+1)) (tr.schedule.nome_lt_one (n+1))
          (shiftedState tr (n+1)).val (shiftedState tr (n+1)).val))
        (RCscale ((1 : Q')-delta n) (completedInner hwC0 hwC1
          (completedTime hwC0 hwC1 1 (Phi (shiftedState tr (n+1))).val)
          (completedTime hwC0 hwC1 1 (Phi (shiftedState tr (n+1))).val))))) :
    RCle (RCscale (Q'.ofNat (side (n+1))*((1 : Q')-D))
      (RCsub (completedInner (tr.schedule.nome_pos (n+1)) (tr.schedule.nome_lt_one (n+1))
        (shiftedState tr (n+1)).val (shiftedState tr (n+1)).val)
        (completedInner hwC0 hwC1 (Phi (shiftedState tr (n+1))).val (Phi (shiftedState tr (n+1))).val)))
      (RCscale (4*c0) (completedInner (tr.schedule.nome_pos (n+1)) (tr.schedule.nome_lt_one (n+1))
        (shiftedState tr (n+1)).val (shiftedState tr (n+1)).val)) := by
  have hterm : delta n ≤ finSum delta (n+1) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' (delta n))))
      (Q'.add_le_add_right _ _ (delta n) (finSum_nonnegative delta hd n))
  exact shiftedState_retention_of_cap tr (n+1) hwC0 hwC1 widthC Phi c0 (delta n) D H1 hD
    (Q'.le_trans' _ _ _ hterm (hprefix (n+1))) hupper hrelative

end YMGap.Continuum.BF4WilsonAllNomeRGSlowStateRetention

#print axioms YMGap.Continuum.BF4WilsonAllNomeRGSlowStateRetention.shiftedState
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGSlowStateRetention.shiftedState_fourStep_loss
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGSlowStateRetention.shiftedState_retention
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGSlowStateRetention.shiftedState_retention_of_cap
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGSlowStateRetention.shiftedState_retention_of_window
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGSlowStateRetention.shiftedState_retention_of_prefix
