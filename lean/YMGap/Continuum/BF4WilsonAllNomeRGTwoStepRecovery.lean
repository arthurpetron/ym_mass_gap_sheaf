/-
# Recovering a one-step Wilson contraction from a two-step bound

On the SAME literal-width completed Wilson carrier, self-adjoint time balance
and completed Cauchy--Schwarz give ||T x||^4 <= ||x||^2 ||T^2 x||^2.
Constructive square order reflection therefore converts a two-step factor
alpha <= r^4 into the actual one-step vacuum-square contraction at r.

The explicit rational rate (3+alpha)/4 avoids choosing an exact fourth root.
This closes an operator join, not the analytic RG input: no approximate RG
map, error summability, AF seed, scaling limit or continuum theory is supplied.
The old RgRateRelationκ requires the OPPOSITE inequality r^4 <= alpha;
it is not produced by the explicit rate used here.
-/

import YMGap.Continuum.BF4WilsonAllNomeRGStepComposition
import YMGap.Continuum.BF4WilsonAllNomeCompletedLogConvexity
import YMGap.Continuum.RCNonnegativeSquareReflection
import YMGap.Continuum.RGExplicitRationalRate

namespace YMGap.Continuum.BF4WilsonAllNomeRGTwoStepRecovery

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedLogConvexity
open YMGap.Continuum.BF4WilsonAllNomeExprMixRateContraction (WilsonVacuumSqContraction)
open YMGap.Continuum.BF4WilsonAllNomeRGStepComposition
open YMGap.Continuum.RGExplicitRationalRate

local infix:50 " ≈ " => Q'.eqv

private theorem mul_mono_left {a b c : RC} (ha : RCnonneg a) (hbc : RCle b c) :
    RCle (RCmul a b) (RCmul a c) := by
  refine Quotient.inductionOn₃ a b c ?_ ha hbc
  intro A B C ha hbc
  exact leEv_mul_nonneg_left ha hbc

private theorem fourth_scaled_square (r : Q') (a : RC) :
    RCmul a (RCscale ((r*r)*(r*r)) a) =
      RCmul (RCscale (r*r) a) (RCscale (r*r) a) := by
  refine Quotient.inductionOn a ?_
  intro A
  apply Quotient.sound
  exact SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.mul (.var 1) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0))) (.var 1)))
      (.mul (.mul (.mul (.var 0) (.var 0)) (.var 1))
            (.mul (.mul (.var 0) (.var 0)) (.var 1)))
      (by decide) (fun | 0 => r | _ => A.approx n))

/-- A two-step norm factor below r^4 gives a one-step norm contraction at r.
No positive norm floor, division, or survival assumption is needed. -/
theorem vacuumSq_of_twoStepFactor
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')} {width : Nat}
    (r alpha : Q') (hfactor : alpha ≤ (r*r)*(r*r))
    (H : WilsonVacuumSqTwoStepFactor hw0 hw1 width alpha) :
    WilsonVacuumSqContraction hw0 hw1 width r := by
  intro y
  have hnorm := completedInner_nonnegative hw0 hw1 y.val
  have hcs := completedInner_cauchySchwarz hw0 hw1 width y.val
    (completedTime hw0 hw1 2 y.val)
  have hdiag : completedInner hw0 hw1 y.val (completedTime hw0 hw1 2 y.val) =
      completedInner hw0 hw1 (completedTime hw0 hw1 1 y.val)
        (completedTime hw0 hw1 1 y.val) :=
    (completedInner_time_sum hw0 hw1 1 1 y.val y.val).symm
  rw [hdiag] at hcs
  have htwo := RCle_trans (H y) (RCscale_mono_scalar hfactor hnorm)
  have hsquare := RCle_trans hcs (mul_mono_left hnorm htwo)
  rw [fourth_scaled_square] at hsquare
  have hright : RCnonneg (RCscale (r*r) (completedInner hw0 hw1 y.val y.val)) := by
    have h := RCscale_mono (SumOfSquares.q_mul_self_nonneg r) hnorm
    rwa [RCscale_RCzero] at h
  exact RCsquare_le_reflect_right_nonnegative hright hsquare

/-- Computed rational recovery; alpha in [0,1] needs no exact-root witness. -/
theorem vacuumSq_explicitRate_of_twoStepFactor
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')} {width : Nat}
    (alpha : Q') (h0 : (0 : Q') ≤ alpha) (h1 : alpha ≤ (1 : Q'))
    (H : WilsonVacuumSqTwoStepFactor hw0 hw1 width alpha) :
    WilsonVacuumSqContraction hw0 hw1 width (explicitRate alpha) :=
  vacuumSq_of_twoStepFactor _ _ (factor_le_rate_fourth alpha h0 h1) H

/-- The actual RG quadratic comparison, when supplied, now feeds the actual
one-step Wilson contraction at a computed rate. The comparison is still OPEN. -/
theorem approxRg_transfers_explicitRate
    {wF wC : Q'} {hwF0 : (0 : Q') < wF} {hwF1 : wF < (1 : Q')}
    {hwC0 : (0 : Q') < wC} {hwC1 : wC < (1 : Q')}
    {widthF widthC : Nat} {epsilon kappa : Q'}
    (H : ApproxRgIntertwiner hwF0 hwF1 hwC0 hwC1 widthF widthC epsilon kappa)
    (rC : Q') (hc : WilsonVacuumSqContraction hwC0 hwC1 widthC rC)
    (h1 : kappa * (rC*rC + epsilon) ≤ (1 : Q')) :
    WilsonVacuumSqContraction hwF0 hwF1 widthF
      (explicitRate (kappa * (rC*rC + epsilon))) := by
  have h0 : (0 : Q') ≤ kappa * (rC*rC + epsilon) :=
    Q'.mul_nonneg _ _ (Q'.le_of_lt H.kappa_pos)
      (Q'.zero_le_add _ _ (SumOfSquares.q_mul_self_nonneg rC) H.epsilon_nonneg)
  exact vacuumSq_explicitRate_of_twoStepFactor _ h0 h1 (approxRg_transfers H rC hc)

/-- The computed rate has the required half-margin recurrence directly.
This does not assert the old opposite fourth-power rate relation. Its actual
consumer is `RGStepComposition.scaled_step_core`. -/
theorem explicitRate_margin_step (rC kappa epsilon : Q') :
    HalfPow.half * (HalfPow.half *
      (((1 : Q') - rC) + ((1 : Q') - rC) +
        -(((1 : Q') - rC) * ((1 : Q') - rC)) +
        -(effectiveRgDefect kappa epsilon rC))) ≤
      (1 : Q') - explicitRate (kappa * (rC*rC + epsilon)) := by
  have he : ((1 : Q') - rC) + ((1 : Q') - rC) +
      -(((1 : Q') - rC) * ((1 : Q') - rC)) +
      -(effectiveRgDefect kappa epsilon rC) ≈
        (1 : Q') - kappa * (rC*rC + epsilon) :=
    poly_identity_of_normal_eq
      (.add (.add (.add (.add (.const 1) (.neg (.var 0)))
        (.add (.const 1) (.neg (.var 0))))
        (.neg (.mul (.add (.const 1) (.neg (.var 0)))
          (.add (.const 1) (.neg (.var 0))))))
        (.neg (.add (.mul (.add (.var 1) (.neg (.const 1)))
          (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 2)))))
      (.add (.const 1) (.neg (.mul (.var 1)
        (.add (.mul (.var 0) (.var 0)) (.var 2)))))
      (by decide) (fun | 0 => rC | 1 => kappa | _ => epsilon)
  have hh : (HalfPow.half * HalfPow.half).eqv quarter := by decide
  have hq : (HalfPow.half * (HalfPow.half *
      (((1 : Q') - rC) + ((1 : Q') - rC) +
        -(((1 : Q') - rC) * ((1 : Q') - rC)) +
        -(effectiveRgDefect kappa epsilon rC)))).eqv
      (quarter * ((1 : Q') - kappa * (rC*rC + epsilon))) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hh)
        (Q'.mul_eqv_congr_left _ _ _ he))
  exact Q'.le_of_eqv (Q'.eqv_trans _ _ _ hq
    (Q'.eqv_symm (rate_margin (kappa * (rC*rC + epsilon)))))

end YMGap.Continuum.BF4WilsonAllNomeRGTwoStepRecovery

#print axioms YMGap.Continuum.BF4WilsonAllNomeRGTwoStepRecovery.vacuumSq_of_twoStepFactor
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGTwoStepRecovery.vacuumSq_explicitRate_of_twoStepFactor
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGTwoStepRecovery.approxRg_transfers_explicitRate
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGTwoStepRecovery.explicitRate_margin_step
