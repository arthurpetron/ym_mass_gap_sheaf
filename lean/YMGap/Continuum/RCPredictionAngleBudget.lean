/-
Scalar order bookkeeping for a prediction-covariance estimate.  The input
identity retains the nonnegative defect square; a pointwise upper bound on
the centered prediction covariance then yields a residual-pair lower bound.
-/

import YMGap.Continuum.RCSignedPairBudget
import YMGap.Continuum.RCScaleClose
import YMGap.Continuum.HamiltonianScalar
import YMGap.Constructive.HalfPow

namespace YMGap.Continuum.RCPredictionAngleBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_of_eq (Q'.zero_add' (A.approx n))))

private theorem rc_add_cancel_right (a b : RC) :
    RCadd (RCadd a b) (RCneg b) = a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 1)))
      (.var 0) (by decide) (fun | 0 => A.approx n | _ => B.approx n)))

private theorem rc_sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (CReal.sub_self_eqv_zero A)

private theorem rc_add_nonneg {a b : RC}
    (ha : RCnonneg a) (hb : RCnonneg b) : RCnonneg (RCadd a b) := by
  have h := RCadd_le_add ha hb
  rw [rc_zero_add] at h
  exact h

private theorem rc_sub_nonneg_of_le {a b : RC}
    (h : RCle b a) : RCnonneg (RCsub a b) := by
  have h' := RCadd_le_add h (RCle_refl (RCneg b))
  change RCle (RCsub b b) (RCsub a b) at h'
  rw [rc_sub_self] at h'
  exact h'

private theorem rc_scale_nonneg {s : Q'} (hs : (0 : Q') ≤ s)
    (a : RC) (ha : RCnonneg a) : RCnonneg (RCscale s a) := by
  change RCle RCzero (RCscale s a)
  rw [← RCscale_RCzero s]
  exact RCscale_mono hs ha

private theorem scale_congr {s t : Q'} (h : s ≈ t) (a : RC) :
    RCscale s a = RCscale t a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.mul_eqv_congr_right s t (A.approx n) h))

private theorem scale_factor (rho : Q') :
    (2 * (1 + rho)) * (HalfPow.half * rho) ≈ rho * (1 + rho) := by
  have hinner : (1 + rho) * (HalfPow.half * rho) ≈
      HalfPow.half * (rho * (1 + rho)) := by
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm
        (Q'.mul_assoc_eqv (1 + rho) HalfPow.half rho))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv (1 + rho) HalfPow.half))
        (Q'.eqv_trans _ _ _
          (Q'.mul_assoc_eqv HalfPow.half (1 + rho) rho)
          (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv (1 + rho) rho))))
  exact Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv 2 (1 + rho) (HalfPow.half * rho))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hinner)
      (Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv 2 HalfPow.half (rho * (1 + rho))))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _
            (by decide : (2 : Q') * HalfPow.half ≈ 1))
          (Q'.one_mul_eqv (rho * (1 + rho))))))

/-- A pointwise centered-prediction covariance budget implies the desired
residual-pair lower bound, provided the displayed defect-square identity
holds.  No projection-range or all-state estimate is assumed here. -/
theorem residual_lower (rho : Q') (hrho0 : (0 : Q') ≤ rho)
    (hrho1 : rho ≤ 1) (cross energy variance cov square : RC)
    (hsquare : RCnonneg square)
    (hcov : RCle (RCscale 2 cov) (RCscale rho variance))
    (hidentity : RCadd (RCscale (2 * (1 + rho)) cross)
        (RCscale (rho * (1 + rho)) energy) =
      RCadd (RCscale 2 square)
        (RCscale (1 + (-rho))
          (RCsub (RCscale rho variance) (RCscale 2 cov)))) :
    RCle (RCneg (RCscale (HalfPow.half * rho) energy)) cross := by
  have hfactor_nonneg : (0 : Q') ≤ 1 + (-rho) :=
    Q'.sub_nonneg_of_le hrho1
  have hcov_nonneg : RCnonneg
      (RCsub (RCscale rho variance) (RCscale 2 cov)) :=
    rc_sub_nonneg_of_le hcov
  have hsquare_scaled : RCnonneg (RCscale 2 square) :=
    rc_scale_nonneg (by decide) square hsquare
  have hcov_scaled : RCnonneg
      (RCscale (1 + (-rho))
        (RCsub (RCscale rho variance) (RCscale 2 cov))) :=
    rc_scale_nonneg hfactor_nonneg _ hcov_nonneg
  have hsum_nonneg : RCnonneg
      (RCadd (RCscale (2 * (1 + rho)) cross)
        (RCscale (rho * (1 + rho)) energy)) := by
    rw [hidentity]
    exact rc_add_nonneg hsquare_scaled hcov_scaled
  have hpositive : (0 : Q') < 2 * (1 + rho) :=
    Q'.mul_pos (by decide) (Q'.pos_add_nonneg (by decide) hrho0)
  have hfactorized :
      RCadd (RCscale (2 * (1 + rho)) cross)
        (RCscale (rho * (1 + rho)) energy) =
      RCscale (2 * (1 + rho))
        (RCadd cross (RCscale (HalfPow.half * rho) energy)) := by
    calc
      _ = RCadd (RCscale (2 * (1 + rho)) cross)
          (RCscale ((2 * (1 + rho)) * (HalfPow.half * rho)) energy) :=
        congrArg (fun z => RCadd (RCscale (2 * (1 + rho)) cross) z)
          (scale_congr (Q'.eqv_symm (scale_factor rho)) energy)
      _ = RCscale (2 * (1 + rho))
          (RCadd cross (RCscale (HalfPow.half * rho) energy)) := by
        rw [RCscale_RCadd, RCscale_RCscale]
  have hscaled_nonneg :
      RCnonneg (RCscale (2 * (1 + rho))
        (RCadd cross (RCscale (HalfPow.half * rho) energy))) := by
    rw [← hfactorized]
    exact hsum_nonneg
  have hinv_nonneg : (0 : Q') ≤ Q'.recipPos (2 * (1 + rho)) hpositive :=
    Q'.le_of_lt (Q'.recipPos_pos _ hpositive)
  have htarget_nonneg :
      RCnonneg (RCadd cross (RCscale (HalfPow.half * rho) energy)) := by
    have h := rc_scale_nonneg hinv_nonneg _ hscaled_nonneg
    rw [RCscale_RCscale] at h
    have hunit : Q'.eqv
        (Q'.recipPos (2 * (1 + rho)) hpositive * (2 * (1 + rho))) 1 :=
      Q'.eqv_trans _ _ _
        (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ hpositive)
    rw [scale_congr hunit, RCscale_one] at h
    exact h
  have hcancel := RCadd_le_add htarget_nonneg
    (RCle_refl (RCneg (RCscale (HalfPow.half * rho) energy)))
  change RCle (RCadd RCzero (RCneg (RCscale (HalfPow.half * rho) energy)))
    (RCadd (RCadd cross (RCscale (HalfPow.half * rho) energy))
      (RCneg (RCscale (HalfPow.half * rho) energy))) at hcancel
  rw [rc_zero_add, rc_add_cancel_right] at hcancel
  exact hcancel

#print axioms residual_lower

end YMGap.Continuum.RCPredictionAngleBudget
