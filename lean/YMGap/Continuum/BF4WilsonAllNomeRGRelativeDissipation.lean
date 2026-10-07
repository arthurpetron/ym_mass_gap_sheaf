/-
# RG gap recovery from relative dissipated-norm comparison

On the actual original completed fine/coarse Wilson carriers, write
A=||x||_f^2, F=||Tf^2 x||_f^2 and C=||Tc Phi x||_c^2. The sufficient
comparison is F <= delta*A+(1-delta)*C, equivalently
(1-delta)*(A-C) <= A-F. An upper norm comparison for Phi and a coarse
contraction give alpha=delta+(1-delta)*rC^2. Its additive error is exactly
delta*(1-rC^2), not delta against the whole norm.

This changes the useful estimate to seek, not the original action or any
canonical field. No actual cross-action comparison or RG map is constructed.
The complete integrated middle spatial action and separate partitions still
have to be controlled. AF survival, physical scaling and Clay remain open.
-/

import YMGap.Continuum.BF4WilsonAllNomeRGTwoStepRecovery
import YMGap.Continuum.BF4WilsonAllNomeRGTimeSmoothingObstruction

namespace YMGap.Continuum.BF4WilsonAllNomeRGRelativeDissipation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (VacuumComplement completedTime)
open YMGap.Continuum.BF4WilsonAllNomeRGStepComposition (WilsonVacuumSqTwoStepFactor)
open YMGap.Continuum.BF4WilsonAllNomeExprMixRateContraction (WilsonVacuumSqContraction)
open YMGap.Continuum.BF4WilsonAllNomeRGTwoStepRecovery
  (vacuumSq_explicitRate_of_twoStepFactor)
open YMGap.Continuum.RGExplicitRationalRate (explicitRate rate_margin quarter)
open YMGap.Continuum.RCPolynomialFunctional (rc_scale_coeff_add)
open YMGap.Continuum.RCSignedPairBudget (scale_congr neg_mono)

local infix:50 " ≈ " => Q'.eqv

/-- The factor keeps the contraction deficit instead of charging delta to it. -/
def relativeFactor (delta r : Q') : Q' := delta + ((1 : Q') - delta) * (r*r)

theorem relativeFactor_error (delta r : Q') :
    relativeFactor delta r ≈ (1 : Q') * (r*r + delta*((1 : Q') - r*r)) :=
  poly_identity_of_normal_eq
    (.add (.var 0) (.mul (.add (.const 1) (.neg (.var 0))) (.mul (.var 1) (.var 1))))
    (.mul (.const 1) (.add (.mul (.var 1) (.var 1))
      (.mul (.var 0) (.add (.const 1) (.neg (.mul (.var 1) (.var 1)))))))
    (by decide) (fun | 0 => delta | _ => r)

theorem relativeFactor_nonnegative (delta r : Q')
    (hd0 : (0 : Q') ≤ delta) (hd1 : delta ≤ (1 : Q')) :
    (0 : Q') ≤ relativeFactor delta r :=
  Q'.zero_le_add _ _ hd0 (Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le hd1)
    (SumOfSquares.q_mul_self_nonneg r))

theorem relativeFactor_le_one (delta r : Q') (hd1 : delta ≤ (1 : Q'))
    (hr0 : (0 : Q') ≤ r) (hr1 : r ≤ (1 : Q')) :
    relativeFactor delta r ≤ (1 : Q') := by
  have hs : r*r ≤ (1 : Q') := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg hr1 hr1 (by decide) hr0) (by decide)
  have h := Q'.add_le_add_left delta _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ ((1 : Q') - delta) hs
      (Q'.sub_nonneg_of_le hd1))
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (poly_identity_of_normal_eq
    (.add (.var 0) (.mul (.add (.const 1) (.neg (.var 0))) (.const 1)))
    (.const 1) (by decide) (fun _ => delta)))

/-- The exact recovered margin. Relative error loses a fraction of the
coarse squared contraction deficit, not a bare additive margin. -/
theorem relativeRate_margin (delta r : Q') :
    (1 : Q') - explicitRate (relativeFactor delta r) ≈
      quarter * (((1 : Q') - delta) * ((1 : Q') - r*r)) :=
  Q'.eqv_trans _ _ _ (rate_margin _)
    (Q'.mul_eqv_congr_left _ _ _ (poly_identity_of_normal_eq
      (.add (.const 1) (.neg (.add (.var 0)
        (.mul (.add (.const 1) (.neg (.var 0))) (.mul (.var 1) (.var 1))))))
      (.mul (.add (.const 1) (.neg (.var 0)))
        (.add (.const 1) (.neg (.mul (.var 1) (.var 1)))))
      (by decide) (fun | 0 => delta | _ => r)))

private theorem sub_sub (A F : RC) : RCsub A (RCsub A F) = F := by
  refine Quotient.inductionOn₂ A F ?_
  intro a f
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq (.add (.var 0) (.neg (.add (.var 0) (.neg (.var 1)))))
      (.var 1) (by decide) (fun | 0 => a.approx n | _ => f.approx n)))

private theorem relative_rhs (delta : Q') (A C : RC) :
    RCsub A (RCscale ((1 : Q') - delta) (RCsub A C)) =
      RCadd (RCscale delta A) (RCscale ((1 : Q') - delta) C) := by
  refine Quotient.inductionOn₂ A C ?_
  intro a c
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.var 1) (.neg (.mul (.add (.const 1) (.neg (.var 0)))
        (.add (.var 1) (.neg (.var 2))))))
      (.add (.mul (.var 0) (.var 1))
        (.mul (.add (.const 1) (.neg (.var 0))) (.var 2)))
      (by decide) (fun | 0 => delta | 1 => a.approx n | _ => c.approx n)))

/-- Exact signed equivalence, before any action comparison or absolute bound. -/
theorem relative_comparison_iff_dissipation (delta : Q') (A F C : RC) :
    RCle F (RCadd (RCscale delta A) (RCscale ((1 : Q') - delta) C)) ↔
      RCle (RCscale ((1 : Q') - delta) (RCsub A C)) (RCsub A F) := by
  constructor
  · intro h
    rw [← relative_rhs delta A C] at h
    have hh := RCadd_le_add (RCle_refl A) (neg_mono h)
    change RCle (RCsub A (RCsub A (RCscale ((1 : Q') - delta) (RCsub A C))))
      (RCsub A F) at hh
    rwa [sub_sub] at hh
  · intro h
    have hh := RCadd_le_add (RCle_refl A) (neg_mono h)
    change RCle (RCsub A (RCsub A F))
      (RCsub A (RCscale ((1 : Q') - delta) (RCsub A C))) at hh
    rwa [sub_sub, relative_rhs] at hh

variable {wF wC : Q'} (hwF0 : (0 : Q') < wF) (hwF1 : wF < (1 : Q'))
  (hwC0 : (0 : Q') < wC) (hwC1 : wC < (1 : Q'))

/-- Relative loss comparison on the actual completed carriers. No lower
comparison, preservation of fringe norms, linearity or norm division. -/
theorem twoStepFactor_of_relative_comparison (widthF widthC : Nat) (delta rC : Q')
    (Phi : VacuumComplement hwF0 hwF1 (width := widthF) →
      VacuumComplement hwC0 hwC1 (width := widthC))
    (hd1 : delta ≤ (1 : Q'))
    (hupper : ∀ y, RCle
      (completedInner hwC0 hwC1 (Phi y).val (Phi y).val)
      (completedInner hwF0 hwF1 y.val y.val))
    (hrelative : ∀ y, RCle
      (completedInner hwF0 hwF1 (completedTime hwF0 hwF1 2 y.val)
        (completedTime hwF0 hwF1 2 y.val))
      (RCadd (RCscale delta (completedInner hwF0 hwF1 y.val y.val))
        (RCscale ((1 : Q') - delta) (completedInner hwC0 hwC1
          (completedTime hwC0 hwC1 1 (Phi y).val)
          (completedTime hwC0 hwC1 1 (Phi y).val)))))
    (hc : WilsonVacuumSqContraction hwC0 hwC1 widthC rC) :
    WilsonVacuumSqTwoStepFactor hwF0 hwF1 widthF (relativeFactor delta rC) := by
  intro y
  have hs := RCscale_mono (Q'.sub_nonneg_of_le hd1) (hc (Phi y))
  rw [RCscale_RCscale] at hs
  have hcoeff : (0 : Q') ≤ ((1 : Q') - delta)*(rC*rC) :=
    Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le hd1) (SumOfSquares.q_mul_self_nonneg rC)
  have hh := RCle_trans hs (RCscale_mono hcoeff (hupper y))
  have hsum := RCadd_le_add
    (RCle_refl (RCscale delta (completedInner hwF0 hwF1 y.val y.val))) hh
  rw [← rc_scale_coeff_add] at hsum
  exact RCle_trans (hrelative y) hsum

/-- The existing SAME-carrier recovery consumes the relative factor. Strict
positive dyadic margins still require the independent relative-error budget. -/
theorem contraction_of_relative_comparison (widthF widthC : Nat) (delta rC : Q')
    (Phi : VacuumComplement hwF0 hwF1 (width := widthF) →
      VacuumComplement hwC0 hwC1 (width := widthC))
    (hd0 : (0 : Q') ≤ delta) (hd1 : delta ≤ (1 : Q'))
    (hr0 : (0 : Q') ≤ rC) (hr1 : rC ≤ (1 : Q'))
    (hupper : ∀ y, RCle
      (completedInner hwC0 hwC1 (Phi y).val (Phi y).val)
      (completedInner hwF0 hwF1 y.val y.val))
    (hrelative : ∀ y, RCle
      (completedInner hwF0 hwF1 (completedTime hwF0 hwF1 2 y.val)
        (completedTime hwF0 hwF1 2 y.val))
      (RCadd (RCscale delta (completedInner hwF0 hwF1 y.val y.val))
        (RCscale ((1 : Q') - delta) (completedInner hwC0 hwC1
          (completedTime hwC0 hwC1 1 (Phi y).val)
          (completedTime hwC0 hwC1 1 (Phi y).val)))))
    (hc : WilsonVacuumSqContraction hwC0 hwC1 widthC rC) :
    WilsonVacuumSqContraction hwF0 hwF1 widthF (explicitRate (relativeFactor delta rC)) :=
  vacuumSq_explicitRate_of_twoStepFactor _ (relativeFactor_nonnegative delta rC hd0 hd1)
    (relativeFactor_le_one delta rC hd1 hr0 hr1)
    (twoStepFactor_of_relative_comparison hwF0 hwF1 hwC0 hwC1
      widthF widthC delta rC Phi hd1 hupper hrelative hc)

end YMGap.Continuum.BF4WilsonAllNomeRGRelativeDissipation

#print axioms YMGap.Continuum.BF4WilsonAllNomeRGRelativeDissipation.relativeFactor_error
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGRelativeDissipation.relativeFactor_nonnegative
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGRelativeDissipation.relativeFactor_le_one
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGRelativeDissipation.relativeRate_margin
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGRelativeDissipation.relative_comparison_iff_dissipation
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGRelativeDissipation.twoStepFactor_of_relative_comparison
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGRelativeDissipation.contraction_of_relative_comparison
