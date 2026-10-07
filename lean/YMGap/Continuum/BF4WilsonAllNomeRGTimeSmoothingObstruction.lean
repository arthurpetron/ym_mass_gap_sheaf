/-
# Positive-time smoothing cannot supply the original RG coercive comparison

At every positive fine width the actual centered boundary plaquette has
nonzero norm and is killed by one original completed time step. Consequently
any zero-preserving postprocessing of a positive-time image fails the
coercive lower bound of `ApproxRgIntertwiner`, independently of linearity,
coarse nome/width, distortion or additive error.

This prunes producers for the FULL coercive RG interface. Its lower bound
is unnecessary for the gap transfer: the minimal transfer theorem below
uses only a norm upper comparison and the two-step comparison. Thus a map
that loses fringe norms can still supply this smaller analytic producer.
No existing frontier field is changed and no comparison is constructed.
-/

import YMGap.Continuum.BF4WilsonAllNomeRGStepComposition
import YMGap.Continuum.BF4WilsonAllNomeWidthInclusionObstruction
import YMGap.Continuum.RCPolynomialFunctional

namespace YMGap.Continuum.BF4WilsonAllNomeRGTimeSmoothingObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear (completedZero)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
  (completedInner_zero_right completedTime_zero_element)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteExcitation
  (plaquetteExcitation plaquetteExcitation_norm_ne_zero)
open YMGap.Continuum.BF4WilsonAllNomeFringeTimeKernel
  (inactive_face_time_one_zero)
open YMGap.Continuum.BF4WilsonAllNomeWidthInclusionObstruction
  (boundaryFace boundaryFace_mem boundaryFace_not_fully_active)
open YMGap.Continuum.BF4WilsonAllNomeRGStepComposition
  (ApproxRgIntertwiner WilsonVacuumSqTwoStepFactor)
open YMGap.Continuum.BF4WilsonAllNomeExprMixRateContraction (WilsonVacuumSqContraction)
open YMGap.Continuum.RCPolynomialFunctional (rc_scale_coeff_add)
open YMGap.Continuum.RCSignedPairBudget (scale_congr)

variable {wF wC : Q'}
  (hwF0 : (0 : Q') < wF) (hwF1 : wF < (1 : Q'))
  (hwC0 : (0 : Q') < wC) (hwC1 : wC < (1 : Q'))

/-- Minimal actual quadratic gap transfer. A map may lose fine norms:
no coercive lower comparison, linearity or zero-preservation is required.
The upper and two-step comparisons remain action-specific analytic inputs. -/
theorem twoStepFactor_of_upper_comparison (widthF widthC : Nat) (epsilon kappa rC : Q')
    (Phi : VacuumComplement hwF0 hwF1 (width := widthF) →
      VacuumComplement hwC0 hwC1 (width := widthC))
    (hk : (0 : Q') ≤ kappa)
    (hupper : ∀ y : VacuumComplement hwF0 hwF1 (width := widthF),
      RCle (completedInner hwC0 hwC1 (Phi y).val (Phi y).val)
        (completedInner hwF0 hwF1 y.val y.val))
    (htwo : ∀ y : VacuumComplement hwF0 hwF1 (width := widthF),
      RCle (completedInner hwF0 hwF1
        (completedTime hwF0 hwF1 2 y.val) (completedTime hwF0 hwF1 2 y.val))
        (RCadd (RCscale kappa (completedInner hwC0 hwC1
          (completedTime hwC0 hwC1 1 (Phi y).val)
          (completedTime hwC0 hwC1 1 (Phi y).val)))
          (RCscale (kappa*epsilon) (completedInner hwF0 hwF1 y.val y.val))))
    (hc : WilsonVacuumSqContraction hwC0 hwC1 widthC rC) :
    WilsonVacuumSqTwoStepFactor hwF0 hwF1 widthF (kappa*(rC*rC+epsilon)) := by
  intro y
  have hcoarse := RCscale_mono hk (hc (Phi y))
  rw [RCscale_RCscale] at hcoarse
  have hleft := RCle_trans hcoarse
    (RCscale_mono (Q'.mul_nonneg _ _ hk (SumOfSquares.q_mul_self_nonneg rC)) (hupper y))
  have hsum := RCadd_le_add hleft
    (RCle_refl (RCscale (kappa*epsilon) (completedInner hwF0 hwF1 y.val y.val)))
  rw [← rc_scale_coeff_add, scale_congr
    (Q'.eqv_symm (Q'.mul_add_eqv kappa (rC*rC) epsilon))] at hsum
  exact RCle_trans (htwo y) hsum

/-- The actual positive-norm fringe defeats any coercive lower comparison
after positive-time smoothing followed by arbitrary zero-preserving R. -/
theorem no_coercive_positive_time_smoothing (n widthC k : Nat) (kappa : Q')
    (R : Completion hwF0 hwF1 (n+1) → Completion hwC0 hwC1 widthC)
    (hzero : R (completedZero hwF0 hwF1 (n+1)) = completedZero hwC0 hwC1 widthC)
    (hlower : ∀ x : VacuumComplement hwF0 hwF1 (width := n+1),
      RCle (completedInner hwF0 hwF1 x.val x.val)
        (RCscale kappa (completedInner hwC0 hwC1
          (R (completedTime hwF0 hwF1 (k+1) x.val))
          (R (completedTime hwF0 hwF1 (k+1) x.val))))) : False := by
  let x := plaquetteExcitation hwF0 hwF1 (n+1) (boundaryFace n) (boundaryFace_mem n)
  have htime : completedTime hwF0 hwF1 1 x.val = completedZero hwF0 hwF1 (n+1) :=
    inactive_face_time_one_zero hwF0 hwF1 (n+1) (boundaryFace n) (boundaryFace_mem n)
      (boundaryFace_not_fully_active n)
  have htimek : completedTime hwF0 hwF1 (k+1) x.val = completedZero hwF0 hwF1 (n+1) := by
    rw [completedTime_add, htime, completedTime_zero_element]
  have h := hlower x
  rw [htimek, hzero, completedInner_zero_right, RCscale_RCzero] at h
  exact plaquetteExcitation_norm_ne_zero hwF0 hwF1 (n+1) (boundaryFace n) (boundaryFace_mem n)
    (RCle_antisymm h (completedInner_nonnegative hwF0 hwF1 x.val))

/-- The existing approximate RG interface cannot be inhabited by a map
that factors through positive original time and sends its zero image to zero.
No linearity or exact vector-intertwining law is assumed. -/
theorem approxRg_not_positive_time_smoothing (n widthC k : Nat) (epsilon kappa : Q')
    (H : ApproxRgIntertwiner hwF0 hwF1 hwC0 hwC1 (n+1) widthC epsilon kappa)
    (R : Completion hwF0 hwF1 (n+1) → Completion hwC0 hwC1 widthC)
    (hzero : R (completedZero hwF0 hwF1 (n+1)) = completedZero hwC0 hwC1 widthC)
    (hfactor : ∀ x : VacuumComplement hwF0 hwF1 (width := n+1),
      (H.Φ x).val = R (completedTime hwF0 hwF1 (k+1) x.val)) : False := by
  apply no_coercive_positive_time_smoothing hwF0 hwF1 hwC0 hwC1 n widthC k kappa R hzero
  intro x
  have h := H.lowerBound x
  rw [hfactor x] at h
  exact h

end YMGap.Continuum.BF4WilsonAllNomeRGTimeSmoothingObstruction

#print axioms YMGap.Continuum.BF4WilsonAllNomeRGTimeSmoothingObstruction.twoStepFactor_of_upper_comparison
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGTimeSmoothingObstruction.no_coercive_positive_time_smoothing
#print axioms YMGap.Continuum.BF4WilsonAllNomeRGTimeSmoothingObstruction.approxRg_not_positive_time_smoothing
