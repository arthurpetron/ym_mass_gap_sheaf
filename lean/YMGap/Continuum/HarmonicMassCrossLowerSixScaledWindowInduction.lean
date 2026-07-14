/-
The weakest rational cross-scale invariant suggested by the complete
lower-six payment.

The unscaled interior payment decreases with the harmonic denominator, so
plain monotonicity cannot propagate the exact finite anchor.  Multiplication
by the harmonic denominator is the first integral power that reverses this
asymptotic direction.  This file records the exact window form of that
scaled quantity and proves that one uniform scaled-window step propagates
the already-derived `k = 247` anchor through every later scale.

No new finite band is enumerated here.  The remaining analytic residual is
the single adjacent-scale inequality `LowerSixScaledWindowStep k`.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapSecond

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledWindowInduction

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapSecond
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixActual
open YMGap.Continuum.HarmonicMassCrossLowerSixTerminalPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixTwoSidedWindow
open YMGap.Continuum.HarmonicMassCrossResidualSandwich
open YMGap.Continuum.HarmonicMovingDeterminantThetaAbel
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

/-- Boundary-free lower-six payment, including the exact left endpoint. -/
def lowerSixInteriorPayment (k : Nat) : Q' :=
  lowerSixInteriorSum k +
    Q'.ofNat 4 * integerThetaTerm (harmW k) 1

/-- The natural denominator-scaled payment. -/
def lowerSixScaledInteriorPayment (k : Nat) : Q' :=
  Q'.ofNat (k + 2) * lowerSixInteriorPayment k

/-- Exact full-suffix presentation of the scaled payment. -/
theorem lowerSixScaledInteriorPayment_eqv_window {k : Nat} (hk : 48 ≤ k) :
    lowerSixScaledInteriorPayment k ≈
      Q'.ofNat (k + 2) *
        (lowerSixWindowPrefix k + lowerSixWindowRightReserve k) := by
  unfold lowerSixScaledInteriorPayment lowerSixInteriorPayment
  exact Q'.mul_eqv_congr_left _ _ _
    (lowerSixInterior_eqv_windowPrefix_add_rightReserve hk)

/-- The single adjacent-scale analytic invariant left by this route.  It
retains the entire already-proved nonnegative suffix; no fixed multiple of
the square-root center is truncated. -/
def LowerSixScaledWindowStep (k : Nat) : Prop :=
  Q'.ofNat (k + 2) *
      (lowerSixWindowPrefix k + lowerSixWindowRightReserve k) ≤
    Q'.ofNat (k + 3) *
      (lowerSixWindowPrefix (k + 1) +
        lowerSixWindowRightReserve (k + 1))

/-- A scaled-window step is exactly a monotonicity step for the scaled
interior payment. -/
theorem lowerSixScaledInteriorPayment_mono_of_windowStep
    {k : Nat} (hk : 48 ≤ k) (hstep : LowerSixScaledWindowStep k) :
    lowerSixScaledInteriorPayment k ≤
      lowerSixScaledInteriorPayment (k + 1) := by
  have h0 := lowerSixScaledInteriorPayment_eqv_window (k := k) hk
  have h1 := lowerSixScaledInteriorPayment_eqv_window
    (k := k + 1) (by omega)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv h0)
    (Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv (Q'.eqv_symm h1)))

/-- Exact nonnegative anchor supplied by the previously checked recovery
payment at the final scale of the finite bootstrap. -/
theorem lowerSixInteriorPayment_anchor_247_nonnegative :
    (0 : Q') ≤ lowerSixInteriorPayment 247 := by
  unfold lowerSixInteriorPayment
  exact lowerSixInterior_nonnegative_of_recovery_payment_actual
    (by decide)
    (lowerSixRecoveryPayment_148_247 (by decide) (by decide))

/-- The anchor in the scaled coordinates used by the induction. -/
theorem lowerSixScaledInteriorPayment_anchor_247_nonnegative :
    (0 : Q') ≤ lowerSixScaledInteriorPayment 247 := by
  unfold lowerSixScaledInteriorPayment
  exact Q'.mul_nonneg _ _ (by decide)
    lowerSixInteriorPayment_anchor_247_nonnegative

/-- Iteration of the exact adjacent-scale invariant. -/
theorem lowerSixScaledInteriorPayment_anchor_le {k : Nat}
    (hk : 247 ≤ k)
    (hstep : ∀ j, 247 ≤ j → LowerSixScaledWindowStep j) :
    lowerSixScaledInteriorPayment 247 ≤
      lowerSixScaledInteriorPayment k := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk
  subst k
  clear hk
  induction d with
  | zero =>
      exact Q'.le_refl' _
  | succ d ih =>
      exact Q'.le_trans' _ _ _ ih
        (lowerSixScaledInteriorPayment_mono_of_windowStep
          (show 48 ≤ 247 + d by omega) (hstep (247 + d) (by omega)))

/-- A uniform proof of the scaled step discharges the boundary-free payment
at every later scale.  Positivity of the harmonic denominator is used only
at the final cancellation. -/
theorem lowerSixInteriorPayment_nonnegative_of_scaledWindowSteps
    {k : Nat} (hk : 247 ≤ k)
    (hstep : ∀ j, 247 ≤ j → LowerSixScaledWindowStep j) :
    (0 : Q') ≤ lowerSixInteriorPayment k := by
  have hanchor := lowerSixScaledInteriorPayment_anchor_247_nonnegative
  have hmono := lowerSixScaledInteriorPayment_anchor_le hk hstep
  have hscaled : (0 : Q') ≤ lowerSixScaledInteriorPayment k :=
    Q'.le_trans' _ _ _ hanchor hmono
  unfold lowerSixScaledInteriorPayment at hscaled
  have hmul : Q'.ofNat (k + 2) * (0 : Q') ≤
      Q'.ofNat (k + 2) * lowerSixInteriorPayment k :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_zero_eqv (Q'.ofNat (k + 2)))) hscaled
  exact Q'.le_of_mul_le_mul_left hmul (Q'.ofNat_succ_pos (k + 1))

/-- Downstream closure of the actual six-unit growing residual from the
same sole adjacent-scale invariant. -/
theorem growingResidualLowerSix_of_scaledWindowSteps
    {k : Nat} (hk : 247 ≤ k)
    (hstep : ∀ j, 247 ≤ j → LowerSixScaledWindowStep j) :
    GrowingResidualLowerSix k := by
  exact growingResidualLowerSix_of_interior_nonnegative (by omega)
    (lowerSixInteriorPayment_nonnegative_of_scaledWindowSteps hk hstep)

/-- Exact splice with the committed finite prefix.  Consequently the whole
lower-six frontier is reduced to one genuinely uniform adjacent-scale
statement, with no further closed-scale enumeration. -/
theorem growingResidualLowerSix_all_of_scaledWindowSteps
    (hstep : ∀ j, 247 ≤ j → LowerSixScaledWindowStep j)
    {k : Nat} (hk : 10 ≤ k) :
    GrowingResidualLowerSix k := by
  by_cases hsmall : k < 248
  · exact growingResidualLowerSix_below_twoFortyEight hk hsmall
  · exact growingResidualLowerSix_of_scaledWindowSteps
      (show 247 ≤ k by omega) hstep

/-- Plain unscaled monotonicity already points the wrong way at the first
symbolic scale: the payment strictly decreases from scale 48 to scale 49.
Thus an unscaled induction is not a viable replacement for the scaled
invariant. -/
theorem lowerSix_unscaled_monotonicity_fails_k48 :
    ¬ (lowerSixInteriorPayment 48 ≤ lowerSixInteriorPayment 49) := by
  unfold lowerSixInteriorPayment lowerSixInteriorSum
    lowerSixDirichletIncrement lowerSixDirichletProfile
    thetaDirichletCell thetaRootTerm integerThetaTerm growingAnchor
    harmW harmU ReciprocalBernoulliUpper.oneSub unit finSum qpow
  decide

#print axioms lowerSixScaledInteriorPayment_eqv_window
#print axioms lowerSixScaledInteriorPayment_mono_of_windowStep
#print axioms lowerSixInteriorPayment_anchor_247_nonnegative
#print axioms lowerSixScaledInteriorPayment_anchor_247_nonnegative
#print axioms lowerSixScaledInteriorPayment_anchor_le
#print axioms lowerSixInteriorPayment_nonnegative_of_scaledWindowSteps
#print axioms growingResidualLowerSix_of_scaledWindowSteps
#print axioms growingResidualLowerSix_all_of_scaledWindowSteps
#print axioms lowerSix_unscaled_monotonicity_fails_k48

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledWindowInduction
