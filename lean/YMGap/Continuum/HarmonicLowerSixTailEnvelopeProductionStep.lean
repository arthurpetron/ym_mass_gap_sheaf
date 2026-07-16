/-
# Downstream RG splice for the production lower-six envelope

The envelope certificate is useful only after it reaches the adjacent-scale
window invariant.  This file keeps that final transport explicit: the exact
Hermite remainder payment supplies the already-established quadratic drift
payment, which in turn supplies the physical scaled-window step.
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeProductionClosure
import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentUpperFluxPayment

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeProductionStep

open YMGap.Constructive
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeProductionClosure
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentUpperFluxPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftRemainderPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixTerminalPayment
open YMGap.Continuum.HarmonicMassCrossResidualSandwich
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledWindowInduction

/-- The exact Base/E8/E9 envelope closes the nonlinear quadratic payment at
every production scale. -/
theorem lowerSixQuadraticPayment_production
    {k : Nat} (hk : 8189 ≤ k) :
    -YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftScaleStep.lowerSixScaledLinearCrossPaymentResidual k ≤
      lowerSixScaledQuadraticCrossWindowSuffix k :=
  lowerSixQuadraticPayment_large_of_remainder hk
    (lowerSixFullRemainderPayment_production hk)

/-- First physical consumer of the generated envelope tables: an actual
adjacent-scale lower-six window step, with no certificate hypothesis left. -/
theorem lowerSixScaledWindowStep_production
    {k : Nat} (hk : 8189 ≤ k) :
    LowerSixScaledWindowStep k :=
  lowerSixScaledWindowStep_of_quadratic_payment
    (show 48 ≤ k by omega)
    (lowerSixQuadraticPayment_production hk)

/-- Iteration of the production step from the first scale on which the
projective envelope certificate is uniform. -/
theorem lowerSixScaledInteriorPayment_8189_le
    {k : Nat} (hk : 8189 ≤ k) :
    lowerSixScaledInteriorPayment 8189 ≤
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
          (show 48 ≤ 8189 + d by omega)
          (lowerSixScaledWindowStep_production
            (show 8189 ≤ 8189 + d by omega)))

/-- Once the finite intermediate range supplies the exact scale-8189
interior anchor, the symbolic envelope certificate propagates the physical
growing residual through every later scale. -/
theorem growingResidualLowerSix_production_of_anchor
    {k : Nat} (hk : 8189 ≤ k)
    (hanchor : (0 : Q') ≤ lowerSixInteriorPayment 8189) :
    GrowingResidualLowerSix k := by
  have hanchorScaled :
      (0 : Q') ≤ lowerSixScaledInteriorPayment 8189 := by
    unfold lowerSixScaledInteriorPayment
    exact Q'.mul_nonneg _ _ (by decide) hanchor
  have hscaled : (0 : Q') ≤ lowerSixScaledInteriorPayment k :=
    Q'.le_trans' _ _ _ hanchorScaled
      (lowerSixScaledInteriorPayment_8189_le hk)
  have hmul : Q'.ofNat (k + 2) * (0 : Q') ≤
      Q'.ofNat (k + 2) * lowerSixInteriorPayment k :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_zero_eqv (Q'.ofNat (k + 2)))) hscaled
  have hinterior : (0 : Q') ≤ lowerSixInteriorPayment k :=
    Q'.le_of_mul_le_mul_left hmul (Q'.ofNat_succ_pos (k + 1))
  exact growingResidualLowerSix_of_interior_nonnegative (by omega) hinterior

#print axioms lowerSixQuadraticPayment_production
#print axioms lowerSixScaledWindowStep_production
#print axioms lowerSixScaledInteriorPayment_8189_le
#print axioms growingResidualLowerSix_production_of_anchor

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeProductionStep
