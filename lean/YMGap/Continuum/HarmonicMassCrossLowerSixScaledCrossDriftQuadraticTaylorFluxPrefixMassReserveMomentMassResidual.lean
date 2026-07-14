/-
Final mass-reserve assembly after the cubic debt has been paid.

Only the remote upper Hermite flux remains: two of the three reserve masses
are assigned to it, while the third is consumed by the cubic debt.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentMassPayment

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentMassResidual

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFlux
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxEnvelope
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixCubicDebt
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserve
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentMassPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxSummedEnvelope

local infix:50 " ≈ " => Q'.eqv

private abbrev PE := RingNormaliser.PolyExpr

private def pResidualAssemblyL : PE :=
  let F : PE := .var 0
  let M : PE := .var 1
  let D : PE := .var 2
  .add
    (.add (.mul (.const 4) F) (.mul (.const 2) M))
    (.add M (.neg D))

private def pResidualAssemblyR : PE :=
  let F : PE := .var 0
  let M : PE := .var 1
  let D : PE := .var 2
  .add
    (.add (.mul (.const 4) F) (.mul (.const 3) M))
    (.neg D)

private theorem pResidualAssembly_normal :
    RingNormaliser.normalize pResidualAssemblyL =
      RingNormaliser.normalize pResidualAssemblyR := by decide

private theorem residual_assembly_algebra (F M D : Q') :
    (Q'.ofNat 4 * F + Q'.ofNat 2 * M) + (M + -D) ≈
      (Q'.ofNat 4 * F + Q'.ofNat 3 * M) + -D := by
  let rho : Nat → Q' := fun
    | 0 => F
    | 1 => M
    | _ => D
  simpa [pResidualAssemblyL, pResidualAssemblyR,
    RingNormaliser.eval, rho] using
    (RingNormaliser.poly_identity_of_normal_eq
      pResidualAssemblyL pResidualAssemblyR
      pResidualAssembly_normal rho)

/-- Once two masses pay the negative remote upper flux, the already-proved
one-mass cubic-debt estimate makes the full reserve residual nonnegative. -/
theorem lowerSixCubicDebtMassReserveResidual_nonnegative_large
    {k : Nat} (hk : 8189 ≤ k)
    (hupper :
      -(Q'.ofNat 4 *
          lowerSixDiscreteHermiteFluxNumerator k (growingAnchor k + 1)) ≤
        Q'.ofNat 2 * lowerSixHermiteMassSum k) :
    (0 : Q') ≤ lowerSixCubicDebtMassReserveResidual k := by
  let F := lowerSixDiscreteHermiteFluxNumerator k (growingAnchor k + 1)
  let M := lowerSixHermiteMassSum k
  let D := Q'.ofNat 4 * lowerSixQuadraticTaylorClearingScale k *
    prefixCubicDebtSum k
  have hfluxSub := Q'.sub_nonneg_of_le hupper
  have hflux : (0 : Q') ≤ Q'.ofNat 4 * F + Q'.ofNat 2 * M := by
    have hrewrite : Q'.ofNat 2 * M + -( -(Q'.ofNat 4 * F)) ≈
        Q'.ofNat 4 * F + Q'.ofNat 2 * M := by
      refine Q'.eqv_trans _
        (Q'.ofNat 2 * M + Q'.ofNat 4 * F) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv _)
      · exact Q'.add_comm_eqv _ _
    dsimp only [F, M] at hfluxSub hrewrite ⊢
    exact Q'.le_trans' _ _ _ hfluxSub (Q'.le_of_eqv hrewrite)
  have hdebt := lowerSixFourClearingScaleCubicDebt_le_HermiteMass_large hk
  change D ≤ M at hdebt
  have hdebtSub : (0 : Q') ≤ M + -D := Q'.sub_nonneg_of_le hdebt
  have hsum := Q'.zero_le_add _ _ hflux hdebtSub
  have hrewrite :
      (Q'.ofNat 4 * F + Q'.ofNat 2 * M) + (M + -D) ≈
        lowerSixCubicDebtMassReserveResidual k := by
    refine Q'.eqv_trans _
      ((Q'.ofNat 4 * F + Q'.ofNat 3 * M) + -D) _
      (residual_assembly_algebra F M D) ?_
    unfold lowerSixCubicDebtMassReserveResidual
    dsimp only [F, M, D]
    exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hrewrite)

/-- Production composition with the existing mass-reserve theorem.  The two
remaining inputs are now exactly the signed-remainder payment and the remote
upper-flux estimate. -/
theorem lowerSixQuadraticPayment_large_of_remainder_and_upperFlux
    {k : Nat} (hk : 8189 ≤ k)
    (hremainder :
      -(Q'.ofNat 4 * lowerSixHermiteRemainderSum k) ≤
        lowerSixHermiteLinearHeadMassFloor k)
    (hupper :
      -(Q'.ofNat 4 *
          lowerSixDiscreteHermiteFluxNumerator k (growingAnchor k + 1)) ≤
        Q'.ofNat 2 * lowerSixHermiteMassSum k) :
    -YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftScaleStep.lowerSixScaledLinearCrossPaymentResidual k ≤
      YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftRemainderPayment.lowerSixScaledQuadraticCrossWindowSuffix k := by
  exact lowerSixQuadraticPayment_of_cubicDebt_mass_reserve
    (show 247 ≤ k by omega) hremainder
    (lowerSixCubicDebtMassReserveResidual_nonnegative_large hk hupper)

#print axioms lowerSixCubicDebtMassReserveResidual_nonnegative_large
#print axioms lowerSixQuadraticPayment_large_of_remainder_and_upperFlux

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentMassResidual
