/-
# Positive-weight reduction of the lower-six local tail inequality

The production local second-flux bound contains the old Gaussian mode weight
in every term.  This file removes that common factor exactly.  The result is
an iff with a weight-free bracket, justified by a proved-positive harmonic
weight; it is not a new analytic assumption.
-/

import YMGap.Continuum.HarmonicLowerSixTailPaymentAssembly
import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticCarrier

namespace YMGap.Continuum.HarmonicLowerSixTailLocalWeightReduction

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicLowerSixJointEndpointPayment
open YMGap.Continuum.HarmonicLowerSixSecondFluxSign
open YMGap.Continuum.HarmonicLowerSixTailPaymentAssembly
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFlux
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticCarrier
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

/-- Weight-free form of the production local second-flux inequality. -/
def LowerSixTailSecondFluxWeightFreeBound (k n : Nat) : Prop :=
  let D := Q'.ofNat (k + 2)
  let step := qpow (harmW k * harmW k) (2 * n + 1)
  lowerSixJointSecondClearingScale k *
      -(Q'.ofNat 4 * lowerSixHermiteRemainderNetBracket k n) ≤
    (step * lowerSixHermiteSecondFluxPoly D (Q'.ofNat (n + 1)) +
      -lowerSixHermiteSecondFluxPoly D (Q'.ofNat n)) +
      (Q'.ofNat 15630 * RingNormaliser.qpow D 4)

/-- Exact adjacent-mode ratio for the positive squared harmonic weight. -/
theorem lowerSixModeWeight_succ_eqv_old_mul_step (k n : Nat) :
    lowerSixModeWeight k (n + 1) ≈
      lowerSixModeWeight k n *
        qpow (harmW k * harmW k) (2 * n + 1) := by
  have hexp : (n + 1) * (n + 1) = n * n + (2 * n + 1) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
    omega
  unfold lowerSixModeWeight
  rw [hexp]
  exact HeatKernelRGStep.qpow_add
    (harmW k * harmW k) (n * n) (2 * n + 1)

private abbrev PE := RingNormaliser.PolyExpr

private def pLocalLeftL : PE :=
  .mul (.var 0) (.neg (.mul (.const 4) (.mul (.var 1) (.var 2))))

private def pLocalLeftR : PE :=
  .mul (.var 1) (.mul (.var 0) (.neg (.mul (.const 4) (.var 2))))

private theorem pLocalLeft_normal :
    RingNormaliser.normalize pLocalLeftL =
      RingNormaliser.normalize pLocalLeftR := by
  decide

private theorem localLeft_algebra (T W B : Q') :
    T * -(Q'.ofNat 4 * (W * B)) ≈
      W * (T * -(Q'.ofNat 4 * B)) := by
  simpa [pLocalLeftL, pLocalLeftR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pLocalLeftL pLocalLeftR pLocalLeft_normal
      (fun | 0 => T | 1 => W | _ => B))

private def pLocalRightL : PE :=
  .add
    (.add
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.neg (.mul (.var 0) (.var 3))))
    (.mul (.var 4) (.var 0))

private def pLocalRightR : PE :=
  .mul (.var 0)
    (.add
      (.add (.mul (.var 1) (.var 2)) (.neg (.var 3)))
      (.var 4))

private theorem pLocalRight_normal :
    RingNormaliser.normalize pLocalRightL =
      RingNormaliser.normalize pLocalRightR := by
  decide

private theorem localRight_algebra (W step Pnext P C : Q') :
    (((W * step) * Pnext + -(W * P)) + C * W) ≈
      W * ((step * Pnext + -P) + C) := by
  simpa [pLocalRightL, pLocalRightR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pLocalRightL pLocalRightR pLocalRight_normal
      (fun | 0 => W | 1 => step | 2 => Pnext | 3 => P | _ => C))

/-- Exact factorization of the production local-bound left side. -/
theorem lowerSixTailSecondFluxLocalLeft_eqv_weight_mul (k n : Nat) :
    lowerSixJointSecondClearingScale k *
        -(Q'.ofNat 4 * lowerSixDiscreteHermiteRemainder k n) ≈
      lowerSixModeWeight k n *
        (lowerSixJointSecondClearingScale k *
          -(Q'.ofNat 4 * lowerSixHermiteRemainderNetBracket k n)) := by
  have hremainder :=
    lowerSixDiscreteHermiteRemainder_eqv_weight_mul_netBracket k n
  have hreplace :
      lowerSixJointSecondClearingScale k *
          -(Q'.ofNat 4 * lowerSixDiscreteHermiteRemainder k n) ≈
        lowerSixJointSecondClearingScale k *
          -(Q'.ofNat 4 *
            (lowerSixModeWeight k n *
              lowerSixHermiteRemainderNetBracket k n)) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left _ _ _ hremainder))
  exact Q'.eqv_trans _ _ _ hreplace
    (localLeft_algebra _ _ _)

/-- Exact factorization of the production local-bound right side. -/
theorem lowerSixTailSecondFluxLocalRight_eqv_weight_mul (k n : Nat) :
    (lowerSixHermiteSecondFluxNumerator k (n + 1) +
        -lowerSixHermiteSecondFluxNumerator k n) +
        (Q'.ofNat 15630 *
          RingNormaliser.qpow (Q'.ofNat (k + 2)) 4) *
          lowerSixModeWeight k n ≈
      lowerSixModeWeight k n *
        ((qpow (harmW k * harmW k) (2 * n + 1) *
            lowerSixHermiteSecondFluxPoly (Q'.ofNat (k + 2))
              (Q'.ofNat (n + 1)) +
          -lowerSixHermiteSecondFluxPoly (Q'.ofNat (k + 2))
            (Q'.ofNat n)) +
          (Q'.ofNat 15630 *
            RingNormaliser.qpow (Q'.ofNat (k + 2)) 4)) := by
  let W := lowerSixModeWeight k n
  let step := qpow (harmW k * harmW k) (2 * n + 1)
  let Pnext := lowerSixHermiteSecondFluxPoly (Q'.ofNat (k + 2))
    (Q'.ofNat (n + 1))
  let P := lowerSixHermiteSecondFluxPoly (Q'.ofNat (k + 2))
    (Q'.ofNat n)
  let C := Q'.ofNat 15630 *
    RingNormaliser.qpow (Q'.ofNat (k + 2)) 4
  have hweight := lowerSixModeWeight_succ_eqv_old_mul_step k n
  have hfirst :
      lowerSixHermiteSecondFluxNumerator k (n + 1) ≈
        (W * step) * Pnext := by
    unfold lowerSixHermiteSecondFluxNumerator
    dsimp only [W, step, Pnext]
    exact Q'.mul_eqv_congr_right _ _ _ hweight
  have hreplace :
      (lowerSixHermiteSecondFluxNumerator k (n + 1) +
          -lowerSixHermiteSecondFluxNumerator k n) + C * W ≈
        ((W * step) * Pnext + -(W * P)) + C * W := by
    unfold lowerSixHermiteSecondFluxNumerator
    dsimp only [W, step, Pnext, P, C] at hfirst ⊢
    exact Q'.add_eqv_congr_right _ _ _
      (Q'.add_eqv_congr_right _ _ _ hfirst)
  dsimp only [W, step, Pnext, P, C] at hreplace ⊢
  exact Q'.eqv_trans _ _ _ hreplace
    (localRight_algebra _ _ _ _ _)

theorem lowerSixModeWeight_pos (k n : Nat) :
    (0 : Q') < lowerSixModeWeight k n := by
  unfold lowerSixModeWeight
  exact BondMovingScaledNorm.qpow_pos
    (Q'.mul_pos
      (HarmonicFusedSchurObstruction.harmW_pos k)
      (HarmonicFusedSchurObstruction.harmW_pos k)) (n * n)

/-- The production local inequality is equivalent, constructively and in
both directions, to its weight-free bracket. -/
theorem lowerSixTailSecondFluxLocalBound_iff_weightFree (k n : Nat) :
    LowerSixTailSecondFluxLocalBound k n ↔
      LowerSixTailSecondFluxWeightFreeBound k n := by
  let W := lowerSixModeWeight k n
  let L := lowerSixJointSecondClearingScale k *
    -(Q'.ofNat 4 * lowerSixHermiteRemainderNetBracket k n)
  let R :=
    (qpow (harmW k * harmW k) (2 * n + 1) *
        lowerSixHermiteSecondFluxPoly (Q'.ofNat (k + 2))
          (Q'.ofNat (n + 1)) +
      -lowerSixHermiteSecondFluxPoly (Q'.ofNat (k + 2))
        (Q'.ofNat n)) +
      (Q'.ofNat 15630 *
        RingNormaliser.qpow (Q'.ofNat (k + 2)) 4)
  have hleft := lowerSixTailSecondFluxLocalLeft_eqv_weight_mul k n
  have hright := lowerSixTailSecondFluxLocalRight_eqv_weight_mul k n
  have hWpos : (0 : Q') < W := by
    dsimp only [W]
    exact lowerSixModeWeight_pos k n
  constructor
  · intro hproduction
    have hscaled : W * L ≤ W * R :=
      Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
        (Q'.le_trans' _ _ _ hproduction (Q'.le_of_eqv hright))
    have hweightFree : L ≤ R :=
      Q'.le_of_mul_le_mul_left hscaled hWpos
    unfold LowerSixTailSecondFluxWeightFreeBound
    dsimp only [W, L, R] at hweightFree ⊢
    exact hweightFree
  · intro hweightFree
    unfold LowerSixTailSecondFluxWeightFreeBound at hweightFree
    dsimp only [L, R] at hweightFree
    have hscaled : W * L ≤ W * R :=
      Q'.mul_le_mul_of_nonneg_left _ _ W hweightFree
        (Q'.le_of_lt hWpos)
    unfold LowerSixTailSecondFluxLocalBound
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hscaled (Q'.ge_of_eqv hright))

#print axioms lowerSixModeWeight_succ_eqv_old_mul_step
#print axioms lowerSixTailSecondFluxLocalLeft_eqv_weight_mul
#print axioms lowerSixTailSecondFluxLocalRight_eqv_weight_mul
#print axioms lowerSixModeWeight_pos
#print axioms lowerSixTailSecondFluxLocalBound_iff_weightFree

end YMGap.Continuum.HarmonicLowerSixTailLocalWeightReduction
