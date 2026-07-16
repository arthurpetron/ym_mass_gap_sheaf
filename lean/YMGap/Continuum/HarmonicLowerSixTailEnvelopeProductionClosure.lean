/-
# Production closure of the lower-six E8/E9 envelope certificates

This module composes the sharded raw identities, the staged Taylor and Base
semantics, the two projective-chart signs, and positive-factor cancellation.
Its final theorem supplies the pointwise local premise consumed by the
existing exact Hermite tail-payment assembly.
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentity
import YMGap.Continuum.HarmonicLowerSixTailBaseSemanticPhysical
import YMGap.Continuum.HarmonicLowerSixTailEnvelopePhysicalChartDispatch
import YMGap.Continuum.HarmonicLowerSixTailEnvelopePositiveScale
import YMGap.Continuum.HarmonicLowerSixTailBaseCertificate
import YMGap.Continuum.HarmonicLowerSixTailPaymentAssembly

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeProductionClosure

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.QuadraticRawGridSemanticTransport
open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentity
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeTaylorRaw
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeTaylorSemantic
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeRawScaling
open YMGap.Continuum.HarmonicLowerSixTailEnvelopePhysicalChartDispatch
open YMGap.Continuum.HarmonicLowerSixTailEnvelopePositiveScale
open YMGap.Continuum.HarmonicLowerSixTailBaseSemanticRows
open YMGap.Continuum.HarmonicLowerSixTailBaseSemanticBridge
open YMGap.Continuum.HarmonicLowerSixTailBaseCertificate
open YMGap.Continuum.HarmonicLowerSixTailSecondFluxLocalBound
open YMGap.Continuum.HarmonicLowerSixTailPaymentAssembly
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxSummedEnvelope
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicGrowingAnchorPF2

local infix:50 " ≈ " => Q'.eqv

private theorem rnqpow_two_eqv_mul (value : Q') :
    RingNormaliser.qpow value 2 ≈ value * value := by
  change ((1 : Q') * value) * value ≈ value * value
  exact Q'.mul_eqv_congr_right _ _ value (Q'.one_mul_eqv value)

theorem tailEnvelopeE8Cleared_production_identity
    {k n : Nat} (hn : 4 ≤ n) :
    tailEnvelopeE8ClearedEval
          (Q'.ofNat (k + 2)) (Q'.ofNat n) * Q'.ofNat 4608 ≈
      RingNormaliser.qpow (Q'.ofNat 362880) 2 *
        (envelopeSemanticDenominatorValue (Q'.ofNat (k + 2)) *
          lowerSixTailEnvelope8 k n) := by
  let D := Q'.ofNat (k + 2)
  let N := Q'.ofNat n
  let den := envelopeSemanticDenominatorValue D
  let scale := RingNormaliser.qpow (Q'.ofNat 362880) 2
  let U := oneSubTaylor8 (HarmonicCutoffBoundary.harmU k) (2 * n + 1)
  let K := lowerSixTailStepCoefficient k n
  let B := lowerSixTailEnvelopeBase k n
  let T := RingNormaliser.qpow U 2 * K
  have hraw := tailEnvelopeE8ScaledRaw_production_identity D N
  have htaylor0 := evalRaw_tailEnvelopeTaylor8RawPolynomial
    (quadraticRawRho D N)
  have htaylor1 := envelopeSemanticTaylor8Scaled_production
    (k := k) (n := n) hn
  have htaylor :
      RingNormaliser.evalRaw (quadraticRawRho D N)
          tailEnvelopeTaylor8RawPolynomial ≈
        scale * (den * T) := by
    exact Q'.eqv_trans _ _ _ htaylor0 (by
      dsimp only [D, N, den, scale, U, K, T]
      simpa [quadraticRawRho, envelopeSemanticRho] using htaylor1)
  have hbase0 := evalRawRows_tailBaseSemanticTotalRows_physical k n hn
  have hbase1 :
      evalRawRows (quadraticRawRho D N) tailBaseSemanticTotalRows ≈
        (Q'.ofNat 178605 * den) * B := by
    change
      evalRawRows
          (tailBaseRawEnvironment (Q'.ofNat (k + 2)) (Q'.ofNat n))
          tailBaseSemanticTotalRows ≈
        (Q'.ofNat 178605 *
          envelopeSemanticDenominatorValue (Q'.ofNat (k + 2))) *
            lowerSixTailEnvelopeBase k n
    exact hbase0
  have hbase :
      evalRawRows (quadraticRawRho D N) tailBaseSemanticTotalRows ≈
        Q'.ofNat 178605 * (den * B) :=
    Q'.eqv_trans _ _ _ hbase1
      (Q'.mul_assoc_eqv (Q'.ofNat 178605) den B)
  have hparts :
      RingNormaliser.evalRaw (quadraticRawRho D N)
            tailEnvelopeTaylor8RawPolynomial +
          Q'.ofNat 737280 *
            evalRawRows (quadraticRawRho D N) tailBaseSemanticTotalRows ≈
        scale * (den * T) +
          Q'.ofNat 737280 *
            (Q'.ofNat 178605 * (den * B)) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ htaylor)
      (Q'.add_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat 737280) _ _ hbase))
  have hrecombine := tailEnvelopeProduction_recombine den T B
  have hshape : T + B ≈ lowerSixTailEnvelope8 k n := by
    unfold lowerSixTailEnvelope8 lowerSixTailOldPowerUpper
    dsimp only [T, U, K, B]
    exact Q'.add_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (rnqpow_two_eqv_mul U))
  have hfinal : scale * (den * (T + B)) ≈
      scale * (den * lowerSixTailEnvelope8 k n) :=
    Q'.mul_eqv_congr_left scale _ _
      (Q'.mul_eqv_congr_left den _ _ hshape)
  dsimp only [D, N, den, scale] at hraw hparts hrecombine hfinal ⊢
  exact Q'.eqv_trans _ _ _ hraw
    (Q'.eqv_trans _ _ _ hparts
      (Q'.eqv_trans _ _ _ hrecombine hfinal))

theorem tailEnvelopeE9Cleared_production_identity
    {k n : Nat} (hn : 4 ≤ n) :
    tailEnvelopeE9ClearedEval
          (Q'.ofNat (k + 2)) (Q'.ofNat n) * Q'.ofNat 512 ≈
      RingNormaliser.qpow (Q'.ofNat 362880) 2 *
        (envelopeSemanticDenominatorValue (Q'.ofNat (k + 2)) *
          lowerSixTailEnvelope9 k n) := by
  let D := Q'.ofNat (k + 2)
  let N := Q'.ofNat n
  let den := envelopeSemanticDenominatorValue D
  let scale := RingNormaliser.qpow (Q'.ofNat 362880) 2
  let L := oneSubTaylor9 (HarmonicCutoffBoundary.harmU k) (2 * n + 1)
  let K := lowerSixTailStepCoefficient k n
  let B := lowerSixTailEnvelopeBase k n
  let T := RingNormaliser.qpow L 2 * K
  have hraw := tailEnvelopeE9ScaledRaw_production_identity D N
  have htaylor0 := evalRaw_tailEnvelopeTaylor9RawPolynomial
    (quadraticRawRho D N)
  have htaylor1 := envelopeSemanticTaylor9Scaled_production
    (k := k) (n := n) hn
  have htaylor :
      RingNormaliser.evalRaw (quadraticRawRho D N)
          tailEnvelopeTaylor9RawPolynomial ≈
        scale * (den * T) := by
    exact Q'.eqv_trans _ _ _ htaylor0 (by
      dsimp only [D, N, den, scale, L, K, T]
      simpa [quadraticRawRho, envelopeSemanticRho] using htaylor1)
  have hbase0 := evalRawRows_tailBaseSemanticTotalRows_physical k n hn
  have hbase1 :
      evalRawRows (quadraticRawRho D N) tailBaseSemanticTotalRows ≈
        (Q'.ofNat 178605 * den) * B := by
    change
      evalRawRows
          (tailBaseRawEnvironment (Q'.ofNat (k + 2)) (Q'.ofNat n))
          tailBaseSemanticTotalRows ≈
        (Q'.ofNat 178605 *
          envelopeSemanticDenominatorValue (Q'.ofNat (k + 2))) *
            lowerSixTailEnvelopeBase k n
    exact hbase0
  have hbase :
      evalRawRows (quadraticRawRho D N) tailBaseSemanticTotalRows ≈
        Q'.ofNat 178605 * (den * B) :=
    Q'.eqv_trans _ _ _ hbase1
      (Q'.mul_assoc_eqv (Q'.ofNat 178605) den B)
  have hparts :
      RingNormaliser.evalRaw (quadraticRawRho D N)
            tailEnvelopeTaylor9RawPolynomial +
          Q'.ofNat 737280 *
            evalRawRows (quadraticRawRho D N) tailBaseSemanticTotalRows ≈
        scale * (den * T) +
          Q'.ofNat 737280 *
            (Q'.ofNat 178605 * (den * B)) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ htaylor)
      (Q'.add_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat 737280) _ _ hbase))
  have hrecombine := tailEnvelopeProduction_recombine den T B
  have hshape : T + B ≈ lowerSixTailEnvelope9 k n := by
    unfold lowerSixTailEnvelope9 lowerSixTailOldPowerLower
    dsimp only [T, L, K, B]
    exact Q'.add_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (rnqpow_two_eqv_mul L))
  have hfinal : scale * (den * (T + B)) ≈
      scale * (den * lowerSixTailEnvelope9 k n) :=
    Q'.mul_eqv_congr_left scale _ _
      (Q'.mul_eqv_congr_left den _ _ hshape)
  dsimp only [D, N, den, scale] at hraw hparts hrecombine hfinal ⊢
  exact Q'.eqv_trans _ _ _ hraw
    (Q'.eqv_trans _ _ _ hparts
      (Q'.eqv_trans _ _ _ hrecombine hfinal))

theorem tailEnvelopeE8E9_nonnegative
    {k n : Nat} (hk : 8189 ≤ k)
    (hleft : thetaWindowLeft k + 1 ≤ n)
    (hnright : n ≤ growingAnchor k) :
    (0 : Q') ≤ lowerSixTailEnvelope8 k n ∧
      (0 : Q') ≤ lowerSixTailEnvelope9 k n := by
  have hcenter : 9 ≤ thetaWindowCenter k :=
    thetaWindowCenter_ge_nine (by omega)
  have hn4 : 4 ≤ n := by
    unfold thetaWindowLeft at hleft
    omega
  have hcleared := tailEnvelopeE8E9ClearedEval_nonnegative
    hk hleft hnright
  have hden := envelopeSemanticDenominatorValue_pos hk
  have hE8scaled : (0 : Q') ≤
      tailEnvelopeE8ClearedEval
          (Q'.ofNat (k + 2)) (Q'.ofNat n) * Q'.ofNat 4608 :=
    Q'.mul_nonneg _ _ hcleared.1 (by decide)
  have hE9scaled : (0 : Q') ≤
      tailEnvelopeE9ClearedEval
          (Q'.ofNat (k + 2)) (Q'.ofNat n) * Q'.ofNat 512 :=
    Q'.mul_nonneg _ _ hcleared.2 (by decide)
  have hE8product : (0 : Q') ≤
      RingNormaliser.qpow (Q'.ofNat 362880) 2 *
        (envelopeSemanticDenominatorValue (Q'.ofNat (k + 2)) *
          lowerSixTailEnvelope8 k n) :=
    Q'.le_trans' _ _ _ hE8scaled
      (Q'.le_of_eqv (tailEnvelopeE8Cleared_production_identity hn4))
  have hE9product : (0 : Q') ≤
      RingNormaliser.qpow (Q'.ofNat 362880) 2 *
        (envelopeSemanticDenominatorValue (Q'.ofNat (k + 2)) *
          lowerSixTailEnvelope9 k n) :=
    Q'.le_trans' _ _ _ hE9scaled
      (Q'.le_of_eqv (tailEnvelopeE9Cleared_production_identity hn4))
  exact ⟨
    envelope_nonnegative_of_production_product hden hE8product,
    envelope_nonnegative_of_production_product hden hE9product⟩

theorem lowerSixTailEnvelopeBase_nonnegative
    {k n : Nat} (hk : 8189 ≤ k) (hDn : k + 2 ≤ n)
    (hnright : n ≤ growingAnchor k) :
    (0 : Q') ≤ lowerSixTailEnvelopeBase k n := by
  have hn4 : 4 ≤ n := by omega
  have hD : 8191 ≤ k + 2 := by omega
  have hn2 : n ≤ 2 * (k + 2) := by
    simpa [growingAnchor] using hnright
  have hcleared := tailBaseCleared_nonnegative
    (k + 2) n hD hDn hn2
  have hphysical := tailBaseCleared_physical k n hn4
  have hproduct : (0 : Q') ≤
      (Q'.ofNat 178605 *
          envelopeSemanticDenominatorValue (Q'.ofNat (k + 2))) *
        lowerSixTailEnvelopeBase k n :=
    Q'.le_trans' _ _ _ hcleared (Q'.le_of_eqv hphysical)
  have hscale : (0 : Q') <
      Q'.ofNat 178605 *
        envelopeSemanticDenominatorValue (Q'.ofNat (k + 2)) :=
    Q'.mul_pos
      (by
        simpa only [show 178604 + 1 = 178605 by decide] using
          Q'.ofNat_succ_pos 178604)
      (envelopeSemanticDenominatorValue_pos hk)
  exact Q'.nonneg_of_mul_pos hscale hproduct

/-- Hypothesis-free pointwise lower-six tail certificate on the production
suffix. -/
theorem lowerSixTailSecondFluxLocalBound_production
    {k n : Nat} (hk : 8189 ≤ k)
    (hleft : thetaWindowLeft k + 1 ≤ n)
    (hnright : n ≤ growingAnchor k) :
    LowerSixTailSecondFluxLocalBound k n := by
  have henv := tailEnvelopeE8E9_nonnegative hk hleft hnright
  exact lowerSixTailSecondFluxLocalBound_of_envelope_certificates
    hleft
    (lowerSixTailNextSlopeFloor_nonnegative hk hleft hnright)
    henv.1 henv.2
    (fun hnD =>
      lowerSixTailOldPowerLower_nonnegative_of_le_den hk hleft hnD)
    (fun hDn =>
      lowerSixTailEnvelopeBase_nonnegative hk hDn hnright)

/-- The checked local certificate discharges the complete exact Hermite
remainder payment on every production scale. -/
theorem lowerSixFullRemainderPayment_production
    {k : Nat} (hk : 8189 ≤ k) :
    -(Q'.ofNat 4 * lowerSixHermiteRemainderSum k) ≤
      lowerSixHermiteLinearHeadMassFloor k :=
  lowerSixFullRemainderPayment_of_pointwise hk
    (fun _ hleft hnright =>
      lowerSixTailSecondFluxLocalBound_production hk hleft hnright)

#print axioms tailEnvelopeE8Cleared_production_identity
#print axioms tailEnvelopeE9Cleared_production_identity
#print axioms tailEnvelopeE8E9_nonnegative
#print axioms lowerSixTailEnvelopeBase_nonnegative
#print axioms lowerSixTailSecondFluxLocalBound_production
#print axioms lowerSixFullRemainderPayment_production

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeProductionClosure
